import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_13S14

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 9106000 in
set_option maxHeartbeats 9106000 in
theorem r1l7_22_13_15_H_I_L_I_L_I_s7 (m : N7Model)
    (hb2 : CMSig2_7_H_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg5135 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg6923 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
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
  have h2bigk := hb2.1
  have h3bigk := hb3.1
  have h5bigk := hb5.1
  have h0 := hg0
  have h5135 := hg5135
  have h6923 := hg6923
  rcases m.htr 0 1 5 (by decide) (by decide) with h7870 | h7870
  · rcases m.htr 0 2 3 (by decide) (by decide) with h7871 | h7871
    · rcases m.htr 0 2 4 (by decide) (by decide) with h7872 | h7872
      · rcases m.htr 0 2 5 (by decide) (by decide) with h7873 | h7873
        · rcases m.htr 0 3 4 (by decide) (by decide) with h7874 | h7874
          · rcases m.htr 0 3 5 (by decide) (by decide) with h7875 | h7875
            · rcases m.htr 0 4 5 (by decide) (by decide) with h7876 | h7876
              · rcases m.htr 1 2 3 (by decide) (by decide) with h7877 | h7877
                · rcases m.htr 1 2 4 (by decide) (by decide) with h7878 | h7878
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h7879 | h7879
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h7880 | h7880
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h7881 | h7881
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h7882 | h7882
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h7883 | h7883
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h7884 | h7884
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h7885 | h7885
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h7886 | h7886
                                  · rcases h2bigk with h7887c | h7887c | h7887c | h7887c | h7887c | h7887c | h7887c | h7887c | h7887c | h7887c | h7887c | h7887c | h7887c | h7887c | h7887c | h7887c | h7887c | h7887c | h7887c | h7887c | h7887c | h7887c | h7887c | h7887c | h7887c
                                    · have p7887_0 := h7887c.1
                                      have p7887_1 := h7887c.2.1
                                      have p7887_2 := h7887c.2.2.1
                                      have p7887_3 := h7887c.2.2.2
                                      linarith only [hlam, p7887_0]
                                    · have p7887_0 := h7887c.1
                                      have p7887_1 := h7887c.2.1
                                      have p7887_2 := h7887c.2.2.1
                                      have p7887_3 := h7887c.2.2.2
                                      linarith only [h0, hlam, p7887_0]
                                    · have p7887_0 := h7887c.1
                                      have p7887_1 := h7887c.2.1
                                      have p7887_2 := h7887c.2.2.1
                                      have p7887_3 := h7887c.2.2.2
                                      linarith only [h7883, h7886, hc02, hc45, hlam, hphi, ht0b, ht5b, p7887_1]
                                    · have p7887_0 := h7887c.1
                                      have p7887_1 := h7887c.2.1
                                      have p7887_2 := h7887c.2.2.1
                                      have p7887_3 := h7887c.2.2.2
                                      linarith only [h0, h7883, h7886, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p7887_1]
                                    · have p7887_0 := h7887c.1
                                      have p7887_1 := h7887c.2.1
                                      have p7887_2 := h7887c.2.2.1
                                      have p7887_3 := h7887c.2.2.2
                                      rcases p7887_3 (m.d 0 2) (by simp) with h7892 | h7892
                                      · rcases p7887_3 (m.d 1 2) (by simp) with h7893 | h7893
                                        · rcases p7887_3 (m.d 2 3) (by simp) with h7894 | h7894
                                          · linarith only [h7871, h7894, hlam]
                                          · linarith only [h7884, h7894, hlam]
                                        · linarith only [h7879, h7893, hlam]
                                      · linarith only [h7892, hlam, p7887_0]
                                    · have p7887_0 := h7887c.1
                                      have p7887_1 := h7887c.2.1
                                      have p7887_2 := h7887c.2.2.1
                                      have p7887_3 := h7887c.2.2.2
                                      linarith only [h0, h7870, h7879, h7884, h7886, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p7887_1]
                                    · have p7887_0 := h7887c.1
                                      have p7887_1 := h7887c.2.1
                                      have p7887_2 := h7887c.2.2.1
                                      have p7887_3 := h7887c.2.2.2
                                      linarith only [hlam, p7887_0]
                                    · have p7887_0 := h7887c.1
                                      have p7887_1 := h7887c.2.1
                                      have p7887_2 := h7887c.2.2.1
                                      have p7887_3 := h7887c.2.2.2
                                      linarith only [h7883, h7886, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p7887_1]
                                    · have p7887_0 := h7887c.1
                                      have p7887_1 := h7887c.2.1
                                      have p7887_2 := h7887c.2.2.1
                                      have p7887_3 := h7887c.2.2.2
                                      linarith only [h7883, h7886, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p7887_1]
                                    · have p7887_0 := h7887c.1
                                      have p7887_1 := h7887c.2.1
                                      have p7887_2 := h7887c.2.2.1
                                      have p7887_3 := h7887c.2.2.2
                                      rcases p7887_3 (m.d 0 2) (by simp) with h7903 | h7903
                                      · linarith only [h0, h7903, hlam]
                                      · linarith only [h7873, h7903, hlam]
                                    · have p7887_0 := h7887c.1
                                      have p7887_1 := h7887c.2.1
                                      have p7887_2 := h7887c.2.2.1
                                      have p7887_3 := h7887c.2.2.2
                                      linarith only [h7871, hlam, p7887_0]
                                    · have p7887_0 := h7887c.1
                                      have p7887_1 := h7887c.2.1
                                      have p7887_2 := h7887c.2.2.1
                                      have p7887_3 := h7887c.2.2.2
                                      linarith only [h7877, hlam, p7887_0]
                                    · have p7887_0 := h7887c.1
                                      have p7887_1 := h7887c.2.1
                                      have p7887_2 := h7887c.2.2.1
                                      have p7887_3 := h7887c.2.2.2
                                      linarith only [hlam, p7887_0]
                                    · have p7887_0 := h7887c.1
                                      have p7887_1 := h7887c.2.1
                                      have p7887_2 := h7887c.2.2.1
                                      have p7887_3 := h7887c.2.2.2
                                      linarith only [h7871, h7883, h7886, hc02, hc45, hlam, hphi, ht0b, ht5b, p7887_1]
                                    · have p7887_0 := h7887c.1
                                      have p7887_1 := h7887c.2.1
                                      have p7887_2 := h7887c.2.2.1
                                      have p7887_3 := h7887c.2.2.2
                                      linarith only [h0, h7871, h7884, h7886, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p7887_1]
                                    · have p7887_0 := h7887c.1
                                      have p7887_1 := h7887c.2.1
                                      have p7887_2 := h7887c.2.2.1
                                      have p7887_3 := h7887c.2.2.2
                                      linarith only [h7872, hlam, p7887_0]
                                    · have p7887_0 := h7887c.1
                                      have p7887_1 := h7887c.2.1
                                      have p7887_2 := h7887c.2.2.1
                                      have p7887_3 := h7887c.2.2.2
                                      linarith only [h7878, hlam, p7887_0]
                                    · have p7887_0 := h7887c.1
                                      have p7887_1 := h7887c.2.1
                                      have p7887_2 := h7887c.2.2.1
                                      have p7887_3 := h7887c.2.2.2
                                      linarith only [h7883, hlam, p7887_0]
                                    · have p7887_0 := h7887c.1
                                      have p7887_1 := h7887c.2.1
                                      have p7887_2 := h7887c.2.2.1
                                      have p7887_3 := h7887c.2.2.2
                                      linarith only [hlam, p7887_0]
                                    · have p7887_0 := h7887c.1
                                      have p7887_1 := h7887c.2.1
                                      have p7887_2 := h7887c.2.2.1
                                      have p7887_3 := h7887c.2.2.2
                                      linarith only [h0, h7872, h7884, h7886, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p7887_1]
                                    · have p7887_0 := h7887c.1
                                      have p7887_1 := h7887c.2.1
                                      have p7887_2 := h7887c.2.2.1
                                      have p7887_3 := h7887c.2.2.2
                                      linarith only [h7873, hlam, p7887_0]
                                    · have p7887_0 := h7887c.1
                                      have p7887_1 := h7887c.2.1
                                      have p7887_2 := h7887c.2.2.1
                                      have p7887_3 := h7887c.2.2.2
                                      linarith only [h7879, hlam, p7887_0]
                                    · have p7887_0 := h7887c.1
                                      have p7887_1 := h7887c.2.1
                                      have p7887_2 := h7887c.2.2.1
                                      have p7887_3 := h7887c.2.2.2
                                      linarith only [h7884, hlam, p7887_0]
                                    · have p7887_0 := h7887c.1
                                      have p7887_1 := h7887c.2.1
                                      have p7887_2 := h7887c.2.2.1
                                      have p7887_3 := h7887c.2.2.2
                                      linarith only [h7885, hlam, p7887_1]
                                    · have p7887_0 := h7887c.1
                                      have p7887_1 := h7887c.2.1
                                      have p7887_2 := h7887c.2.2.1
                                      have p7887_3 := h7887c.2.2.2
                                      linarith only [hlam, p7887_0]
                                  · rcases h2bigk with h7921c | h7921c | h7921c | h7921c | h7921c | h7921c | h7921c | h7921c | h7921c | h7921c | h7921c | h7921c | h7921c | h7921c | h7921c | h7921c | h7921c | h7921c | h7921c | h7921c | h7921c | h7921c | h7921c | h7921c | h7921c
                                    · have p7921_0 := h7921c.1
                                      have p7921_1 := h7921c.2.1
                                      have p7921_2 := h7921c.2.2.1
                                      have p7921_3 := h7921c.2.2.2
                                      linarith only [hlam, p7921_0]
                                    · have p7921_0 := h7921c.1
                                      have p7921_1 := h7921c.2.1
                                      have p7921_2 := h7921c.2.2.1
                                      have p7921_3 := h7921c.2.2.2
                                      linarith only [h0, hlam, p7921_0]
                                    · have p7921_0 := h7921c.1
                                      have p7921_1 := h7921c.2.1
                                      have p7921_2 := h7921c.2.2.1
                                      have p7921_3 := h7921c.2.2.2
                                      linarith only [h0, h7883, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p7921_1]
                                    · have p7921_0 := h7921c.1
                                      have p7921_1 := h7921c.2.1
                                      have p7921_2 := h7921c.2.2.1
                                      have p7921_3 := h7921c.2.2.2
                                      linarith only [h0, h7885, h7886, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p7921_1]
                                    · have p7921_0 := h7921c.1
                                      have p7921_1 := h7921c.2.1
                                      have p7921_2 := h7921c.2.2.1
                                      have p7921_3 := h7921c.2.2.2
                                      linarith only [h0, h7885, h7886, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p7921_1]
                                    · have p7921_0 := h7921c.1
                                      have p7921_1 := h7921c.2.1
                                      have p7921_2 := h7921c.2.2.1
                                      have p7921_3 := h7921c.2.2.2
                                      linarith only [h0, h7870, h7879, h7885, h7886, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p7921_1]
                                    · have p7921_0 := h7921c.1
                                      have p7921_1 := h7921c.2.1
                                      have p7921_2 := h7921c.2.2.1
                                      have p7921_3 := h7921c.2.2.2
                                      linarith only [hlam, p7921_0]
                                    · have p7921_0 := h7921c.1
                                      have p7921_1 := h7921c.2.1
                                      have p7921_2 := h7921c.2.2.1
                                      have p7921_3 := h7921c.2.2.2
                                      linarith only [h7884, h7885, h7886, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p7921_1]
                                    · have p7921_0 := h7921c.1
                                      have p7921_1 := h7921c.2.1
                                      have p7921_2 := h7921c.2.2.1
                                      have p7921_3 := h7921c.2.2.2
                                      linarith only [h7885, h7886, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p7921_1]
                                    · have p7921_0 := h7921c.1
                                      have p7921_1 := h7921c.2.1
                                      have p7921_2 := h7921c.2.2.1
                                      have p7921_3 := h7921c.2.2.2
                                      linarith only [h7885, h7886, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p7921_1]
                                    · have p7921_0 := h7921c.1
                                      have p7921_1 := h7921c.2.1
                                      have p7921_2 := h7921c.2.2.1
                                      have p7921_3 := h7921c.2.2.2
                                      linarith only [h7871, hlam, p7921_0]
                                    · have p7921_0 := h7921c.1
                                      have p7921_1 := h7921c.2.1
                                      have p7921_2 := h7921c.2.2.1
                                      have p7921_3 := h7921c.2.2.2
                                      linarith only [h7877, hlam, p7921_0]
                                    · have p7921_0 := h7921c.1
                                      have p7921_1 := h7921c.2.1
                                      have p7921_2 := h7921c.2.2.1
                                      have p7921_3 := h7921c.2.2.2
                                      linarith only [hlam, p7921_0]
                                    · have p7921_0 := h7921c.1
                                      have p7921_1 := h7921c.2.1
                                      have p7921_2 := h7921c.2.2.1
                                      have p7921_3 := h7921c.2.2.2
                                      linarith only [h7885, h7886, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p7921_1]
                                    · have p7921_0 := h7921c.1
                                      have p7921_1 := h7921c.2.1
                                      have p7921_2 := h7921c.2.2.1
                                      have p7921_3 := h7921c.2.2.2
                                      linarith only [h7871, h7885, h7886, hc03, hc34, hlam, hphi, ht0b, ht45, ht5b, p7921_1]
                                    · have p7921_0 := h7921c.1
                                      have p7921_1 := h7921c.2.1
                                      have p7921_2 := h7921c.2.2.1
                                      have p7921_3 := h7921c.2.2.2
                                      linarith only [h7872, hlam, p7921_0]
                                    · have p7921_0 := h7921c.1
                                      have p7921_1 := h7921c.2.1
                                      have p7921_2 := h7921c.2.2.1
                                      have p7921_3 := h7921c.2.2.2
                                      linarith only [h7878, hlam, p7921_0]
                                    · have p7921_0 := h7921c.1
                                      have p7921_1 := h7921c.2.1
                                      have p7921_2 := h7921c.2.2.1
                                      have p7921_3 := h7921c.2.2.2
                                      linarith only [h7883, hlam, p7921_0]
                                    · have p7921_0 := h7921c.1
                                      have p7921_1 := h7921c.2.1
                                      have p7921_2 := h7921c.2.2.1
                                      have p7921_3 := h7921c.2.2.2
                                      linarith only [hlam, p7921_0]
                                    · have p7921_0 := h7921c.1
                                      have p7921_1 := h7921c.2.1
                                      have p7921_2 := h7921c.2.2.1
                                      have p7921_3 := h7921c.2.2.2
                                      linarith only [h7885, h7886, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p7921_1]
                                    · have p7921_0 := h7921c.1
                                      have p7921_1 := h7921c.2.1
                                      have p7921_2 := h7921c.2.2.1
                                      have p7921_3 := h7921c.2.2.2
                                      linarith only [h7873, hlam, p7921_0]
                                    · have p7921_0 := h7921c.1
                                      have p7921_1 := h7921c.2.1
                                      have p7921_2 := h7921c.2.2.1
                                      have p7921_3 := h7921c.2.2.2
                                      linarith only [h7879, hlam, p7921_0]
                                    · have p7921_0 := h7921c.1
                                      have p7921_1 := h7921c.2.1
                                      have p7921_2 := h7921c.2.2.1
                                      have p7921_3 := h7921c.2.2.2
                                      linarith only [h7884, hlam, p7921_0]
                                    · have p7921_0 := h7921c.1
                                      have p7921_1 := h7921c.2.1
                                      have p7921_2 := h7921c.2.2.1
                                      have p7921_3 := h7921c.2.2.2
                                      linarith only [h7885, hlam, p7921_1]
                                    · have p7921_0 := h7921c.1
                                      have p7921_1 := h7921c.2.1
                                      have p7921_2 := h7921c.2.2.1
                                      have p7921_3 := h7921c.2.2.2
                                      linarith only [hlam, p7921_0]
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h7947 | h7947
                                  · linarith only [h7883, h7885, h7947, hlam]
                                  · rcases h2bigk with h7949c | h7949c | h7949c | h7949c | h7949c | h7949c | h7949c | h7949c | h7949c | h7949c | h7949c | h7949c | h7949c | h7949c | h7949c | h7949c | h7949c | h7949c | h7949c | h7949c | h7949c | h7949c | h7949c | h7949c | h7949c
                                    · have p7949_0 := h7949c.1
                                      have p7949_1 := h7949c.2.1
                                      have p7949_2 := h7949c.2.2.1
                                      have p7949_3 := h7949c.2.2.2
                                      linarith only [hlam, p7949_0]
                                    · have p7949_0 := h7949c.1
                                      have p7949_1 := h7949c.2.1
                                      have p7949_2 := h7949c.2.2.1
                                      have p7949_3 := h7949c.2.2.2
                                      linarith only [h0, hlam, p7949_0]
                                    · have p7949_0 := h7949c.1
                                      have p7949_1 := h7949c.2.1
                                      have p7949_2 := h7949c.2.2.1
                                      have p7949_3 := h7949c.2.2.2
                                      linarith only [h0, h7883, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p7949_1]
                                    · have p7949_0 := h7949c.1
                                      have p7949_1 := h7949c.2.1
                                      have p7949_2 := h7949c.2.2.1
                                      have p7949_3 := h7949c.2.2.2
                                      rcases p7949_3 (m.d 0 2) (by simp) with h7953 | h7953
                                      · rcases p7949_3 (m.d 1 2) (by simp) with h7954 | h7954
                                        · rcases p7949_3 (m.d 2 3) (by simp) with h7955 | h7955
                                          · linarith only [h7871, h7955, hlam]
                                          · linarith only [h7883, h7955, hlam]
                                        · linarith only [h7878, h7954, hlam]
                                      · linarith only [h7953, hlam, p7949_0]
                                    · have p7949_0 := h7949c.1
                                      have p7949_1 := h7949c.2.1
                                      have p7949_2 := h7949c.2.2.1
                                      have p7949_3 := h7949c.2.2.2
                                      rcases p7949_3 (m.d 0 2) (by simp) with h7960 | h7960
                                      · rcases p7949_3 (m.d 1 2) (by simp) with h7961 | h7961
                                        · rcases p7949_3 (m.d 2 3) (by simp) with h7962 | h7962
                                          · linarith only [h7871, h7962, hlam]
                                          · linarith only [h7884, h7962, hlam]
                                        · linarith only [h7879, h7961, hlam]
                                      · linarith only [h7960, hlam, p7949_0]
                                    · have p7949_0 := h7949c.1
                                      have p7949_1 := h7949c.2.1
                                      have p7949_2 := h7949c.2.2.1
                                      have p7949_3 := h7949c.2.2.2
                                      linarith only [h0, h7870, h7882, h7883, h7885, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p7949_1]
                                    · have p7949_0 := h7949c.1
                                      have p7949_1 := h7949c.2.1
                                      have p7949_2 := h7949c.2.2.1
                                      have p7949_3 := h7949c.2.2.2
                                      linarith only [hlam, p7949_0]
                                    · have p7949_0 := h7949c.1
                                      have p7949_1 := h7949c.2.1
                                      have p7949_2 := h7949c.2.2.1
                                      have p7949_3 := h7949c.2.2.2
                                      linarith only [h7884, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b, p7949_1]
                                    · have p7949_0 := h7949c.1
                                      have p7949_1 := h7949c.2.1
                                      have p7949_2 := h7949c.2.2.1
                                      have p7949_3 := h7949c.2.2.2
                                      rcases p7949_3 (m.d 0 2) (by simp) with h7970 | h7970
                                      · linarith only [h0, h7970, hlam]
                                      · linarith only [h7872, h7970, hlam]
                                    · have p7949_0 := h7949c.1
                                      have p7949_1 := h7949c.2.1
                                      have p7949_2 := h7949c.2.2.1
                                      have p7949_3 := h7949c.2.2.2
                                      rcases p7949_3 (m.d 0 2) (by simp) with h7973 | h7973
                                      · linarith only [h0, h7973, hlam]
                                      · linarith only [h7873, h7973, hlam]
                                    · have p7949_0 := h7949c.1
                                      have p7949_1 := h7949c.2.1
                                      have p7949_2 := h7949c.2.2.1
                                      have p7949_3 := h7949c.2.2.2
                                      linarith only [h7871, hlam, p7949_0]
                                    · have p7949_0 := h7949c.1
                                      have p7949_1 := h7949c.2.1
                                      have p7949_2 := h7949c.2.2.1
                                      have p7949_3 := h7949c.2.2.2
                                      linarith only [h7877, hlam, p7949_0]
                                    · have p7949_0 := h7949c.1
                                      have p7949_1 := h7949c.2.1
                                      have p7949_2 := h7949c.2.2.1
                                      have p7949_3 := h7949c.2.2.2
                                      linarith only [hlam, p7949_0]
                                    · have p7949_0 := h7949c.1
                                      have p7949_1 := h7949c.2.1
                                      have p7949_2 := h7949c.2.2.1
                                      have p7949_3 := h7949c.2.2.2
                                      linarith only [h7871, h7883, hc02, hc34, hlam, hphi, ht0b, ht45, ht5b, p7949_1]
                                    · have p7949_0 := h7949c.1
                                      have p7949_1 := h7949c.2.1
                                      have p7949_2 := h7949c.2.2.1
                                      have p7949_3 := h7949c.2.2.2
                                      linarith only [h0, h7871, h7883, h7885, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p7949_1]
                                    · have p7949_0 := h7949c.1
                                      have p7949_1 := h7949c.2.1
                                      have p7949_2 := h7949c.2.2.1
                                      have p7949_3 := h7949c.2.2.2
                                      linarith only [h7872, hlam, p7949_0]
                                    · have p7949_0 := h7949c.1
                                      have p7949_1 := h7949c.2.1
                                      have p7949_2 := h7949c.2.2.1
                                      have p7949_3 := h7949c.2.2.2
                                      linarith only [h7878, hlam, p7949_0]
                                    · have p7949_0 := h7949c.1
                                      have p7949_1 := h7949c.2.1
                                      have p7949_2 := h7949c.2.2.1
                                      have p7949_3 := h7949c.2.2.2
                                      linarith only [h7883, hlam, p7949_0]
                                    · have p7949_0 := h7949c.1
                                      have p7949_1 := h7949c.2.1
                                      have p7949_2 := h7949c.2.2.1
                                      have p7949_3 := h7949c.2.2.2
                                      linarith only [hlam, p7949_0]
                                    · have p7949_0 := h7949c.1
                                      have p7949_1 := h7949c.2.1
                                      have p7949_2 := h7949c.2.2.1
                                      have p7949_3 := h7949c.2.2.2
                                      linarith only [h7885, hlam, p7949_0]
                                    · have p7949_0 := h7949c.1
                                      have p7949_1 := h7949c.2.1
                                      have p7949_2 := h7949c.2.2.1
                                      have p7949_3 := h7949c.2.2.2
                                      linarith only [h7873, hlam, p7949_0]
                                    · have p7949_0 := h7949c.1
                                      have p7949_1 := h7949c.2.1
                                      have p7949_2 := h7949c.2.2.1
                                      have p7949_3 := h7949c.2.2.2
                                      linarith only [h7879, hlam, p7949_0]
                                    · have p7949_0 := h7949c.1
                                      have p7949_1 := h7949c.2.1
                                      have p7949_2 := h7949c.2.2.1
                                      have p7949_3 := h7949c.2.2.2
                                      linarith only [h7884, hlam, p7949_0]
                                    · have p7949_0 := h7949c.1
                                      have p7949_1 := h7949c.2.1
                                      have p7949_2 := h7949c.2.2.1
                                      have p7949_3 := h7949c.2.2.2
                                      linarith only [h0, h7873, h7883, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p7949_1]
                                    · have p7949_0 := h7949c.1
                                      have p7949_1 := h7949c.2.1
                                      have p7949_2 := h7949c.2.2.1
                                      have p7949_3 := h7949c.2.2.2
                                      linarith only [hlam, p7949_0]
                              · linarith only [h0, h7870, h7881, h7883, h7884, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h7992 | h7992
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h7993 | h7993
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h7994 | h7994
                                  · rcases h2bigk with h7995c | h7995c | h7995c | h7995c | h7995c | h7995c | h7995c | h7995c | h7995c | h7995c | h7995c | h7995c | h7995c | h7995c | h7995c | h7995c | h7995c | h7995c | h7995c | h7995c | h7995c | h7995c | h7995c | h7995c | h7995c
                                    · have p7995_0 := h7995c.1
                                      have p7995_1 := h7995c.2.1
                                      have p7995_2 := h7995c.2.2.1
                                      have p7995_3 := h7995c.2.2.2
                                      linarith only [hlam, p7995_0]
                                    · have p7995_0 := h7995c.1
                                      have p7995_1 := h7995c.2.1
                                      have p7995_2 := h7995c.2.2.1
                                      have p7995_3 := h7995c.2.2.2
                                      linarith only [h0, hlam, p7995_0]
                                    · have p7995_0 := h7995c.1
                                      have p7995_1 := h7995c.2.1
                                      have p7995_2 := h7995c.2.2.1
                                      have p7995_3 := h7995c.2.2.2
                                      linarith only [h0, h7992, h7994, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p7995_1]
                                    · have p7995_0 := h7995c.1
                                      have p7995_1 := h7995c.2.1
                                      have p7995_2 := h7995c.2.2.1
                                      have p7995_3 := h7995c.2.2.2
                                      linarith only [h0, h7883, h7992, h7994, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p7995_1]
                                    · have p7995_0 := h7995c.1
                                      have p7995_1 := h7995c.2.1
                                      have p7995_2 := h7995c.2.2.1
                                      have p7995_3 := h7995c.2.2.2
                                      rcases p7995_3 (m.d 0 2) (by simp) with h8000 | h8000
                                      · rcases p7995_3 (m.d 1 2) (by simp) with h8001 | h8001
                                        · rcases p7995_3 (m.d 2 3) (by simp) with h8002 | h8002
                                          · linarith only [h7871, h8002, hlam]
                                          · linarith only [h7992, h8002, hlam]
                                        · linarith only [h7879, h8001, hlam]
                                      · linarith only [h8000, hlam, p7995_0]
                                    · have p7995_0 := h7995c.1
                                      have p7995_1 := h7995c.2.1
                                      have p7995_2 := h7995c.2.2.1
                                      have p7995_3 := h7995c.2.2.2
                                      linarith only [h0, hc01, hc12, hlam, hphi, p7995_1]
                                    · have p7995_0 := h7995c.1
                                      have p7995_1 := h7995c.2.1
                                      have p7995_2 := h7995c.2.2.1
                                      have p7995_3 := h7995c.2.2.2
                                      linarith only [hlam, p7995_0]
                                    · have p7995_0 := h7995c.1
                                      have p7995_1 := h7995c.2.1
                                      have p7995_2 := h7995c.2.2.1
                                      have p7995_3 := h7995c.2.2.2
                                      linarith only [h7992, h7994, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p7995_1]
                                    · have p7995_0 := h7995c.1
                                      have p7995_1 := h7995c.2.1
                                      have p7995_2 := h7995c.2.2.1
                                      have p7995_3 := h7995c.2.2.2
                                      linarith only [h7883, h7992, h7994, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p7995_1]
                                    · have p7995_0 := h7995c.1
                                      have p7995_1 := h7995c.2.1
                                      have p7995_2 := h7995c.2.2.1
                                      have p7995_3 := h7995c.2.2.2
                                      rcases p7995_3 (m.d 0 2) (by simp) with h8011 | h8011
                                      · linarith only [h0, h8011, hlam]
                                      · linarith only [h7873, h8011, hlam]
                                    · have p7995_0 := h7995c.1
                                      have p7995_1 := h7995c.2.1
                                      have p7995_2 := h7995c.2.2.1
                                      have p7995_3 := h7995c.2.2.2
                                      linarith only [h7871, hlam, p7995_0]
                                    · have p7995_0 := h7995c.1
                                      have p7995_1 := h7995c.2.1
                                      have p7995_2 := h7995c.2.2.1
                                      have p7995_3 := h7995c.2.2.2
                                      linarith only [h7877, hlam, p7995_0]
                                    · have p7995_0 := h7995c.1
                                      have p7995_1 := h7995c.2.1
                                      have p7995_2 := h7995c.2.2.1
                                      have p7995_3 := h7995c.2.2.2
                                      linarith only [hlam, p7995_0]
                                    · have p7995_0 := h7995c.1
                                      have p7995_1 := h7995c.2.1
                                      have p7995_2 := h7995c.2.2.1
                                      have p7995_3 := h7995c.2.2.2
                                      linarith only [h7883, hlam, p7995_1]
                                    · have p7995_0 := h7995c.1
                                      have p7995_1 := h7995c.2.1
                                      have p7995_2 := h7995c.2.2.1
                                      have p7995_3 := h7995c.2.2.2
                                      linarith only [h7871, h7874, h7883, h7992, h7994, hc02, hc45, hlam, hphi, ht0b, ht5b, p7995_1]
                                    · have p7995_0 := h7995c.1
                                      have p7995_1 := h7995c.2.1
                                      have p7995_2 := h7995c.2.2.1
                                      have p7995_3 := h7995c.2.2.2
                                      linarith only [h7872, hlam, p7995_0]
                                    · have p7995_0 := h7995c.1
                                      have p7995_1 := h7995c.2.1
                                      have p7995_2 := h7995c.2.2.1
                                      have p7995_3 := h7995c.2.2.2
                                      linarith only [h7878, hlam, p7995_0]
                                    · have p7995_0 := h7995c.1
                                      have p7995_1 := h7995c.2.1
                                      have p7995_2 := h7995c.2.2.1
                                      have p7995_3 := h7995c.2.2.2
                                      linarith only [h0, h7872, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p7995_1]
                                    · have p7995_0 := h7995c.1
                                      have p7995_1 := h7995c.2.1
                                      have p7995_2 := h7995c.2.2.1
                                      have p7995_3 := h7995c.2.2.2
                                      linarith only [hlam, p7995_0]
                                    · have p7995_0 := h7995c.1
                                      have p7995_1 := h7995c.2.1
                                      have p7995_2 := h7995c.2.2.1
                                      have p7995_3 := h7995c.2.2.2
                                      linarith only [h0, h7871, h7874, h7883, h7992, h7994, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p7995_1]
                                    · have p7995_0 := h7995c.1
                                      have p7995_1 := h7995c.2.1
                                      have p7995_2 := h7995c.2.2.1
                                      have p7995_3 := h7995c.2.2.2
                                      linarith only [h7873, hlam, p7995_0]
                                    · have p7995_0 := h7995c.1
                                      have p7995_1 := h7995c.2.1
                                      have p7995_2 := h7995c.2.2.1
                                      have p7995_3 := h7995c.2.2.2
                                      linarith only [h7879, hlam, p7995_0]
                                    · have p7995_0 := h7995c.1
                                      have p7995_1 := h7995c.2.1
                                      have p7995_2 := h7995c.2.2.1
                                      have p7995_3 := h7995c.2.2.2
                                      linarith only [h7992, hlam, p7995_0]
                                    · have p7995_0 := h7995c.1
                                      have p7995_1 := h7995c.2.1
                                      have p7995_2 := h7995c.2.2.1
                                      have p7995_3 := h7995c.2.2.2
                                      linarith only [h7993, hlam, p7995_1]
                                    · have p7995_0 := h7995c.1
                                      have p7995_1 := h7995c.2.1
                                      have p7995_2 := h7995c.2.2.1
                                      have p7995_3 := h7995c.2.2.2
                                      linarith only [hlam, p7995_0]
                                  · linarith only [h6923, h7870, h7877, h7880, h7882, h7883, h7992, h7994, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b]
                                · linarith only [h6923, h7870, h7877, h7880, h7882, h7883, h7992, h7993, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b]
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h8031 | h8031
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h8032 | h8032
                                  · rcases h2bigk with h8033c | h8033c | h8033c | h8033c | h8033c | h8033c | h8033c | h8033c | h8033c | h8033c | h8033c | h8033c | h8033c | h8033c | h8033c | h8033c | h8033c | h8033c | h8033c | h8033c | h8033c | h8033c | h8033c | h8033c | h8033c
                                    · have p8033_0 := h8033c.1
                                      have p8033_1 := h8033c.2.1
                                      have p8033_2 := h8033c.2.2.1
                                      have p8033_3 := h8033c.2.2.2
                                      linarith only [hlam, p8033_0]
                                    · have p8033_0 := h8033c.1
                                      have p8033_1 := h8033c.2.1
                                      have p8033_2 := h8033c.2.2.1
                                      have p8033_3 := h8033c.2.2.2
                                      linarith only [h0, hlam, p8033_0]
                                    · have p8033_0 := h8033c.1
                                      have p8033_1 := h8033c.2.1
                                      have p8033_2 := h8033c.2.2.1
                                      have p8033_3 := h8033c.2.2.2
                                      rcases p8033_3 (m.d 0 2) (by simp) with h8036 | h8036
                                      · rcases p8033_3 (m.d 1 2) (by simp) with h8037 | h8037
                                        · rcases p8033_3 (m.d 2 3) (by simp) with h8038 | h8038
                                          · linarith only [h8038, hlam, p8033_0]
                                          · rcases p8033_3 (m.d 2 4) (by simp) with h8040 | h8040
                                            · linarith only [h7872, h8040, hlam]
                                            · linarith only [h7883, h8040, hlam]
                                        · linarith only [h7877, h8037, hlam]
                                      · linarith only [h8036, hlam, p8033_0]
                                    · have p8033_0 := h8033c.1
                                      have p8033_1 := h8033c.2.1
                                      have p8033_2 := h8033c.2.2.1
                                      have p8033_3 := h8033c.2.2.2
                                      linarith only [h8031, hc02, hc45, hlam, hphi, ht0b, ht5b, p8033_1]
                                    · have p8033_0 := h8033c.1
                                      have p8033_1 := h8033c.2.1
                                      have p8033_2 := h8033c.2.2.1
                                      have p8033_3 := h8033c.2.2.2
                                      rcases p8033_3 (m.d 0 2) (by simp) with h8046 | h8046
                                      · rcases p8033_3 (m.d 1 2) (by simp) with h8047 | h8047
                                        · rcases p8033_3 (m.d 2 3) (by simp) with h8048 | h8048
                                          · linarith only [h7871, h8048, hlam]
                                          · rcases p8033_3 (m.d 2 4) (by simp) with h8050 | h8050
                                            · linarith only [h7872, h8050, hlam]
                                            · linarith only [h8031, h8050, hlam]
                                        · linarith only [h7879, h8047, hlam]
                                      · linarith only [h8046, hlam, p8033_0]
                                    · have p8033_0 := h8033c.1
                                      have p8033_1 := h8033c.2.1
                                      have p8033_2 := h8033c.2.2.1
                                      have p8033_3 := h8033c.2.2.2
                                      linarith only [h0, hc01, hc12, hlam, hphi, p8033_1]
                                    · have p8033_0 := h8033c.1
                                      have p8033_1 := h8033c.2.1
                                      have p8033_2 := h8033c.2.2.1
                                      have p8033_3 := h8033c.2.2.2
                                      linarith only [hlam, p8033_0]
                                    · have p8033_0 := h8033c.1
                                      have p8033_1 := h8033c.2.1
                                      have p8033_2 := h8033c.2.2.1
                                      have p8033_3 := h8033c.2.2.2
                                      rcases p8033_3 (m.d 0 2) (by simp) with h8057 | h8057
                                      · linarith only [h0, h8057, hlam]
                                      · linarith only [h7871, h8057, hlam]
                                    · have p8033_0 := h8033c.1
                                      have p8033_1 := h8033c.2.1
                                      have p8033_2 := h8033c.2.2.1
                                      have p8033_3 := h8033c.2.2.2
                                      linarith only [h8031, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p8033_1]
                                    · have p8033_0 := h8033c.1
                                      have p8033_1 := h8033c.2.1
                                      have p8033_2 := h8033c.2.2.1
                                      have p8033_3 := h8033c.2.2.2
                                      rcases p8033_3 (m.d 0 2) (by simp) with h8061 | h8061
                                      · linarith only [h0, h8061, hlam]
                                      · linarith only [h7873, h8061, hlam]
                                    · have p8033_0 := h8033c.1
                                      have p8033_1 := h8033c.2.1
                                      have p8033_2 := h8033c.2.2.1
                                      have p8033_3 := h8033c.2.2.2
                                      linarith only [h7871, hlam, p8033_0]
                                    · have p8033_0 := h8033c.1
                                      have p8033_1 := h8033c.2.1
                                      have p8033_2 := h8033c.2.2.1
                                      have p8033_3 := h8033c.2.2.2
                                      linarith only [h7877, hlam, p8033_0]
                                    · have p8033_0 := h8033c.1
                                      have p8033_1 := h8033c.2.1
                                      have p8033_2 := h8033c.2.2.1
                                      have p8033_3 := h8033c.2.2.2
                                      linarith only [hlam, p8033_0]
                                    · have p8033_0 := h8033c.1
                                      have p8033_1 := h8033c.2.1
                                      have p8033_2 := h8033c.2.2.1
                                      have p8033_3 := h8033c.2.2.2
                                      linarith only [h7883, hlam, p8033_1]
                                    · have p8033_0 := h8033c.1
                                      have p8033_1 := h8033c.2.1
                                      have p8033_2 := h8033c.2.2.1
                                      have p8033_3 := h8033c.2.2.2
                                      linarith only [h7992, hlam, p8033_1]
                                    · have p8033_0 := h8033c.1
                                      have p8033_1 := h8033c.2.1
                                      have p8033_2 := h8033c.2.2.1
                                      have p8033_3 := h8033c.2.2.2
                                      linarith only [h7872, hlam, p8033_0]
                                    · have p8033_0 := h8033c.1
                                      have p8033_1 := h8033c.2.1
                                      have p8033_2 := h8033c.2.2.1
                                      have p8033_3 := h8033c.2.2.2
                                      linarith only [h7878, hlam, p8033_0]
                                    · have p8033_0 := h8033c.1
                                      have p8033_1 := h8033c.2.1
                                      have p8033_2 := h8033c.2.2.1
                                      have p8033_3 := h8033c.2.2.2
                                      linarith only [h7872, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p8033_1]
                                    · have p8033_0 := h8033c.1
                                      have p8033_1 := h8033c.2.1
                                      have p8033_2 := h8033c.2.2.1
                                      have p8033_3 := h8033c.2.2.2
                                      linarith only [hlam, p8033_0]
                                    · have p8033_0 := h8033c.1
                                      have p8033_1 := h8033c.2.1
                                      have p8033_2 := h8033c.2.2.1
                                      have p8033_3 := h8033c.2.2.2
                                      linarith only [h5135, h7874, h7877, h7883, h7992, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p8033_1]
                                    · have p8033_0 := h8033c.1
                                      have p8033_1 := h8033c.2.1
                                      have p8033_2 := h8033c.2.2.1
                                      have p8033_3 := h8033c.2.2.2
                                      linarith only [h7873, hlam, p8033_0]
                                    · have p8033_0 := h8033c.1
                                      have p8033_1 := h8033c.2.1
                                      have p8033_2 := h8033c.2.2.1
                                      have p8033_3 := h8033c.2.2.2
                                      linarith only [h7879, hlam, p8033_0]
                                    · have p8033_0 := h8033c.1
                                      have p8033_1 := h8033c.2.1
                                      have p8033_2 := h8033c.2.2.1
                                      have p8033_3 := h8033c.2.2.2
                                      linarith only [h0, h7873, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p8033_1]
                                    · have p8033_0 := h8033c.1
                                      have p8033_1 := h8033c.2.1
                                      have p8033_2 := h8033c.2.2.1
                                      have p8033_3 := h8033c.2.2.2
                                      linarith only [h8031, hlam, p8033_1]
                                    · have p8033_0 := h8033c.1
                                      have p8033_1 := h8033c.2.1
                                      have p8033_2 := h8033c.2.2.1
                                      have p8033_3 := h8033c.2.2.2
                                      linarith only [hlam, p8033_0]
                                  · linarith only [h6923, h7870, h7877, h7880, h7882, h7883, h8032, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h8080 | h8080
                                  · rcases h2bigk with h8081c | h8081c | h8081c | h8081c | h8081c | h8081c | h8081c | h8081c | h8081c | h8081c | h8081c | h8081c | h8081c | h8081c | h8081c | h8081c | h8081c | h8081c | h8081c | h8081c | h8081c | h8081c | h8081c | h8081c | h8081c
                                    · have p8081_0 := h8081c.1
                                      have p8081_1 := h8081c.2.1
                                      have p8081_2 := h8081c.2.2.1
                                      have p8081_3 := h8081c.2.2.2
                                      linarith only [hlam, p8081_0]
                                    · have p8081_0 := h8081c.1
                                      have p8081_1 := h8081c.2.1
                                      have p8081_2 := h8081c.2.2.1
                                      have p8081_3 := h8081c.2.2.2
                                      linarith only [h0, hlam, p8081_0]
                                    · have p8081_0 := h8081c.1
                                      have p8081_1 := h8081c.2.1
                                      have p8081_2 := h8081c.2.2.1
                                      have p8081_3 := h8081c.2.2.2
                                      rcases p8081_3 (m.d 0 2) (by simp) with h8084 | h8084
                                      · rcases p8081_3 (m.d 1 2) (by simp) with h8085 | h8085
                                        · rcases p8081_3 (m.d 2 3) (by simp) with h8086 | h8086
                                          · linarith only [h8086, hlam, p8081_0]
                                          · rcases p8081_3 (m.d 2 4) (by simp) with h8088 | h8088
                                            · linarith only [h7872, h8088, hlam]
                                            · linarith only [h7883, h8088, hlam]
                                        · linarith only [h7877, h8085, hlam]
                                      · linarith only [h8084, hlam, p8081_0]
                                    · have p8081_0 := h8081c.1
                                      have p8081_1 := h8081c.2.1
                                      have p8081_2 := h8081c.2.2.1
                                      have p8081_3 := h8081c.2.2.2
                                      rcases p8081_3 (m.d 0 2) (by simp) with h8093 | h8093
                                      · rcases p8081_3 (m.d 1 2) (by simp) with h8094 | h8094
                                        · rcases p8081_3 (m.d 2 3) (by simp) with h8095 | h8095
                                          · linarith only [h7871, h8095, hlam]
                                          · rcases p8081_3 (m.d 2 4) (by simp) with h8097 | h8097
                                            · linarith only [h8097, hlam, p8081_0]
                                            · rcases p8081_3 (m.d 2 5) (by simp) with h8099 | h8099
                                              · linarith only [h7873, h8099, hlam]
                                              · linarith only [h8031, h8099, hlam]
                                        · linarith only [h7878, h8094, hlam]
                                      · linarith only [h8093, hlam, p8081_0]
                                    · have p8081_0 := h8081c.1
                                      have p8081_1 := h8081c.2.1
                                      have p8081_2 := h8081c.2.2.1
                                      have p8081_3 := h8081c.2.2.2
                                      rcases p8081_3 (m.d 0 2) (by simp) with h8104 | h8104
                                      · rcases p8081_3 (m.d 1 2) (by simp) with h8105 | h8105
                                        · rcases p8081_3 (m.d 2 3) (by simp) with h8106 | h8106
                                          · linarith only [h7871, h8106, hlam]
                                          · rcases p8081_3 (m.d 2 4) (by simp) with h8108 | h8108
                                            · linarith only [h7872, h8108, hlam]
                                            · rcases p8081_3 (m.d 2 5) (by simp) with h8110 | h8110
                                              · linarith only [h8110, hlam, p8081_0]
                                              · rcases h3bigk with h8112c | h8112c | h8112c | h8112c | h8112c | h8112c | h8112c | h8112c | h8112c | h8112c | h8112c | h8112c | h8112c | h8112c | h8112c | h8112c | h8112c | h8112c | h8112c | h8112c | h8112c | h8112c | h8112c | h8112c | h8112c
                                                · have p8112_0 := h8112c.1
                                                  have p8112_1 := h8112c.2.1
                                                  have p8112_2 := h8112c.2.2.1
                                                  have p8112_3 := h8112c.2.2.2
                                                  linarith only [hlam, p8112_0]
                                                · have p8112_0 := h8112c.1
                                                  have p8112_1 := h8112c.2.1
                                                  have p8112_2 := h8112c.2.2.1
                                                  have p8112_3 := h8112c.2.2.2
                                                  linarith only [h5135, hlam, p8112_1]
                                                · have p8112_0 := h8112c.1
                                                  have p8112_1 := h8112c.2.1
                                                  have p8112_2 := h8112c.2.2.1
                                                  have p8112_3 := h8112c.2.2.2
                                                  linarith only [h7874, h7883, h8031, h8080, hlam, p8112_2]
                                                · have p8112_0 := h8112c.1
                                                  have p8112_1 := h8112c.2.1
                                                  have p8112_2 := h8112c.2.2.1
                                                  have p8112_3 := h8112c.2.2.2
                                                  linarith only [h7883, h8031, h8080, hc03, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p8112_1]
                                                · have p8112_0 := h8112c.1
                                                  have p8112_1 := h8112c.2.1
                                                  have p8112_2 := h8112c.2.2.1
                                                  have p8112_3 := h8112c.2.2.2
                                                  rcases p8112_3 (m.d 0 3) (by simp) with h8117 | h8117
                                                  · rcases p8112_3 (m.d 1 3) (by simp) with h8118 | h8118
                                                    · rcases p8112_3 (m.d 2 3) (by simp) with h8119 | h8119
                                                      · linarith only [h7871, h8119, hlam]
                                                      · rcases p8112_3 (m.d 3 4) (by simp) with h8121 | h8121
                                                        · linarith only [h7874, h8121, hlam]
                                                        · linarith only [h8080, h8121, hlam]
                                                    · linarith only [h7881, h8118, hlam]
                                                  · linarith only [h8117, hlam, p8112_0]
                                                · have p8112_0 := h8112c.1
                                                  have p8112_1 := h8112c.2.1
                                                  have p8112_2 := h8112c.2.2.1
                                                  have p8112_3 := h8112c.2.2.2
                                                  linarith only [h7874, h7877, h7883, h8031, h8080, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p8112_1]
                                                · have p8112_0 := h8112c.1
                                                  have p8112_1 := h8112c.2.1
                                                  have p8112_2 := h8112c.2.2.1
                                                  have p8112_3 := h8112c.2.2.2
                                                  linarith only [hlam, p8112_0]
                                                · have p8112_0 := h8112c.1
                                                  have p8112_1 := h8112c.2.1
                                                  have p8112_2 := h8112c.2.2.1
                                                  have p8112_3 := h8112c.2.2.2
                                                  linarith only [h5135, h7874, h7883, h8031, h8080, hlam, p8112_2]
                                                · have p8112_0 := h8112c.1
                                                  have p8112_1 := h8112c.2.1
                                                  have p8112_2 := h8112c.2.2.1
                                                  have p8112_3 := h8112c.2.2.2
                                                  linarith only [h7877, h7883, h8031, h8080, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p8112_1]
                                                · have p8112_0 := h8112c.1
                                                  have p8112_1 := h8112c.2.1
                                                  have p8112_2 := h8112c.2.2.1
                                                  have p8112_3 := h8112c.2.2.2
                                                  rcases p8112_3 (m.d 0 3) (by simp) with h8130 | h8130
                                                  · linarith only [h5135, h8130, hlam]
                                                  · linarith only [h7875, h8130, hlam]
                                                · have p8112_0 := h8112c.1
                                                  have p8112_1 := h8112c.2.1
                                                  have p8112_2 := h8112c.2.2.1
                                                  have p8112_3 := h8112c.2.2.2
                                                  linarith only [h7871, hlam, p8112_1]
                                                · have p8112_0 := h8112c.1
                                                  have p8112_1 := h8112c.2.1
                                                  have p8112_2 := h8112c.2.2.1
                                                  have p8112_3 := h8112c.2.2.2
                                                  linarith only [h7877, hlam, p8112_1]
                                                · have p8112_0 := h8112c.1
                                                  have p8112_1 := h8112c.2.1
                                                  have p8112_2 := h8112c.2.2.1
                                                  have p8112_3 := h8112c.2.2.2
                                                  linarith only [hlam, p8112_0]
                                                · have p8112_0 := h8112c.1
                                                  have p8112_1 := h8112c.2.1
                                                  have p8112_2 := h8112c.2.2.1
                                                  have p8112_3 := h8112c.2.2.2
                                                  linarith only [h7883, hlam, p8112_0]
                                                · have p8112_0 := h8112c.1
                                                  have p8112_1 := h8112c.2.1
                                                  have p8112_2 := h8112c.2.2.1
                                                  have p8112_3 := h8112c.2.2.2
                                                  linarith only [h7992, hlam, p8112_0]
                                                · have p8112_0 := h8112c.1
                                                  have p8112_1 := h8112c.2.1
                                                  have p8112_2 := h8112c.2.2.1
                                                  have p8112_3 := h8112c.2.2.2
                                                  linarith only [h7874, hlam, p8112_0]
                                                · have p8112_0 := h8112c.1
                                                  have p8112_1 := h8112c.2.1
                                                  have p8112_2 := h8112c.2.2.1
                                                  have p8112_3 := h8112c.2.2.2
                                                  linarith only [h7880, hlam, p8112_0]
                                                · have p8112_0 := h8112c.1
                                                  have p8112_1 := h8112c.2.1
                                                  have p8112_2 := h8112c.2.2.1
                                                  have p8112_3 := h8112c.2.2.2
                                                  rcases p8112_3 (m.d 0 3) (by simp) with h8140 | h8140
                                                  · rcases p8112_3 (m.d 1 3) (by simp) with h8141 | h8141
                                                    · rcases p8112_3 (m.d 2 3) (by simp) with h8142 | h8142
                                                      · linarith only [h8142, hlam, p8112_0]
                                                      · rcases p8112_3 (m.d 3 4) (by simp) with h8144 | h8144
                                                        · rcases p8112_3 (m.d 3 5) (by simp) with h8145 | h8145
                                                          · linarith only [h8080, h8145, hlam]
                                                          · linarith only [h7992, h8145, hlam]
                                                        · linarith only [h8144, hlam, p8112_0]
                                                    · linarith only [h7877, h8141, hlam]
                                                  · linarith only [h7871, h8140, hlam]
                                                · have p8112_0 := h8112c.1
                                                  have p8112_1 := h8112c.2.1
                                                  have p8112_2 := h8112c.2.2.1
                                                  have p8112_3 := h8112c.2.2.2
                                                  linarith only [hlam, p8112_0]
                                                · have p8112_0 := h8112c.1
                                                  have p8112_1 := h8112c.2.1
                                                  have p8112_2 := h8112c.2.2.1
                                                  have p8112_3 := h8112c.2.2.2
                                                  linarith only [h7883, h8031, h8080, hc23, hc34, hlam, hphi, p8112_1]
                                                · have p8112_0 := h8112c.1
                                                  have p8112_1 := h8112c.2.1
                                                  have p8112_2 := h8112c.2.2.1
                                                  have p8112_3 := h8112c.2.2.2
                                                  linarith only [h7875, hlam, p8112_0]
                                                · have p8112_0 := h8112c.1
                                                  have p8112_1 := h8112c.2.1
                                                  have p8112_2 := h8112c.2.2.1
                                                  have p8112_3 := h8112c.2.2.2
                                                  linarith only [h7881, hlam, p8112_0]
                                                · have p8112_0 := h8112c.1
                                                  have p8112_1 := h8112c.2.1
                                                  have p8112_2 := h8112c.2.2.1
                                                  have p8112_3 := h8112c.2.2.2
                                                  linarith only [h6923, h7870, h7877, h7880, h7881, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p8112_1]
                                                · have p8112_0 := h8112c.1
                                                  have p8112_1 := h8112c.2.1
                                                  have p8112_2 := h8112c.2.2.1
                                                  have p8112_3 := h8112c.2.2.2
                                                  linarith only [h8080, hlam, p8112_1]
                                                · have p8112_0 := h8112c.1
                                                  have p8112_1 := h8112c.2.1
                                                  have p8112_2 := h8112c.2.2.1
                                                  have p8112_3 := h8112c.2.2.2
                                                  linarith only [hlam, p8112_0]
                                        · linarith only [h7879, h8105, hlam]
                                      · linarith only [h8104, hlam, p8081_0]
                                    · have p8081_0 := h8081c.1
                                      have p8081_1 := h8081c.2.1
                                      have p8081_2 := h8081c.2.2.1
                                      have p8081_3 := h8081c.2.2.2
                                      linarith only [h0, hc01, hc12, hlam, hphi, p8081_1]
                                    · have p8081_0 := h8081c.1
                                      have p8081_1 := h8081c.2.1
                                      have p8081_2 := h8081c.2.2.1
                                      have p8081_3 := h8081c.2.2.2
                                      linarith only [hlam, p8081_0]
                                    · have p8081_0 := h8081c.1
                                      have p8081_1 := h8081c.2.1
                                      have p8081_2 := h8081c.2.2.1
                                      have p8081_3 := h8081c.2.2.2
                                      rcases p8081_3 (m.d 0 2) (by simp) with h8162 | h8162
                                      · linarith only [h0, h8162, hlam]
                                      · linarith only [h7871, h8162, hlam]
                                    · have p8081_0 := h8081c.1
                                      have p8081_1 := h8081c.2.1
                                      have p8081_2 := h8081c.2.2.1
                                      have p8081_3 := h8081c.2.2.2
                                      rcases p8081_3 (m.d 0 2) (by simp) with h8165 | h8165
                                      · linarith only [h0, h8165, hlam]
                                      · linarith only [h7872, h8165, hlam]
                                    · have p8081_0 := h8081c.1
                                      have p8081_1 := h8081c.2.1
                                      have p8081_2 := h8081c.2.2.1
                                      have p8081_3 := h8081c.2.2.2
                                      rcases p8081_3 (m.d 0 2) (by simp) with h8168 | h8168
                                      · linarith only [h0, h8168, hlam]
                                      · linarith only [h7873, h8168, hlam]
                                    · have p8081_0 := h8081c.1
                                      have p8081_1 := h8081c.2.1
                                      have p8081_2 := h8081c.2.2.1
                                      have p8081_3 := h8081c.2.2.2
                                      linarith only [h7871, hlam, p8081_0]
                                    · have p8081_0 := h8081c.1
                                      have p8081_1 := h8081c.2.1
                                      have p8081_2 := h8081c.2.2.1
                                      have p8081_3 := h8081c.2.2.2
                                      linarith only [h7877, hlam, p8081_0]
                                    · have p8081_0 := h8081c.1
                                      have p8081_1 := h8081c.2.1
                                      have p8081_2 := h8081c.2.2.1
                                      have p8081_3 := h8081c.2.2.2
                                      linarith only [hlam, p8081_0]
                                    · have p8081_0 := h8081c.1
                                      have p8081_1 := h8081c.2.1
                                      have p8081_2 := h8081c.2.2.1
                                      have p8081_3 := h8081c.2.2.2
                                      linarith only [h7883, hlam, p8081_1]
                                    · have p8081_0 := h8081c.1
                                      have p8081_1 := h8081c.2.1
                                      have p8081_2 := h8081c.2.2.1
                                      have p8081_3 := h8081c.2.2.2
                                      linarith only [h7992, hlam, p8081_1]
                                    · have p8081_0 := h8081c.1
                                      have p8081_1 := h8081c.2.1
                                      have p8081_2 := h8081c.2.2.1
                                      have p8081_3 := h8081c.2.2.2
                                      linarith only [h7872, hlam, p8081_0]
                                    · have p8081_0 := h8081c.1
                                      have p8081_1 := h8081c.2.1
                                      have p8081_2 := h8081c.2.2.1
                                      have p8081_3 := h8081c.2.2.2
                                      linarith only [h7878, hlam, p8081_0]
                                    · have p8081_0 := h8081c.1
                                      have p8081_1 := h8081c.2.1
                                      have p8081_2 := h8081c.2.2.1
                                      have p8081_3 := h8081c.2.2.2
                                      linarith only [h7870, h7881, h8031, h8080, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p8081_1]
                                    · have p8081_0 := h8081c.1
                                      have p8081_1 := h8081c.2.1
                                      have p8081_2 := h8081c.2.2.1
                                      have p8081_3 := h8081c.2.2.2
                                      linarith only [hlam, p8081_0]
                                    · have p8081_0 := h8081c.1
                                      have p8081_1 := h8081c.2.1
                                      have p8081_2 := h8081c.2.2.1
                                      have p8081_3 := h8081c.2.2.2
                                      linarith only [h8031, hlam, p8081_0]
                                    · have p8081_0 := h8081c.1
                                      have p8081_1 := h8081c.2.1
                                      have p8081_2 := h8081c.2.2.1
                                      have p8081_3 := h8081c.2.2.2
                                      linarith only [h7873, hlam, p8081_0]
                                    · have p8081_0 := h8081c.1
                                      have p8081_1 := h8081c.2.1
                                      have p8081_2 := h8081c.2.2.1
                                      have p8081_3 := h8081c.2.2.2
                                      linarith only [h7879, hlam, p8081_0]
                                    · have p8081_0 := h8081c.1
                                      have p8081_1 := h8081c.2.1
                                      have p8081_2 := h8081c.2.2.1
                                      have p8081_3 := h8081c.2.2.2
                                      linarith only [h7873, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p8081_1]
                                    · have p8081_0 := h8081c.1
                                      have p8081_1 := h8081c.2.1
                                      have p8081_2 := h8081c.2.2.1
                                      have p8081_3 := h8081c.2.2.2
                                      linarith only [h6923, h7870, h7877, h7880, h7881, h8031, h8080, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p8081_1]
                                    · have p8081_0 := h8081c.1
                                      have p8081_1 := h8081c.2.1
                                      have p8081_2 := h8081c.2.2.1
                                      have p8081_3 := h8081c.2.2.2
                                      linarith only [hlam, p8081_0]
                                  · linarith only [h6923, h7870, h7877, h7880, h7882, h7883, h8080, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                          · linarith only [h6923, h7870, h7876, h7882, hlam]
                        · linarith only [h5135, h7875, h7881, hlam]
                      · linarith only [h5135, h7874, h7880, hlam]
                    · linarith only [h0, h7873, h7879, hlam]
                  · linarith only [h0, h7872, h7878, hlam]
                · linarith only [h0, h7871, h7877, hlam]
              · linarith only [h6923, h7870, h7876, hlam]
            · linarith only [h6923, h7870, h7874, h7875, hlam]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h8195 | h8195
            · rcases m.htr 0 4 5 (by decide) (by decide) with h8196 | h8196
              · rcases m.htr 1 2 3 (by decide) (by decide) with h8197 | h8197
                · rcases m.htr 1 2 4 (by decide) (by decide) with h8198 | h8198
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h8199 | h8199
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h8200 | h8200
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h8201 | h8201
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h8202 | h8202
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h8203 | h8203
                            · linarith only [h5135, h7870, h7871, h7874, h8199, h8203, hc02, hc25, hlam, hphi, ht0b, ht5b]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h8205 | h8205
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h8206 | h8206
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h8207 | h8207
                                  · rcases h2bigk with h8208c | h8208c | h8208c | h8208c | h8208c | h8208c | h8208c | h8208c | h8208c | h8208c | h8208c | h8208c | h8208c | h8208c | h8208c | h8208c | h8208c | h8208c | h8208c | h8208c | h8208c | h8208c | h8208c | h8208c | h8208c
                                    · have p8208_0 := h8208c.1
                                      have p8208_1 := h8208c.2.1
                                      have p8208_2 := h8208c.2.2.1
                                      have p8208_3 := h8208c.2.2.2
                                      linarith only [hlam, p8208_0]
                                    · have p8208_0 := h8208c.1
                                      have p8208_1 := h8208c.2.1
                                      have p8208_2 := h8208c.2.2.1
                                      have p8208_3 := h8208c.2.2.2
                                      linarith only [h0, hlam, p8208_0]
                                    · have p8208_0 := h8208c.1
                                      have p8208_1 := h8208c.2.1
                                      have p8208_2 := h8208c.2.2.1
                                      have p8208_3 := h8208c.2.2.2
                                      linarith only [h0, h8205, h8207, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p8208_1]
                                    · have p8208_0 := h8208c.1
                                      have p8208_1 := h8208c.2.1
                                      have p8208_2 := h8208c.2.2.1
                                      have p8208_3 := h8208c.2.2.2
                                      linarith only [h0, h8203, h8205, h8207, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p8208_1]
                                    · have p8208_0 := h8208c.1
                                      have p8208_1 := h8208c.2.1
                                      have p8208_2 := h8208c.2.2.1
                                      have p8208_3 := h8208c.2.2.2
                                      rcases p8208_3 (m.d 0 2) (by simp) with h8213 | h8213
                                      · rcases p8208_3 (m.d 1 2) (by simp) with h8214 | h8214
                                        · rcases p8208_3 (m.d 2 3) (by simp) with h8215 | h8215
                                          · linarith only [h7871, h8215, hlam]
                                          · linarith only [h8205, h8215, hlam]
                                        · linarith only [h8199, h8214, hlam]
                                      · linarith only [h8213, hlam, p8208_0]
                                    · have p8208_0 := h8208c.1
                                      have p8208_1 := h8208c.2.1
                                      have p8208_2 := h8208c.2.2.1
                                      have p8208_3 := h8208c.2.2.2
                                      linarith only [h0, h7870, h8199, h8205, h8207, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p8208_1]
                                    · have p8208_0 := h8208c.1
                                      have p8208_1 := h8208c.2.1
                                      have p8208_2 := h8208c.2.2.1
                                      have p8208_3 := h8208c.2.2.2
                                      linarith only [hlam, p8208_0]
                                    · have p8208_0 := h8208c.1
                                      have p8208_1 := h8208c.2.1
                                      have p8208_2 := h8208c.2.2.1
                                      have p8208_3 := h8208c.2.2.2
                                      linarith only [h8205, h8207, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p8208_1]
                                    · have p8208_0 := h8208c.1
                                      have p8208_1 := h8208c.2.1
                                      have p8208_2 := h8208c.2.2.1
                                      have p8208_3 := h8208c.2.2.2
                                      linarith only [h8203, h8205, h8207, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p8208_1]
                                    · have p8208_0 := h8208c.1
                                      have p8208_1 := h8208c.2.1
                                      have p8208_2 := h8208c.2.2.1
                                      have p8208_3 := h8208c.2.2.2
                                      rcases p8208_3 (m.d 0 2) (by simp) with h8224 | h8224
                                      · linarith only [h0, h8224, hlam]
                                      · linarith only [h7873, h8224, hlam]
                                    · have p8208_0 := h8208c.1
                                      have p8208_1 := h8208c.2.1
                                      have p8208_2 := h8208c.2.2.1
                                      have p8208_3 := h8208c.2.2.2
                                      linarith only [h7871, hlam, p8208_0]
                                    · have p8208_0 := h8208c.1
                                      have p8208_1 := h8208c.2.1
                                      have p8208_2 := h8208c.2.2.1
                                      have p8208_3 := h8208c.2.2.2
                                      linarith only [h8197, hlam, p8208_0]
                                    · have p8208_0 := h8208c.1
                                      have p8208_1 := h8208c.2.1
                                      have p8208_2 := h8208c.2.2.1
                                      have p8208_3 := h8208c.2.2.2
                                      linarith only [hlam, p8208_0]
                                    · have p8208_0 := h8208c.1
                                      have p8208_1 := h8208c.2.1
                                      have p8208_2 := h8208c.2.2.1
                                      have p8208_3 := h8208c.2.2.2
                                      linarith only [h8203, hlam, p8208_1]
                                    · have p8208_0 := h8208c.1
                                      have p8208_1 := h8208c.2.1
                                      have p8208_2 := h8208c.2.2.1
                                      have p8208_3 := h8208c.2.2.2
                                      linarith only [h7872, h8203, h8205, h8207, hc02, hc45, hlam, hphi, ht0b, ht5b, p8208_1]
                                    · have p8208_0 := h8208c.1
                                      have p8208_1 := h8208c.2.1
                                      have p8208_2 := h8208c.2.2.1
                                      have p8208_3 := h8208c.2.2.2
                                      linarith only [h7872, hlam, p8208_0]
                                    · have p8208_0 := h8208c.1
                                      have p8208_1 := h8208c.2.1
                                      have p8208_2 := h8208c.2.2.1
                                      have p8208_3 := h8208c.2.2.2
                                      linarith only [h8198, hlam, p8208_0]
                                    · have p8208_0 := h8208c.1
                                      have p8208_1 := h8208c.2.1
                                      have p8208_2 := h8208c.2.2.1
                                      have p8208_3 := h8208c.2.2.2
                                      linarith only [h7872, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p8208_1]
                                    · have p8208_0 := h8208c.1
                                      have p8208_1 := h8208c.2.1
                                      have p8208_2 := h8208c.2.2.1
                                      have p8208_3 := h8208c.2.2.2
                                      linarith only [hlam, p8208_0]
                                    · have p8208_0 := h8208c.1
                                      have p8208_1 := h8208c.2.1
                                      have p8208_2 := h8208c.2.2.1
                                      have p8208_3 := h8208c.2.2.2
                                      linarith only [h7872, h7874, h8197, h8200, h8205, h8207, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p8208_1]
                                    · have p8208_0 := h8208c.1
                                      have p8208_1 := h8208c.2.1
                                      have p8208_2 := h8208c.2.2.1
                                      have p8208_3 := h8208c.2.2.2
                                      linarith only [h7873, hlam, p8208_0]
                                    · have p8208_0 := h8208c.1
                                      have p8208_1 := h8208c.2.1
                                      have p8208_2 := h8208c.2.2.1
                                      have p8208_3 := h8208c.2.2.2
                                      linarith only [h8199, hlam, p8208_0]
                                    · have p8208_0 := h8208c.1
                                      have p8208_1 := h8208c.2.1
                                      have p8208_2 := h8208c.2.2.1
                                      have p8208_3 := h8208c.2.2.2
                                      linarith only [h8205, hlam, p8208_0]
                                    · have p8208_0 := h8208c.1
                                      have p8208_1 := h8208c.2.1
                                      have p8208_2 := h8208c.2.2.1
                                      have p8208_3 := h8208c.2.2.2
                                      linarith only [h8206, hlam, p8208_1]
                                    · have p8208_0 := h8208c.1
                                      have p8208_1 := h8208c.2.1
                                      have p8208_2 := h8208c.2.2.1
                                      have p8208_3 := h8208c.2.2.2
                                      linarith only [hlam, p8208_0]
                                  · linarith only [h5135, h7870, h7874, h8196, h8199, h8205, h8207, hc04, hc35, hlam, hphi, ht0b, ht5b]
                                · linarith only [h5135, h7870, h7874, h8197, h8200, h8202, h8206, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b]
                              · linarith only [h7874, h8195, h8197, h8200, h8205, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                          · linarith only [h6923, h8196, h8202, hlam]
                        · linarith only [h7874, h8195, h8201, hc13, hc34, hlam, hphi]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h8247 | h8247
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h8248 | h8248
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h8249 | h8249
                            · linarith only [h5135, h8200, h8249, hc01, hc23, hlam, hphi, ht12]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h8251 | h8251
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h8252 | h8252
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h8253 | h8253
                                  · rcases h2bigk with h8254c | h8254c | h8254c | h8254c | h8254c | h8254c | h8254c | h8254c | h8254c | h8254c | h8254c | h8254c | h8254c | h8254c | h8254c | h8254c | h8254c | h8254c | h8254c | h8254c | h8254c | h8254c | h8254c | h8254c | h8254c
                                    · have p8254_0 := h8254c.1
                                      have p8254_1 := h8254c.2.1
                                      have p8254_2 := h8254c.2.2.1
                                      have p8254_3 := h8254c.2.2.2
                                      linarith only [hlam, p8254_0]
                                    · have p8254_0 := h8254c.1
                                      have p8254_1 := h8254c.2.1
                                      have p8254_2 := h8254c.2.2.1
                                      have p8254_3 := h8254c.2.2.2
                                      linarith only [h0, hlam, p8254_0]
                                    · have p8254_0 := h8254c.1
                                      have p8254_1 := h8254c.2.1
                                      have p8254_2 := h8254c.2.2.1
                                      have p8254_3 := h8254c.2.2.2
                                      linarith only [h0, h8251, h8253, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p8254_1]
                                    · have p8254_0 := h8254c.1
                                      have p8254_1 := h8254c.2.1
                                      have p8254_2 := h8254c.2.2.1
                                      have p8254_3 := h8254c.2.2.2
                                      linarith only [h0, h8249, h8251, h8253, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p8254_1]
                                    · have p8254_0 := h8254c.1
                                      have p8254_1 := h8254c.2.1
                                      have p8254_2 := h8254c.2.2.1
                                      have p8254_3 := h8254c.2.2.2
                                      rcases p8254_3 (m.d 0 2) (by simp) with h8259 | h8259
                                      · rcases p8254_3 (m.d 1 2) (by simp) with h8260 | h8260
                                        · rcases p8254_3 (m.d 2 3) (by simp) with h8261 | h8261
                                          · linarith only [h7871, h8261, hlam]
                                          · linarith only [h8251, h8261, hlam]
                                        · linarith only [h8199, h8260, hlam]
                                      · linarith only [h8259, hlam, p8254_0]
                                    · have p8254_0 := h8254c.1
                                      have p8254_1 := h8254c.2.1
                                      have p8254_2 := h8254c.2.2.1
                                      have p8254_3 := h8254c.2.2.2
                                      linarith only [h0, h7870, h8199, h8251, h8253, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p8254_1]
                                    · have p8254_0 := h8254c.1
                                      have p8254_1 := h8254c.2.1
                                      have p8254_2 := h8254c.2.2.1
                                      have p8254_3 := h8254c.2.2.2
                                      linarith only [hlam, p8254_0]
                                    · have p8254_0 := h8254c.1
                                      have p8254_1 := h8254c.2.1
                                      have p8254_2 := h8254c.2.2.1
                                      have p8254_3 := h8254c.2.2.2
                                      linarith only [h8251, h8253, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p8254_1]
                                    · have p8254_0 := h8254c.1
                                      have p8254_1 := h8254c.2.1
                                      have p8254_2 := h8254c.2.2.1
                                      have p8254_3 := h8254c.2.2.2
                                      linarith only [h8249, h8251, h8253, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p8254_1]
                                    · have p8254_0 := h8254c.1
                                      have p8254_1 := h8254c.2.1
                                      have p8254_2 := h8254c.2.2.1
                                      have p8254_3 := h8254c.2.2.2
                                      rcases p8254_3 (m.d 0 2) (by simp) with h8270 | h8270
                                      · linarith only [h0, h8270, hlam]
                                      · linarith only [h7873, h8270, hlam]
                                    · have p8254_0 := h8254c.1
                                      have p8254_1 := h8254c.2.1
                                      have p8254_2 := h8254c.2.2.1
                                      have p8254_3 := h8254c.2.2.2
                                      linarith only [h7871, hlam, p8254_0]
                                    · have p8254_0 := h8254c.1
                                      have p8254_1 := h8254c.2.1
                                      have p8254_2 := h8254c.2.2.1
                                      have p8254_3 := h8254c.2.2.2
                                      linarith only [h8197, hlam, p8254_0]
                                    · have p8254_0 := h8254c.1
                                      have p8254_1 := h8254c.2.1
                                      have p8254_2 := h8254c.2.2.1
                                      have p8254_3 := h8254c.2.2.2
                                      linarith only [hlam, p8254_0]
                                    · have p8254_0 := h8254c.1
                                      have p8254_1 := h8254c.2.1
                                      have p8254_2 := h8254c.2.2.1
                                      have p8254_3 := h8254c.2.2.2
                                      linarith only [h8249, hlam, p8254_1]
                                    · have p8254_0 := h8254c.1
                                      have p8254_1 := h8254c.2.1
                                      have p8254_2 := h8254c.2.2.1
                                      have p8254_3 := h8254c.2.2.2
                                      linarith only [h7871, h8251, h8253, hc02, hc45, hlam, hphi, ht0b, ht5b, p8254_1]
                                    · have p8254_0 := h8254c.1
                                      have p8254_1 := h8254c.2.1
                                      have p8254_2 := h8254c.2.2.1
                                      have p8254_3 := h8254c.2.2.2
                                      linarith only [h7872, hlam, p8254_0]
                                    · have p8254_0 := h8254c.1
                                      have p8254_1 := h8254c.2.1
                                      have p8254_2 := h8254c.2.2.1
                                      have p8254_3 := h8254c.2.2.2
                                      linarith only [h8198, hlam, p8254_0]
                                    · have p8254_0 := h8254c.1
                                      have p8254_1 := h8254c.2.1
                                      have p8254_2 := h8254c.2.2.1
                                      have p8254_3 := h8254c.2.2.2
                                      linarith only [h0, h5135, h7870, h7872, h8199, h8200, h8251, h8253, hc12, hc23, hc34, hc45, hlam, hphi, ht01, ht0b, ht5b, p8254_1]
                                    · have p8254_0 := h8254c.1
                                      have p8254_1 := h8254c.2.1
                                      have p8254_2 := h8254c.2.2.1
                                      have p8254_3 := h8254c.2.2.2
                                      linarith only [hlam, p8254_0]
                                    · have p8254_0 := h8254c.1
                                      have p8254_1 := h8254c.2.1
                                      have p8254_2 := h8254c.2.2.1
                                      have p8254_3 := h8254c.2.2.2
                                      linarith only [h0, h7872, h8251, h8253, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p8254_1]
                                    · have p8254_0 := h8254c.1
                                      have p8254_1 := h8254c.2.1
                                      have p8254_2 := h8254c.2.2.1
                                      have p8254_3 := h8254c.2.2.2
                                      linarith only [h7873, hlam, p8254_0]
                                    · have p8254_0 := h8254c.1
                                      have p8254_1 := h8254c.2.1
                                      have p8254_2 := h8254c.2.2.1
                                      have p8254_3 := h8254c.2.2.2
                                      linarith only [h8199, hlam, p8254_0]
                                    · have p8254_0 := h8254c.1
                                      have p8254_1 := h8254c.2.1
                                      have p8254_2 := h8254c.2.2.1
                                      have p8254_3 := h8254c.2.2.2
                                      linarith only [h8251, hlam, p8254_0]
                                    · have p8254_0 := h8254c.1
                                      have p8254_1 := h8254c.2.1
                                      have p8254_2 := h8254c.2.2.1
                                      have p8254_3 := h8254c.2.2.2
                                      linarith only [h8252, hlam, p8254_1]
                                    · have p8254_0 := h8254c.1
                                      have p8254_1 := h8254c.2.1
                                      have p8254_2 := h8254c.2.2.1
                                      have p8254_3 := h8254c.2.2.2
                                      linarith only [hlam, p8254_0]
                                  · linarith only [h5135, h7870, h8199, h8200, h8251, h8253, hc35, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b]
                                · linarith only [h5135, h7870, h8200, h8248, h8252, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                              · linarith only [h5135, h7870, h8200, h8247, h8251, hc23, hc34, hlam, hphi]
                          · linarith only [h6923, h8196, h8248, hlam]
                        · linarith only [h5135, h7870, h8195, h8247, hc03, hc15, hlam, hphi, ht0b, ht5b]
                    · linarith only [h0, h7873, h8199, hlam]
                  · linarith only [h0, h7872, h8198, hlam]
                · linarith only [h0, h7871, h8197, hlam]
              · linarith only [h6923, h7870, h8196, hlam]
            · linarith only [h5135, h7870, h8195, hlam]
        · linarith only [h0, h7870, h7873, hlam]
      · rcases m.htr 0 2 5 (by decide) (by decide) with h8299 | h8299
        · rcases m.htr 0 3 4 (by decide) (by decide) with h8300 | h8300
          · linarith only [h7871, h7872, h8300, hlam]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h8302 | h8302
            · rcases m.htr 0 4 5 (by decide) (by decide) with h8303 | h8303
              · rcases m.htr 1 2 3 (by decide) (by decide) with h8304 | h8304
                · rcases m.htr 1 2 4 (by decide) (by decide) with h8305 | h8305
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h8306 | h8306
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h8307 | h8307
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h8308 | h8308
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h8309 | h8309
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h8310 | h8310
                            · linarith only [h5135, h7871, h7872, h8300, h8305, h8310, hc01, hc12, hlam, hphi]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h8312 | h8312
                              · linarith only [h7871, h7872, h8304, h8307, h8310, h8312, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b]
                              · linarith only [h7871, h7872, h8302, h8304, h8307, h8310, h8312, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                          · linarith only [h6923, h7870, h8303, h8306, h8309, hc04, hc25, hlam, hphi, ht0b, ht5b]
                        · linarith only [h7871, h7872, h8300, h8307, h8308, hc23, hc35, hlam, hphi]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h8317 | h8317
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h8318 | h8318
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h8319 | h8319
                            · linarith only [h7871, h7872, h8305, h8307, h8319, hc13, hc14, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h8321 | h8321
                              · linarith only [h7871, h7872, h8305, h8321, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b]
                              · linarith only [h7871, h7872, h8302, h8305, h8321, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                          · linarith only [h6923, h7870, h8303, h8306, h8318, hc04, hc25, hlam, hphi, ht0b, ht5b]
                        · linarith only [h5135, h7870, h7871, h7872, h8302, h8305, h8306, h8317, hc12, hc25, hlam, hphi, ht01, ht0b, ht5b]
                    · linarith only [h7872, h8305, h8306, hc02, hc25, hlam, hphi]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h8327 | h8327
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h8328 | h8328
                      · linarith only [h5135, h8300, h8304, h8305, h8328, hc01, hc24, hlam, hphi, ht12]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h8330 | h8330
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h8331 | h8331
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h8332 | h8332
                            · linarith only [h0, h7871, h8305, h8328, h8332, hc13, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h8334 | h8334
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h8335 | h8335
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h8336 | h8336
                                  · rcases h2bigk with h8337c | h8337c | h8337c | h8337c | h8337c | h8337c | h8337c | h8337c | h8337c | h8337c | h8337c | h8337c | h8337c | h8337c | h8337c | h8337c | h8337c | h8337c | h8337c | h8337c | h8337c | h8337c | h8337c | h8337c | h8337c
                                    · have p8337_0 := h8337c.1
                                      have p8337_1 := h8337c.2.1
                                      have p8337_2 := h8337c.2.2.1
                                      have p8337_3 := h8337c.2.2.2
                                      linarith only [hlam, p8337_0]
                                    · have p8337_0 := h8337c.1
                                      have p8337_1 := h8337c.2.1
                                      have p8337_2 := h8337c.2.2.1
                                      have p8337_3 := h8337c.2.2.2
                                      linarith only [h0, hlam, p8337_0]
                                    · have p8337_0 := h8337c.1
                                      have p8337_1 := h8337c.2.1
                                      have p8337_2 := h8337c.2.2.1
                                      have p8337_3 := h8337c.2.2.2
                                      linarith only [h0, h8305, h8332, hc23, hc34, hlam, hphi, p8337_1]
                                    · have p8337_0 := h8337c.1
                                      have p8337_1 := h8337c.2.1
                                      have p8337_2 := h8337c.2.2.1
                                      have p8337_3 := h8337c.2.2.2
                                      linarith only [h7872, hlam, p8337_0]
                                    · have p8337_0 := h8337c.1
                                      have p8337_1 := h8337c.2.1
                                      have p8337_2 := h8337c.2.2.1
                                      have p8337_3 := h8337c.2.2.2
                                      linarith only [h0, h8305, h8332, h8334, h8336, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p8337_1]
                                    · have p8337_0 := h8337c.1
                                      have p8337_1 := h8337c.2.1
                                      have p8337_2 := h8337c.2.2.1
                                      have p8337_3 := h8337c.2.2.2
                                      linarith only [h8305, h8332, hc02, hc34, hlam, hphi, ht23, p8337_1]
                                    · have p8337_0 := h8337c.1
                                      have p8337_1 := h8337c.2.1
                                      have p8337_2 := h8337c.2.2.1
                                      have p8337_3 := h8337c.2.2.2
                                      linarith only [hlam, p8337_0]
                                    · have p8337_0 := h8337c.1
                                      have p8337_1 := h8337c.2.1
                                      have p8337_2 := h8337c.2.2.1
                                      have p8337_3 := h8337c.2.2.2
                                      linarith only [h8305, h8332, hc23, hc34, hlam, hphi, p8337_1]
                                    · have p8337_0 := h8337c.1
                                      have p8337_1 := h8337c.2.1
                                      have p8337_2 := h8337c.2.2.1
                                      have p8337_3 := h8337c.2.2.2
                                      linarith only [h8305, hlam, p8337_0]
                                    · have p8337_0 := h8337c.1
                                      have p8337_1 := h8337c.2.1
                                      have p8337_2 := h8337c.2.2.1
                                      have p8337_3 := h8337c.2.2.2
                                      linarith only [h8305, h8332, h8334, h8336, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p8337_1]
                                    · have p8337_0 := h8337c.1
                                      have p8337_1 := h8337c.2.1
                                      have p8337_2 := h8337c.2.2.1
                                      have p8337_3 := h8337c.2.2.2
                                      linarith only [h7871, hlam, p8337_0]
                                    · have p8337_0 := h8337c.1
                                      have p8337_1 := h8337c.2.1
                                      have p8337_2 := h8337c.2.2.1
                                      have p8337_3 := h8337c.2.2.2
                                      linarith only [h8304, hlam, p8337_0]
                                    · have p8337_0 := h8337c.1
                                      have p8337_1 := h8337c.2.1
                                      have p8337_2 := h8337c.2.2.1
                                      have p8337_3 := h8337c.2.2.2
                                      linarith only [hlam, p8337_0]
                                    · have p8337_0 := h8337c.1
                                      have p8337_1 := h8337c.2.1
                                      have p8337_2 := h8337c.2.2.1
                                      have p8337_3 := h8337c.2.2.2
                                      linarith only [h8332, hlam, p8337_1]
                                    · have p8337_0 := h8337c.1
                                      have p8337_1 := h8337c.2.1
                                      have p8337_2 := h8337c.2.2.1
                                      have p8337_3 := h8337c.2.2.2
                                      linarith only [h7871, h8334, h8336, hc02, hc45, hlam, hphi, ht0b, ht5b, p8337_1]
                                    · have p8337_0 := h8337c.1
                                      have p8337_1 := h8337c.2.1
                                      have p8337_2 := h8337c.2.2.1
                                      have p8337_3 := h8337c.2.2.2
                                      linarith only [h8332, hc02, hc34, hlam, hphi, ht23, p8337_1]
                                    · have p8337_0 := h8337c.1
                                      have p8337_1 := h8337c.2.1
                                      have p8337_2 := h8337c.2.2.1
                                      have p8337_3 := h8337c.2.2.2
                                      linarith only [h8332, hc12, hc34, hlam, hphi, ht23, p8337_1]
                                    · have p8337_0 := h8337c.1
                                      have p8337_1 := h8337c.2.1
                                      have p8337_2 := h8337c.2.2.1
                                      have p8337_3 := h8337c.2.2.2
                                      linarith only [h8332, hc23, hc34, hlam, hphi, p8337_1]
                                    · have p8337_0 := h8337c.1
                                      have p8337_1 := h8337c.2.1
                                      have p8337_2 := h8337c.2.2.1
                                      have p8337_3 := h8337c.2.2.2
                                      linarith only [hlam, p8337_0]
                                    · have p8337_0 := h8337c.1
                                      have p8337_1 := h8337c.2.1
                                      have p8337_2 := h8337c.2.2.1
                                      have p8337_3 := h8337c.2.2.2
                                      rcases p8337_3 (m.d 0 2) (by simp) with h8357 | h8357
                                      · linarith only [h7872, h8357, hlam]
                                      · linarith only [h8299, h8357, hlam]
                                    · have p8337_0 := h8337c.1
                                      have p8337_1 := h8337c.2.1
                                      have p8337_2 := h8337c.2.2.1
                                      have p8337_3 := h8337c.2.2.2
                                      linarith only [h8299, hlam, p8337_0]
                                    · have p8337_0 := h8337c.1
                                      have p8337_1 := h8337c.2.1
                                      have p8337_2 := h8337c.2.2.1
                                      have p8337_3 := h8337c.2.2.2
                                      linarith only [h8327, hlam, p8337_0]
                                    · have p8337_0 := h8337c.1
                                      have p8337_1 := h8337c.2.1
                                      have p8337_2 := h8337c.2.2.1
                                      have p8337_3 := h8337c.2.2.2
                                      linarith only [h8334, hlam, p8337_0]
                                    · have p8337_0 := h8337c.1
                                      have p8337_1 := h8337c.2.1
                                      have p8337_2 := h8337c.2.2.1
                                      have p8337_3 := h8337c.2.2.2
                                      linarith only [h8335, hlam, p8337_1]
                                    · have p8337_0 := h8337c.1
                                      have p8337_1 := h8337c.2.1
                                      have p8337_2 := h8337c.2.2.1
                                      have p8337_3 := h8337c.2.2.2
                                      linarith only [hlam, p8337_0]
                                  · linarith only [h7871, h7872, h8332, h8334, h8336, hc35, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b]
                                · linarith only [h5135, h7870, h8304, h8305, h8331, h8335, hlam]
                              · linarith only [h0, h7871, h8302, h8305, h8332, h8334, hc23, hc34, hlam, hphi]
                          · linarith only [h6923, h8303, h8331, hlam]
                        · linarith only [h0, h5135, h7871, h8302, h8330, hc01, hc12, hlam, hphi]
                    · linarith only [h0, h8299, h8327, hlam]
                · linarith only [h0, h7871, h8304, hlam]
              · linarith only [h0, h7870, h7872, h8303, hlam]
            · linarith only [h5135, h7870, h8302, hlam]
        · linarith only [h5135, h7870, h7871, h8299, hlam]
    · rcases m.htr 0 2 4 (by decide) (by decide) with h8375 | h8375
      · rcases m.htr 0 2 5 (by decide) (by decide) with h8376 | h8376
        · rcases m.htr 0 3 4 (by decide) (by decide) with h8377 | h8377
          · rcases m.htr 0 3 5 (by decide) (by decide) with h8378 | h8378
            · rcases m.htr 0 4 5 (by decide) (by decide) with h8379 | h8379
              · rcases m.htr 1 2 3 (by decide) (by decide) with h8380 | h8380
                · rcases m.htr 1 2 4 (by decide) (by decide) with h8381 | h8381
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h8382 | h8382
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h8383 | h8383
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h8384 | h8384
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h8385 | h8385
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h8386 | h8386
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h8387 | h8387
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h8388 | h8388
                                · linarith only [h7871, h8375, h8380, h8388, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b]
                                · linarith only [h7871, h8375, h8379, h8380, h8388, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b]
                              · linarith only [h6923, h7870, h7871, h8375, h8378, h8387, hc03, hc15, hlam, hphi, ht0b, ht5b]
                            · linarith only [h6923, h7870, h7871, h8375, h8377, h8386, hc03, hc15, hlam, hphi, ht0b, ht5b]
                          · linarith only [h6923, h7871, h8375, h8379, h8380, h8385, hc01, hc12, hlam, hphi]
                        · linarith only [h5135, h8378, h8384, hlam]
                      · linarith only [h7871, h8375, h8377, h8380, h8383, hlam]
                    · linarith only [h7871, h8380, h8382, hc02, hc25, hlam, hphi]
                  · linarith only [h6923, h7870, h7871, h8375, h8380, h8381, hc15, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h8398 | h8398
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h8399 | h8399
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h8400 | h8400
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h8401 | h8401
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h8402 | h8402
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h8403 | h8403
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h8404 | h8404
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h8405 | h8405
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h8406 | h8406
                                  · rcases h2bigk with h8407c | h8407c | h8407c | h8407c | h8407c | h8407c | h8407c | h8407c | h8407c | h8407c | h8407c | h8407c | h8407c | h8407c | h8407c | h8407c | h8407c | h8407c | h8407c | h8407c | h8407c | h8407c | h8407c | h8407c | h8407c
                                    · have p8407_0 := h8407c.1
                                      have p8407_1 := h8407c.2.1
                                      have p8407_2 := h8407c.2.2.1
                                      have p8407_3 := h8407c.2.2.2
                                      linarith only [hlam, p8407_0]
                                    · have p8407_0 := h8407c.1
                                      have p8407_1 := h8407c.2.1
                                      have p8407_2 := h8407c.2.2.1
                                      have p8407_3 := h8407c.2.2.2
                                      linarith only [h0, hlam, p8407_0]
                                    · have p8407_0 := h8407c.1
                                      have p8407_1 := h8407c.2.1
                                      have p8407_2 := h8407c.2.2.1
                                      have p8407_3 := h8407c.2.2.2
                                      linarith only [h7871, hlam, p8407_0]
                                    · have p8407_0 := h8407c.1
                                      have p8407_1 := h8407c.2.1
                                      have p8407_2 := h8407c.2.2.1
                                      have p8407_3 := h8407c.2.2.2
                                      linarith only [h8403, h8406, hc02, hc45, hlam, hphi, ht0b, ht5b, p8407_1]
                                    · have p8407_0 := h8407c.1
                                      have p8407_1 := h8407c.2.1
                                      have p8407_2 := h8407c.2.2.1
                                      have p8407_3 := h8407c.2.2.2
                                      linarith only [h0, h8380, h8404, h8406, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p8407_1]
                                    · have p8407_0 := h8407c.1
                                      have p8407_1 := h8407c.2.1
                                      have p8407_2 := h8407c.2.2.1
                                      have p8407_3 := h8407c.2.2.2
                                      linarith only [h8380, hc02, hc23, hlam, hphi, p8407_1]
                                    · have p8407_0 := h8407c.1
                                      have p8407_1 := h8407c.2.1
                                      have p8407_2 := h8407c.2.2.1
                                      have p8407_3 := h8407c.2.2.2
                                      linarith only [hlam, p8407_0]
                                    · have p8407_0 := h8407c.1
                                      have p8407_1 := h8407c.2.1
                                      have p8407_2 := h8407c.2.2.1
                                      have p8407_3 := h8407c.2.2.2
                                      linarith only [h8380, hlam, p8407_0]
                                    · have p8407_0 := h8407c.1
                                      have p8407_1 := h8407c.2.1
                                      have p8407_2 := h8407c.2.2.1
                                      have p8407_3 := h8407c.2.2.2
                                      linarith only [h8380, h8403, h8406, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p8407_1]
                                    · have p8407_0 := h8407c.1
                                      have p8407_1 := h8407c.2.1
                                      have p8407_2 := h8407c.2.2.1
                                      have p8407_3 := h8407c.2.2.2
                                      linarith only [h8380, h8404, h8406, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p8407_1]
                                    · have p8407_0 := h8407c.1
                                      have p8407_1 := h8407c.2.1
                                      have p8407_2 := h8407c.2.2.1
                                      have p8407_3 := h8407c.2.2.2
                                      linarith only [h8375, h8403, h8406, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p8407_1]
                                    · have p8407_0 := h8407c.1
                                      have p8407_1 := h8407c.2.1
                                      have p8407_2 := h8407c.2.2.1
                                      have p8407_3 := h8407c.2.2.2
                                      linarith only [hc12, hc23, hlam, hphi, p8407_1]
                                    · have p8407_0 := h8407c.1
                                      have p8407_1 := h8407c.2.1
                                      have p8407_2 := h8407c.2.2.1
                                      have p8407_3 := h8407c.2.2.2
                                      linarith only [hlam, p8407_0]
                                    · have p8407_0 := h8407c.1
                                      have p8407_1 := h8407c.2.1
                                      have p8407_2 := h8407c.2.2.1
                                      have p8407_3 := h8407c.2.2.2
                                      linarith only [h8403, h8406, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p8407_1]
                                    · have p8407_0 := h8407c.1
                                      have p8407_1 := h8407c.2.1
                                      have p8407_2 := h8407c.2.2.1
                                      have p8407_3 := h8407c.2.2.2
                                      rcases p8407_3 (m.d 0 2) (by simp) with h8422 | h8422
                                      · linarith only [h7871, h8422, hlam]
                                      · linarith only [h8376, h8422, hlam]
                                    · have p8407_0 := h8407c.1
                                      have p8407_1 := h8407c.2.1
                                      have p8407_2 := h8407c.2.2.1
                                      have p8407_3 := h8407c.2.2.2
                                      linarith only [h8375, hlam, p8407_0]
                                    · have p8407_0 := h8407c.1
                                      have p8407_1 := h8407c.2.1
                                      have p8407_2 := h8407c.2.2.1
                                      have p8407_3 := h8407c.2.2.2
                                      linarith only [h8398, hlam, p8407_0]
                                    · have p8407_0 := h8407c.1
                                      have p8407_1 := h8407c.2.1
                                      have p8407_2 := h8407c.2.2.1
                                      have p8407_3 := h8407c.2.2.2
                                      linarith only [h8403, hlam, p8407_0]
                                    · have p8407_0 := h8407c.1
                                      have p8407_1 := h8407c.2.1
                                      have p8407_2 := h8407c.2.2.1
                                      have p8407_3 := h8407c.2.2.2
                                      linarith only [hlam, p8407_0]
                                    · have p8407_0 := h8407c.1
                                      have p8407_1 := h8407c.2.1
                                      have p8407_2 := h8407c.2.2.1
                                      have p8407_3 := h8407c.2.2.2
                                      linarith only [h8375, h8404, h8406, hc02, hc45, hlam, hphi, ht0b, ht5b, p8407_1]
                                    · have p8407_0 := h8407c.1
                                      have p8407_1 := h8407c.2.1
                                      have p8407_2 := h8407c.2.2.1
                                      have p8407_3 := h8407c.2.2.2
                                      linarith only [h8376, hlam, p8407_0]
                                    · have p8407_0 := h8407c.1
                                      have p8407_1 := h8407c.2.1
                                      have p8407_2 := h8407c.2.2.1
                                      have p8407_3 := h8407c.2.2.2
                                      linarith only [h8399, hlam, p8407_0]
                                    · have p8407_0 := h8407c.1
                                      have p8407_1 := h8407c.2.1
                                      have p8407_2 := h8407c.2.2.1
                                      have p8407_3 := h8407c.2.2.2
                                      linarith only [h8404, hlam, p8407_0]
                                    · have p8407_0 := h8407c.1
                                      have p8407_1 := h8407c.2.1
                                      have p8407_2 := h8407c.2.2.1
                                      have p8407_3 := h8407c.2.2.2
                                      linarith only [h8405, hlam, p8407_1]
                                    · have p8407_0 := h8407c.1
                                      have p8407_1 := h8407c.2.1
                                      have p8407_2 := h8407c.2.2.1
                                      have p8407_3 := h8407c.2.2.2
                                      linarith only [hlam, p8407_0]
                                  · linarith only [h6923, h7870, h8380, h8398, h8402, h8406, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                                · linarith only [h6923, h7870, h8380, h8398, h8402, h8405, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                              · linarith only [h6923, h8380, h8398, h8404, hc01, hc35, hlam, hphi, ht12, ht23]
                            · linarith only [h6923, h7870, h8380, h8398, h8402, h8403, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                          · linarith only [h6923, h7870, h8375, h8379, h8399, h8402, hc02, hc25, hlam, hphi, ht0b, ht5b]
                        · linarith only [h5135, h8378, h8401, hlam]
                      · linarith only [h5135, h8377, h8400, hlam]
                    · linarith only [h0, h8376, h8399, hlam]
                  · linarith only [h0, h8375, h8398, hlam]
              · linarith only [h6923, h7870, h8379, hlam]
            · linarith only [h0, h7870, h7871, h8378, hlam]
          · linarith only [h7871, h8375, h8377, hlam]
        · linarith only [h6923, h7870, h8375, h8376, hlam]
      · rcases m.htr 0 2 5 (by decide) (by decide) with h8448 | h8448
        · rcases m.htr 0 3 4 (by decide) (by decide) with h8449 | h8449
          · rcases m.htr 0 3 5 (by decide) (by decide) with h8450 | h8450
            · rcases m.htr 0 4 5 (by decide) (by decide) with h8451 | h8451
              · rcases m.htr 1 2 3 (by decide) (by decide) with h8452 | h8452
                · rcases m.htr 1 2 4 (by decide) (by decide) with h8453 | h8453
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h8454 | h8454
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h8455 | h8455
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h8456 | h8456
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h8457 | h8457
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h8458 | h8458
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h8459 | h8459
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h8460 | h8460
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h8461 | h8461
                                  · rcases h2bigk with h8462c | h8462c | h8462c | h8462c | h8462c | h8462c | h8462c | h8462c | h8462c | h8462c | h8462c | h8462c | h8462c | h8462c | h8462c | h8462c | h8462c | h8462c | h8462c | h8462c | h8462c | h8462c | h8462c | h8462c | h8462c
                                    · have p8462_0 := h8462c.1
                                      have p8462_1 := h8462c.2.1
                                      have p8462_2 := h8462c.2.2.1
                                      have p8462_3 := h8462c.2.2.2
                                      linarith only [hlam, p8462_0]
                                    · have p8462_0 := h8462c.1
                                      have p8462_1 := h8462c.2.1
                                      have p8462_2 := h8462c.2.2.1
                                      have p8462_3 := h8462c.2.2.2
                                      linarith only [h0, hlam, p8462_0]
                                    · have p8462_0 := h8462c.1
                                      have p8462_1 := h8462c.2.1
                                      have p8462_2 := h8462c.2.2.1
                                      have p8462_3 := h8462c.2.2.2
                                      linarith only [h7871, hlam, p8462_0]
                                    · have p8462_0 := h8462c.1
                                      have p8462_1 := h8462c.2.1
                                      have p8462_2 := h8462c.2.2.1
                                      have p8462_3 := h8462c.2.2.2
                                      linarith only [h8375, hlam, p8462_0]
                                    · have p8462_0 := h8462c.1
                                      have p8462_1 := h8462c.2.1
                                      have p8462_2 := h8462c.2.2.1
                                      have p8462_3 := h8462c.2.2.2
                                      linarith only [h8375, h8453, hc14, hc25, hlam, hphi, ht01, ht0b, ht5b, p8462_1]
                                    · have p8462_0 := h8462c.1
                                      have p8462_1 := h8462c.2.1
                                      have p8462_2 := h8462c.2.2.1
                                      have p8462_3 := h8462c.2.2.2
                                      linarith only [h0, h7870, hc12, hc15, hlam, hphi, ht01, ht0b, ht5b, p8462_1]
                                    · have p8462_0 := h8462c.1
                                      have p8462_1 := h8462c.2.1
                                      have p8462_2 := h8462c.2.2.1
                                      have p8462_3 := h8462c.2.2.2
                                      linarith only [hlam, p8462_0]
                                    · have p8462_0 := h8462c.1
                                      have p8462_1 := h8462c.2.1
                                      have p8462_2 := h8462c.2.2.1
                                      have p8462_3 := h8462c.2.2.2
                                      linarith only [h0, h7870, h7871, hc12, hc15, hlam, hphi, ht01, ht0b, ht5b, p8462_1]
                                    · have p8462_0 := h8462c.1
                                      have p8462_1 := h8462c.2.1
                                      have p8462_2 := h8462c.2.2.1
                                      have p8462_3 := h8462c.2.2.2
                                      linarith only [h0, h7870, h8375, hc12, hc15, hlam, hphi, ht01, ht0b, ht5b, p8462_1]
                                    · have p8462_0 := h8462c.1
                                      have p8462_1 := h8462c.2.1
                                      have p8462_2 := h8462c.2.2.1
                                      have p8462_3 := h8462c.2.2.2
                                      rcases p8462_3 (m.d 0 2) (by simp) with h8472 | h8472
                                      · linarith only [h0, h8472, hlam]
                                      · linarith only [h8448, h8472, hlam]
                                    · have p8462_0 := h8462c.1
                                      have p8462_1 := h8462c.2.1
                                      have p8462_2 := h8462c.2.2.1
                                      have p8462_3 := h8462c.2.2.2
                                      linarith only [h0, h7870, h8454, h8459, h8461, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p8462_1]
                                    · have p8462_0 := h8462c.1
                                      have p8462_1 := h8462c.2.1
                                      have p8462_2 := h8462c.2.2.1
                                      have p8462_3 := h8462c.2.2.2
                                      linarith only [h8452, hlam, p8462_0]
                                    · have p8462_0 := h8462c.1
                                      have p8462_1 := h8462c.2.1
                                      have p8462_2 := h8462c.2.2.1
                                      have p8462_3 := h8462c.2.2.2
                                      linarith only [hlam, p8462_0]
                                    · have p8462_0 := h8462c.1
                                      have p8462_1 := h8462c.2.1
                                      have p8462_2 := h8462c.2.2.1
                                      have p8462_3 := h8462c.2.2.2
                                      linarith only [h0, h7870, h8375, h8452, h8454, h8459, h8461, hc13, hc45, hlam, hphi, ht01, ht0b, ht5b, p8462_1]
                                    · have p8462_0 := h8462c.1
                                      have p8462_1 := h8462c.2.1
                                      have p8462_2 := h8462c.2.2.1
                                      have p8462_3 := h8462c.2.2.2
                                      linarith only [h8452, h8459, h8461, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p8462_1]
                                    · have p8462_0 := h8462c.1
                                      have p8462_1 := h8462c.2.1
                                      have p8462_2 := h8462c.2.2.1
                                      have p8462_3 := h8462c.2.2.2
                                      linarith only [h0, h7870, h8453, h8454, h8459, h8461, hc14, hc45, hlam, hphi, ht01, ht0b, ht5b, p8462_1]
                                    · have p8462_0 := h8462c.1
                                      have p8462_1 := h8462c.2.1
                                      have p8462_2 := h8462c.2.2.1
                                      have p8462_3 := h8462c.2.2.2
                                      linarith only [h8453, hlam, p8462_0]
                                    · have p8462_0 := h8462c.1
                                      have p8462_1 := h8462c.2.1
                                      have p8462_2 := h8462c.2.2.1
                                      have p8462_3 := h8462c.2.2.2
                                      linarith only [h8458, hlam, p8462_0]
                                    · have p8462_0 := h8462c.1
                                      have p8462_1 := h8462c.2.1
                                      have p8462_2 := h8462c.2.2.1
                                      have p8462_3 := h8462c.2.2.2
                                      linarith only [hlam, p8462_0]
                                    · have p8462_0 := h8462c.1
                                      have p8462_1 := h8462c.2.1
                                      have p8462_2 := h8462c.2.2.1
                                      have p8462_3 := h8462c.2.2.2
                                      linarith only [h8452, h8458, h8459, h8461, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p8462_1]
                                    · have p8462_0 := h8462c.1
                                      have p8462_1 := h8462c.2.1
                                      have p8462_2 := h8462c.2.2.1
                                      have p8462_3 := h8462c.2.2.2
                                      linarith only [h8448, hlam, p8462_0]
                                    · have p8462_0 := h8462c.1
                                      have p8462_1 := h8462c.2.1
                                      have p8462_2 := h8462c.2.2.1
                                      have p8462_3 := h8462c.2.2.2
                                      linarith only [h8454, hlam, p8462_0]
                                    · have p8462_0 := h8462c.1
                                      have p8462_1 := h8462c.2.1
                                      have p8462_2 := h8462c.2.2.1
                                      have p8462_3 := h8462c.2.2.2
                                      linarith only [h8459, hlam, p8462_0]
                                    · have p8462_0 := h8462c.1
                                      have p8462_1 := h8462c.2.1
                                      have p8462_2 := h8462c.2.2.1
                                      have p8462_3 := h8462c.2.2.2
                                      linarith only [h8460, hlam, p8462_1]
                                    · have p8462_0 := h8462c.1
                                      have p8462_1 := h8462c.2.1
                                      have p8462_2 := h8462c.2.2.1
                                      have p8462_3 := h8462c.2.2.2
                                      linarith only [hlam, p8462_0]
                                  · linarith only [h0, h7870, h7871, h8452, h8457, h8461, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                                · linarith only [h0, h7870, h8375, h8457, h8460, hlam]
                              · linarith only [h0, h7870, h8375, h8450, h8458, h8459, hc03, hc15, hlam, hphi, ht0b, ht5b]
                            · linarith only [h7871, h8449, h8458, hlam]
                          · linarith only [h6923, h8451, h8457, hlam]
                        · linarith only [h5135, h8450, h8456, hlam]
                      · linarith only [h7871, h8449, h8452, h8455, hlam]
                    · linarith only [h8375, h8448, h8454, hc12, hc24, hlam, hphi]
                  · linarith only [h0, h7871, h8452, h8453, hc01, hc24, hlam, hphi, ht12]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h8499 | h8499
                  · linarith only [h0, h7870, h8375, h8452, h8499, hc15, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h8501 | h8501
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h8502 | h8502
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h8503 | h8503
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h8504 | h8504
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h8505 | h8505
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h8506 | h8506
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h8507 | h8507
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h8508 | h8508
                                  · rcases h2bigk with h8509c | h8509c | h8509c | h8509c | h8509c | h8509c | h8509c | h8509c | h8509c | h8509c | h8509c | h8509c | h8509c | h8509c | h8509c | h8509c | h8509c | h8509c | h8509c | h8509c | h8509c | h8509c | h8509c | h8509c | h8509c
                                    · have p8509_0 := h8509c.1
                                      have p8509_1 := h8509c.2.1
                                      have p8509_2 := h8509c.2.2.1
                                      have p8509_3 := h8509c.2.2.2
                                      linarith only [hlam, p8509_0]
                                    · have p8509_0 := h8509c.1
                                      have p8509_1 := h8509c.2.1
                                      have p8509_2 := h8509c.2.2.1
                                      have p8509_3 := h8509c.2.2.2
                                      linarith only [h0, hlam, p8509_0]
                                    · have p8509_0 := h8509c.1
                                      have p8509_1 := h8509c.2.1
                                      have p8509_2 := h8509c.2.2.1
                                      have p8509_3 := h8509c.2.2.2
                                      linarith only [h7871, hlam, p8509_0]
                                    · have p8509_0 := h8509c.1
                                      have p8509_1 := h8509c.2.1
                                      have p8509_2 := h8509c.2.2.1
                                      have p8509_3 := h8509c.2.2.2
                                      linarith only [h8375, hlam, p8509_0]
                                    · have p8509_0 := h8509c.1
                                      have p8509_1 := h8509c.2.1
                                      have p8509_2 := h8509c.2.2.1
                                      have p8509_3 := h8509c.2.2.2
                                      linarith only [h0, h8499, h8505, h8506, h8508, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p8509_1]
                                    · have p8509_0 := h8509c.1
                                      have p8509_1 := h8509c.2.1
                                      have p8509_2 := h8509c.2.2.1
                                      have p8509_3 := h8509c.2.2.2
                                      linarith only [h8499, h8505, hc02, hc23, hlam, hphi, p8509_1]
                                    · have p8509_0 := h8509c.1
                                      have p8509_1 := h8509c.2.1
                                      have p8509_2 := h8509c.2.2.1
                                      have p8509_3 := h8509c.2.2.2
                                      linarith only [hlam, p8509_0]
                                    · have p8509_0 := h8509c.1
                                      have p8509_1 := h8509c.2.1
                                      have p8509_2 := h8509c.2.2.1
                                      have p8509_3 := h8509c.2.2.2
                                      linarith only [h8452, hlam, p8509_0]
                                    · have p8509_0 := h8509c.1
                                      have p8509_1 := h8509c.2.1
                                      have p8509_2 := h8509c.2.2.1
                                      have p8509_3 := h8509c.2.2.2
                                      linarith only [h8499, hlam, p8509_0]
                                    · have p8509_0 := h8509c.1
                                      have p8509_1 := h8509c.2.1
                                      have p8509_2 := h8509c.2.2.1
                                      have p8509_3 := h8509c.2.2.2
                                      linarith only [h8499, h8505, h8506, h8508, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p8509_1]
                                    · have p8509_0 := h8509c.1
                                      have p8509_1 := h8509c.2.1
                                      have p8509_2 := h8509c.2.2.1
                                      have p8509_3 := h8509c.2.2.2
                                      linarith only [h0, h7870, h8501, h8506, h8508, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p8509_1]
                                    · have p8509_0 := h8509c.1
                                      have p8509_1 := h8509c.2.1
                                      have p8509_2 := h8509c.2.2.1
                                      have p8509_3 := h8509c.2.2.2
                                      linarith only [hc12, hc23, hlam, hphi, p8509_1]
                                    · have p8509_0 := h8509c.1
                                      have p8509_1 := h8509c.2.1
                                      have p8509_2 := h8509c.2.2.1
                                      have p8509_3 := h8509c.2.2.2
                                      linarith only [hlam, p8509_0]
                                    · have p8509_0 := h8509c.1
                                      have p8509_1 := h8509c.2.1
                                      have p8509_2 := h8509c.2.2.1
                                      have p8509_3 := h8509c.2.2.2
                                      linarith only [h0, h7870, h8375, h8501, h8506, h8508, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p8509_1]
                                    · have p8509_0 := h8509c.1
                                      have p8509_1 := h8509c.2.1
                                      have p8509_2 := h8509c.2.2.1
                                      have p8509_3 := h8509c.2.2.2
                                      rcases p8509_3 (m.d 0 2) (by simp) with h8524 | h8524
                                      · linarith only [h7871, h8524, hlam]
                                      · linarith only [h8448, h8524, hlam]
                                    · have p8509_0 := h8509c.1
                                      have p8509_1 := h8509c.2.1
                                      have p8509_2 := h8509c.2.2.1
                                      have p8509_3 := h8509c.2.2.2
                                      linarith only [h0, h7870, h8501, h8506, h8508, hc24, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p8509_1]
                                    · have p8509_0 := h8509c.1
                                      have p8509_1 := h8509c.2.1
                                      have p8509_2 := h8509c.2.2.1
                                      have p8509_3 := h8509c.2.2.2
                                      linarith only [h0, h7870, h8501, h8506, h8508, hc24, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p8509_1]
                                    · have p8509_0 := h8509c.1
                                      have p8509_1 := h8509c.2.1
                                      have p8509_2 := h8509c.2.2.1
                                      have p8509_3 := h8509c.2.2.2
                                      linarith only [h8505, hlam, p8509_0]
                                    · have p8509_0 := h8509c.1
                                      have p8509_1 := h8509c.2.1
                                      have p8509_2 := h8509c.2.2.1
                                      have p8509_3 := h8509c.2.2.2
                                      linarith only [hlam, p8509_0]
                                    · have p8509_0 := h8509c.1
                                      have p8509_1 := h8509c.2.1
                                      have p8509_2 := h8509c.2.2.1
                                      have p8509_3 := h8509c.2.2.2
                                      rcases p8509_3 (m.d 0 2) (by simp) with h8531 | h8531
                                      · linarith only [h8375, h8531, hlam]
                                      · linarith only [h8448, h8531, hlam]
                                    · have p8509_0 := h8509c.1
                                      have p8509_1 := h8509c.2.1
                                      have p8509_2 := h8509c.2.2.1
                                      have p8509_3 := h8509c.2.2.2
                                      linarith only [h8448, hlam, p8509_0]
                                    · have p8509_0 := h8509c.1
                                      have p8509_1 := h8509c.2.1
                                      have p8509_2 := h8509c.2.2.1
                                      have p8509_3 := h8509c.2.2.2
                                      linarith only [h8501, hlam, p8509_0]
                                    · have p8509_0 := h8509c.1
                                      have p8509_1 := h8509c.2.1
                                      have p8509_2 := h8509c.2.2.1
                                      have p8509_3 := h8509c.2.2.2
                                      linarith only [h8506, hlam, p8509_0]
                                    · have p8509_0 := h8509c.1
                                      have p8509_1 := h8509c.2.1
                                      have p8509_2 := h8509c.2.2.1
                                      have p8509_3 := h8509c.2.2.2
                                      linarith only [h8507, hlam, p8509_1]
                                    · have p8509_0 := h8509c.1
                                      have p8509_1 := h8509c.2.1
                                      have p8509_2 := h8509c.2.2.1
                                      have p8509_3 := h8509c.2.2.2
                                      linarith only [hlam, p8509_0]
                                  · linarith only [h0, h7870, h8499, h8504, h8505, h8508, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                                · linarith only [h0, h7870, h8499, h8504, h8507, hlam]
                              · linarith only [h0, h8499, h8505, h8506, hc01, hc35, hlam, hphi, ht12, ht23]
                            · linarith only [h0, h7870, h8452, h8501, h8505, hc25, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                          · linarith only [h0, h7870, h8449, h8451, h8499, h8501, h8504, hc03, hc25, hlam, hphi, ht0b, ht5b]
                        · linarith only [h0, h7870, h8450, h8499, h8501, h8502, h8503, hc03, hc25, hlam, hphi, ht0b, ht5b]
                      · linarith only [h5135, h7870, h8449, h8501, h8502, hc03, hc25, hlam, hphi, ht0b, ht5b]
                    · linarith only [h0, h7870, h8375, h8448, h8501, hc04, hc15, hlam, hphi, ht0b, ht5b]
              · linarith only [h0, h7870, h8375, h8451, hlam]
            · linarith only [h0, h7870, h8375, h8449, h8450, hlam]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h8549 | h8549
            · rcases m.htr 0 4 5 (by decide) (by decide) with h8550 | h8550
              · rcases m.htr 1 2 3 (by decide) (by decide) with h8551 | h8551
                · rcases m.htr 1 2 4 (by decide) (by decide) with h8552 | h8552
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h8553 | h8553
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h8554 | h8554
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h8555 | h8555
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h8556 | h8556
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h8557 | h8557
                            · linarith only [h0, h7870, h7871, h8449, h8551, h8553, h8557, hc12, hc25, hlam, hphi, ht01, ht0b, ht5b]
                            · linarith only [h0, h7870, h7871, h8553, h8554, h8557, hc13, hc25, hlam, hphi, ht01, ht0b, ht5b]
                          · linarith only [h6923, h7870, h8550, h8553, h8556, hc04, hc25, hlam, hphi, ht0b, ht5b]
                        · linarith only [h0, h7870, h7871, h8449, h8553, h8554, h8555, hc25, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h8562 | h8562
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h8563 | h8563
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h8564 | h8564
                            · linarith only [h8551, h8554, h8564, hlam]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h8566 | h8566
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h8567 | h8567
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h8568 | h8568
                                  · rcases h2bigk with h8569c | h8569c | h8569c | h8569c | h8569c | h8569c | h8569c | h8569c | h8569c | h8569c | h8569c | h8569c | h8569c | h8569c | h8569c | h8569c | h8569c | h8569c | h8569c | h8569c | h8569c | h8569c | h8569c | h8569c | h8569c
                                    · have p8569_0 := h8569c.1
                                      have p8569_1 := h8569c.2.1
                                      have p8569_2 := h8569c.2.2.1
                                      have p8569_3 := h8569c.2.2.2
                                      linarith only [hlam, p8569_0]
                                    · have p8569_0 := h8569c.1
                                      have p8569_1 := h8569c.2.1
                                      have p8569_2 := h8569c.2.2.1
                                      have p8569_3 := h8569c.2.2.2
                                      linarith only [h0, hlam, p8569_0]
                                    · have p8569_0 := h8569c.1
                                      have p8569_1 := h8569c.2.1
                                      have p8569_2 := h8569c.2.2.1
                                      have p8569_3 := h8569c.2.2.2
                                      linarith only [h7871, hlam, p8569_0]
                                    · have p8569_0 := h8569c.1
                                      have p8569_1 := h8569c.2.1
                                      have p8569_2 := h8569c.2.2.1
                                      have p8569_3 := h8569c.2.2.2
                                      linarith only [h8375, hlam, p8569_0]
                                    · have p8569_0 := h8569c.1
                                      have p8569_1 := h8569c.2.1
                                      have p8569_2 := h8569c.2.2.1
                                      have p8569_3 := h8569c.2.2.2
                                      linarith only [h7871, h8551, h8566, h8568, hc13, hc45, hlam, hphi, ht01, ht0b, ht5b, p8569_1]
                                    · have p8569_0 := h8569c.1
                                      have p8569_1 := h8569c.2.1
                                      have p8569_2 := h8569c.2.2.1
                                      have p8569_3 := h8569c.2.2.2
                                      linarith only [h0, h7870, h8553, h8566, h8568, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p8569_1]
                                    · have p8569_0 := h8569c.1
                                      have p8569_1 := h8569c.2.1
                                      have p8569_2 := h8569c.2.2.1
                                      have p8569_3 := h8569c.2.2.2
                                      linarith only [hlam, p8569_0]
                                    · have p8569_0 := h8569c.1
                                      have p8569_1 := h8569c.2.1
                                      have p8569_2 := h8569c.2.2.1
                                      have p8569_3 := h8569c.2.2.2
                                      linarith only [h0, h7870, h7871, h8553, h8566, h8568, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p8569_1]
                                    · have p8569_0 := h8569c.1
                                      have p8569_1 := h8569c.2.1
                                      have p8569_2 := h8569c.2.2.1
                                      have p8569_3 := h8569c.2.2.2
                                      linarith only [h6923, h7870, h8375, h8553, h8566, h8568, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p8569_1]
                                    · have p8569_0 := h8569c.1
                                      have p8569_1 := h8569c.2.1
                                      have p8569_2 := h8569c.2.2.1
                                      have p8569_3 := h8569c.2.2.2
                                      rcases p8569_3 (m.d 0 2) (by simp) with h8579 | h8579
                                      · linarith only [h0, h8579, hlam]
                                      · linarith only [h8448, h8579, hlam]
                                    · have p8569_0 := h8569c.1
                                      have p8569_1 := h8569c.2.1
                                      have p8569_2 := h8569c.2.2.1
                                      have p8569_3 := h8569c.2.2.2
                                      linarith only [h0, h7870, h8553, h8566, h8568, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p8569_1]
                                    · have p8569_0 := h8569c.1
                                      have p8569_1 := h8569c.2.1
                                      have p8569_2 := h8569c.2.2.1
                                      have p8569_3 := h8569c.2.2.2
                                      linarith only [h8551, hlam, p8569_0]
                                    · have p8569_0 := h8569c.1
                                      have p8569_1 := h8569c.2.1
                                      have p8569_2 := h8569c.2.2.1
                                      have p8569_3 := h8569c.2.2.2
                                      linarith only [hlam, p8569_0]
                                    · have p8569_0 := h8569c.1
                                      have p8569_1 := h8569c.2.1
                                      have p8569_2 := h8569c.2.2.1
                                      have p8569_3 := h8569c.2.2.2
                                      linarith only [h8564, hlam, p8569_1]
                                    · have p8569_0 := h8569c.1
                                      have p8569_1 := h8569c.2.1
                                      have p8569_2 := h8569c.2.2.1
                                      have p8569_3 := h8569c.2.2.2
                                      linarith only [h8551, h8566, h8568, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p8569_1]
                                    · have p8569_0 := h8569c.1
                                      have p8569_1 := h8569c.2.1
                                      have p8569_2 := h8569c.2.2.1
                                      have p8569_3 := h8569c.2.2.2
                                      linarith only [h0, h7870, h8552, h8553, h8566, h8568, hc14, hc45, hlam, hphi, ht01, ht0b, ht5b, p8569_1]
                                    · have p8569_0 := h8569c.1
                                      have p8569_1 := h8569c.2.1
                                      have p8569_2 := h8569c.2.2.1
                                      have p8569_3 := h8569c.2.2.2
                                      linarith only [h8552, hlam, p8569_0]
                                    · have p8569_0 := h8569c.1
                                      have p8569_1 := h8569c.2.1
                                      have p8569_2 := h8569c.2.2.1
                                      have p8569_3 := h8569c.2.2.2
                                      linarith only [h8552, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p8569_1]
                                    · have p8569_0 := h8569c.1
                                      have p8569_1 := h8569c.2.1
                                      have p8569_2 := h8569c.2.2.1
                                      have p8569_3 := h8569c.2.2.2
                                      linarith only [hlam, p8569_0]
                                    · have p8569_0 := h8569c.1
                                      have p8569_1 := h8569c.2.1
                                      have p8569_2 := h8569c.2.2.1
                                      have p8569_3 := h8569c.2.2.2
                                      linarith only [h8552, h8566, h8568, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p8569_1]
                                    · have p8569_0 := h8569c.1
                                      have p8569_1 := h8569c.2.1
                                      have p8569_2 := h8569c.2.2.1
                                      have p8569_3 := h8569c.2.2.2
                                      linarith only [h8448, hlam, p8569_0]
                                    · have p8569_0 := h8569c.1
                                      have p8569_1 := h8569c.2.1
                                      have p8569_2 := h8569c.2.2.1
                                      have p8569_3 := h8569c.2.2.2
                                      linarith only [h8553, hlam, p8569_0]
                                    · have p8569_0 := h8569c.1
                                      have p8569_1 := h8569c.2.1
                                      have p8569_2 := h8569c.2.2.1
                                      have p8569_3 := h8569c.2.2.2
                                      linarith only [h8566, hlam, p8569_0]
                                    · have p8569_0 := h8569c.1
                                      have p8569_1 := h8569c.2.1
                                      have p8569_2 := h8569c.2.2.1
                                      have p8569_3 := h8569c.2.2.2
                                      linarith only [h8567, hlam, p8569_1]
                                    · have p8569_0 := h8569c.1
                                      have p8569_1 := h8569c.2.1
                                      have p8569_2 := h8569c.2.2.1
                                      have p8569_3 := h8569c.2.2.2
                                      linarith only [hlam, p8569_0]
                                  · linarith only [h0, h7870, h7871, h8551, h8553, h8554, h8566, h8568, hc35, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b]
                                · linarith only [h0, h7870, h7871, h8551, h8554, h8563, h8567, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                              · linarith only [h0, h7870, h7871, h8449, h8549, h8566, hc04, hc15, hlam, hphi, ht0b, ht5b]
                          · linarith only [h6923, h7870, h8550, h8553, h8563, hc04, hc25, hlam, hphi, ht0b, ht5b]
                        · linarith only [h0, h7870, h7871, h8549, h8551, h8553, h8562, hc03, hc25, hlam, hphi, ht0b, ht5b]
                    · linarith only [h0, h7870, h8375, h8552, h8553, hc15, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b]
                  · linarith only [h0, h7870, h7871, h8551, h8552, hc15, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h8604 | h8604
                  · linarith only [h0, h7870, h8375, h8551, h8604, hc15, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h8606 | h8606
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h8607 | h8607
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h8608 | h8608
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h8609 | h8609
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h8610 | h8610
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h8611 | h8611
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h8612 | h8612
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h8613 | h8613
                                  · rcases h2bigk with h8614c | h8614c | h8614c | h8614c | h8614c | h8614c | h8614c | h8614c | h8614c | h8614c | h8614c | h8614c | h8614c | h8614c | h8614c | h8614c | h8614c | h8614c | h8614c | h8614c | h8614c | h8614c | h8614c | h8614c | h8614c
                                    · have p8614_0 := h8614c.1
                                      have p8614_1 := h8614c.2.1
                                      have p8614_2 := h8614c.2.2.1
                                      have p8614_3 := h8614c.2.2.2
                                      linarith only [hlam, p8614_0]
                                    · have p8614_0 := h8614c.1
                                      have p8614_1 := h8614c.2.1
                                      have p8614_2 := h8614c.2.2.1
                                      have p8614_3 := h8614c.2.2.2
                                      linarith only [h0, hlam, p8614_0]
                                    · have p8614_0 := h8614c.1
                                      have p8614_1 := h8614c.2.1
                                      have p8614_2 := h8614c.2.2.1
                                      have p8614_3 := h8614c.2.2.2
                                      linarith only [h7871, hlam, p8614_0]
                                    · have p8614_0 := h8614c.1
                                      have p8614_1 := h8614c.2.1
                                      have p8614_2 := h8614c.2.2.1
                                      have p8614_3 := h8614c.2.2.2
                                      linarith only [h8375, hlam, p8614_0]
                                    · have p8614_0 := h8614c.1
                                      have p8614_1 := h8614c.2.1
                                      have p8614_2 := h8614c.2.2.1
                                      have p8614_3 := h8614c.2.2.2
                                      linarith only [h0, h8604, h8610, h8611, h8613, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p8614_1]
                                    · have p8614_0 := h8614c.1
                                      have p8614_1 := h8614c.2.1
                                      have p8614_2 := h8614c.2.2.1
                                      have p8614_3 := h8614c.2.2.2
                                      linarith only [h8604, h8610, hc02, hc23, hlam, hphi, p8614_1]
                                    · have p8614_0 := h8614c.1
                                      have p8614_1 := h8614c.2.1
                                      have p8614_2 := h8614c.2.2.1
                                      have p8614_3 := h8614c.2.2.2
                                      linarith only [hlam, p8614_0]
                                    · have p8614_0 := h8614c.1
                                      have p8614_1 := h8614c.2.1
                                      have p8614_2 := h8614c.2.2.1
                                      have p8614_3 := h8614c.2.2.2
                                      linarith only [h8551, hlam, p8614_0]
                                    · have p8614_0 := h8614c.1
                                      have p8614_1 := h8614c.2.1
                                      have p8614_2 := h8614c.2.2.1
                                      have p8614_3 := h8614c.2.2.2
                                      linarith only [h8604, hlam, p8614_0]
                                    · have p8614_0 := h8614c.1
                                      have p8614_1 := h8614c.2.1
                                      have p8614_2 := h8614c.2.2.1
                                      have p8614_3 := h8614c.2.2.2
                                      linarith only [h8604, h8610, h8611, h8613, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p8614_1]
                                    · have p8614_0 := h8614c.1
                                      have p8614_1 := h8614c.2.1
                                      have p8614_2 := h8614c.2.2.1
                                      have p8614_3 := h8614c.2.2.2
                                      linarith only [h0, h7870, h8606, h8611, h8613, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p8614_1]
                                    · have p8614_0 := h8614c.1
                                      have p8614_1 := h8614c.2.1
                                      have p8614_2 := h8614c.2.2.1
                                      have p8614_3 := h8614c.2.2.2
                                      linarith only [hc12, hc23, hlam, hphi, p8614_1]
                                    · have p8614_0 := h8614c.1
                                      have p8614_1 := h8614c.2.1
                                      have p8614_2 := h8614c.2.2.1
                                      have p8614_3 := h8614c.2.2.2
                                      linarith only [hlam, p8614_0]
                                    · have p8614_0 := h8614c.1
                                      have p8614_1 := h8614c.2.1
                                      have p8614_2 := h8614c.2.2.1
                                      have p8614_3 := h8614c.2.2.2
                                      linarith only [h0, h7870, h8375, h8606, h8611, h8613, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p8614_1]
                                    · have p8614_0 := h8614c.1
                                      have p8614_1 := h8614c.2.1
                                      have p8614_2 := h8614c.2.2.1
                                      have p8614_3 := h8614c.2.2.2
                                      rcases p8614_3 (m.d 0 2) (by simp) with h8629 | h8629
                                      · linarith only [h7871, h8629, hlam]
                                      · linarith only [h8448, h8629, hlam]
                                    · have p8614_0 := h8614c.1
                                      have p8614_1 := h8614c.2.1
                                      have p8614_2 := h8614c.2.2.1
                                      have p8614_3 := h8614c.2.2.2
                                      linarith only [h0, h7870, h8606, h8611, h8613, hc24, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p8614_1]
                                    · have p8614_0 := h8614c.1
                                      have p8614_1 := h8614c.2.1
                                      have p8614_2 := h8614c.2.2.1
                                      have p8614_3 := h8614c.2.2.2
                                      linarith only [h0, h7870, h8606, h8611, h8613, hc24, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p8614_1]
                                    · have p8614_0 := h8614c.1
                                      have p8614_1 := h8614c.2.1
                                      have p8614_2 := h8614c.2.2.1
                                      have p8614_3 := h8614c.2.2.2
                                      linarith only [h8610, hlam, p8614_0]
                                    · have p8614_0 := h8614c.1
                                      have p8614_1 := h8614c.2.1
                                      have p8614_2 := h8614c.2.2.1
                                      have p8614_3 := h8614c.2.2.2
                                      linarith only [hlam, p8614_0]
                                    · have p8614_0 := h8614c.1
                                      have p8614_1 := h8614c.2.1
                                      have p8614_2 := h8614c.2.2.1
                                      have p8614_3 := h8614c.2.2.2
                                      rcases p8614_3 (m.d 0 2) (by simp) with h8636 | h8636
                                      · linarith only [h8375, h8636, hlam]
                                      · linarith only [h8448, h8636, hlam]
                                    · have p8614_0 := h8614c.1
                                      have p8614_1 := h8614c.2.1
                                      have p8614_2 := h8614c.2.2.1
                                      have p8614_3 := h8614c.2.2.2
                                      linarith only [h8448, hlam, p8614_0]
                                    · have p8614_0 := h8614c.1
                                      have p8614_1 := h8614c.2.1
                                      have p8614_2 := h8614c.2.2.1
                                      have p8614_3 := h8614c.2.2.2
                                      linarith only [h8606, hlam, p8614_0]
                                    · have p8614_0 := h8614c.1
                                      have p8614_1 := h8614c.2.1
                                      have p8614_2 := h8614c.2.2.1
                                      have p8614_3 := h8614c.2.2.2
                                      linarith only [h8611, hlam, p8614_0]
                                    · have p8614_0 := h8614c.1
                                      have p8614_1 := h8614c.2.1
                                      have p8614_2 := h8614c.2.2.1
                                      have p8614_3 := h8614c.2.2.2
                                      linarith only [h8612, hlam, p8614_1]
                                    · have p8614_0 := h8614c.1
                                      have p8614_1 := h8614c.2.1
                                      have p8614_2 := h8614c.2.2.1
                                      have p8614_3 := h8614c.2.2.2
                                      linarith only [hlam, p8614_0]
                                  · linarith only [h0, h6923, h7871, h8449, h8550, h8607, h8613, hc01, hc13, hlam, hphi]
                                · linarith only [h0, h7870, h8604, h8609, h8612, hlam]
                              · linarith only [h0, h7871, h8449, h8551, h8607, h8611, hc01, hc35, hlam, hphi, ht12, ht23]
                            · linarith only [h8551, h8607, h8610, hlam]
                          · linarith only [h6923, h8550, h8609, hlam]
                        · linarith only [h0, h7870, h7871, h8449, h8606, h8607, h8608, hc25, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h8650 | h8650
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h8651 | h8651
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h8652 | h8652
                            · linarith only [h0, h7870, h8551, h8606, h8607, h8652, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b]
                            · linarith only [h0, h7870, h8551, h8606, h8652, hc25, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                          · linarith only [h6923, h8550, h8651, hlam]
                        · linarith only [h0, h7870, h8549, h8551, h8606, h8650, hc03, hc25, hlam, hphi, ht0b, ht5b]
                    · linarith only [h0, h7870, h8448, h8606, hc02, hc15, hlam, hphi, ht0b, ht5b]
              · linarith only [h0, h7870, h7871, h8449, h8550, hlam]
            · linarith only [h0, h7870, h7871, h8549, hlam]
        · linarith only [h0, h7870, h8448, hlam]
  · exact r1l7_22_13_15_H_I_L_I_L_I_s8 m hb2 hb3 hb5 h0 h5135 h6923 h7870

end R2N4
