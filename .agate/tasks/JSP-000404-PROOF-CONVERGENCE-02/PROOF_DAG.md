# Proof DAG — PROOF-CONVERGENCE-02 (source-verified at 9945ee8)

    sendov_lower (N≥9 branch: sorry — ROOT GAP)
      └─ sendov_lower_of_selection  [Integration]  PROVED conditional
           └─ count_bound_trivial_of_selection
                └─ staircaseBound_of_selection
                     ├─ exponents_lt_of_floor            PROVED
                     └─ GadgetSelection {low, high}      OPEN
                          └─ gadgetSelection_of_geometricCertificates
                               [CertificateIntegration]  PROVED conditional
                               └─ GeometricCertificates: CertExists (n≥3)
                                    └─ staircase_of_cert →
                                       potential_le_sendovCap
                                       [Induction]      PROVED conditional
                                        └─ CertExists:
                                           over-cap legal cfg ⇒
                                           EmissionDichotomy   OPEN ← crux
                                             └─ removable_of_dichotomy
                                                (proved) ⇒ removable vtx

    Consumer decomposition of CertExists (regimes, S = #saturated rows):
      n=1 both regimes                PROVED (SmallStrip)
      n=2 both regimes                PROVED (SecondStrip{,High})
      LOW  S≥1                        PROVED (OneSaturatedLow)
      HIGH S≥2                        PROVED (TwoSaturatedHigh)
      ── remaining, all n≥3 ──
      R-LOW0   δ<1/2, S=0  → K≤1      OPEN
      R-HIGH1  ½≤δ<1, S=1  → K≤5/4    OPEN  ← MAIN TARGET
      R-HIGH0  ½≤δ<1, S=0  → K≤5/4    OPEN

    Certificate machinery (K3bGeometry, ported):
      tri_piece_rel                   PROVED — per-piece arc identity
      signed_chain_cert (variant A)   PROVED — right fan at x_L
      signed_chain_certB (variant B)  PROVED — endpoint fan + m_j bounds
      signed_chain_extend             PROVED — σ' = σ+1+b'−b−q
      leaf_0001_cert / _extend_cert   PROVED — concrete regressions
      leaf_0046_certB                 PROVED — endpoint regression
      arc_overflow_geometric_of_cells PROVED — fat-arc certificate
      cycle_cert_delta                PROVED — polygon certificate
      exists_first_overfull_level_ge_two PROVED — K>B ⇒ level m∈[2,n]
      ResidualWitness.ge_of           PROVED — τ-parameterized closing

    NOT proved anywhere:
      K>B ⇒ existence of *some* certificate (selection).
      Skeleton-driven scans are diagnostics, not proofs.

    Empirical witness status (witnesses/*.jsonl, verify_cert):
      s6: 101/101 replayed (cap-cap / cap-fan topologies only)
      n4_high: 387/519 replayed, 20 rejected, 112 unclassified
      n4_low: 285/401 replayed, 116 unclassified
      leaf_0177 (mixed-sign two-row family): UNCLASSIFIED
