import Jsp000404.N4R2OuterLeftReplay
import Jsp000404.N4R2WordCatalog

set_option autoImplicit false
set_option pp.fullNames true
set_option maxRecDepth 8192
set_option maxHeartbeats 0
set_option Elab.async false

namespace Jsp404.N4R2OuterLeftData.LeafShard139
open N4R2OuterLeftReplay

-- Cycle fingerprint 0065e6a44ac8ef33a1d7b3c2cb128be35e17586cda1b543e0581e5c07115a53b.
def localCycle00000 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 3, .distance 1 2, .theta 1, .zero, .theta 4, .distance 3 4, .distance 4 5, .distance 5 6, .distance 1 5, .distance 1 4, .distance 1 3]
    constant := ![-2, -1, 0, 0, 3, -1, -1, -1, -2, 0]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false, false, true] }
  origin := ![.gapLower 1 1, .corridorLower 1 2, .thetaLower 1, .thetaUpper 4, .corridorUpper 3 4, .triangle 31 0, .triangle 34 0, .triangle 24 0, .gapLower 1 3, .triangle 19 1]

-- Cycle fingerprint 0115d0d7c9f749ee696a10b7316437c4411cb2205935831f0355c61e91941b2b.
def localCycle00001 : Cycle where
  length := 9
  data := {
    node := ![.theta 1, .zero, .theta 4, .distance 3 4, .distance 4 5, .distance 5 6, .distance 1 5, .distance 1 4, .distance 1 2, .theta 1]
    constant := ![0, 0, 3, -1, -1, -1, 0, 0, -2]
    coefficient := ![0, 1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, true, false] }
  origin := ![.thetaLower 1, .thetaUpper 4, .corridorUpper 3 4, .triangle 31 0, .triangle 34 0, .triangle 24 0, .gapLower 1 3, .triangle 16 1, .gapLower 1 0]

-- Cycle fingerprint 015ae997564c721ed4519130540bce7fd3208eeb7a653670d01a82870c05b2d0.
def localCycle00002 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 6, .distance 1 5, .distance 1 4, .distance 1 3, .theta 1, .zero, .theta 6, .distance 1 6]
    constant := ![-2, 0, -2, -1, 0, 0, 2]
    coefficient := ![0, 0, 0, 0, 0, 1, 0]
    strict := ![false, true, false, false, false, false, true] }
  origin := ![.gapLower 1 4, .triangle 22 1, .gapLower 1 2, .corridorLower 1 3, .thetaLower 1, .thetaUpper 6, .gapUpper 6 0]

-- Cycle fingerprint 019d539540fc9f332454b0aedf6febf7d8fca0c882672d2a162e6d54846cf037.
def localCycle00003 : Cycle where
  length := 10
  data := {
    node := ![.theta 1, .zero, .theta 4, .distance 3 4, .distance 2 4, .distance 4 5, .distance 5 6, .distance 1 5, .distance 1 4, .distance 1 3, .theta 1]
    constant := ![0, 0, 3, 0, -1, -1, -1, 0, -3, -1]
    coefficient := ![0, 1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, false, false, false] }
  origin := ![.thetaLower 1, .thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 28 0, .triangle 34 0, .triangle 24 0, .gapLower 1 3, .gapLower 1 2, .corridorLower 1 3]

-- Cycle fingerprint 020194d208f8368797fce0f3b9d281c4f999863315b73063d7923e3a5bd7dad3.
def localCycle00004 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 5, .distance 1 6, .distance 1 2, .theta 1, .distance 0 1, .distance 0 4, .distance 4 5, .distance 1 5]
    constant := ![-2, 0, -2, 3, 0, -1, 0]
    coefficient := ![0, 0, 0, 1, 0, 0, 0]
    strict := ![false, true, false, false, true, false, true] }
  origin := ![.gapLower 1 4, .triangle 18 1, .gapLower 1 0, .corridorUpper 0 1, .triangle 2 2, .triangle 12 0, .triangle 22 2]

-- Cycle fingerprint 0310ff91b2389153a1c2728f6df594b74a2179188755e0388c2847cc91b9632b.
def localCycle00005 : Cycle where
  length := 4
  data := {
    node := ![.theta 1, .distance 0 1, .distance 1 4, .distance 1 6, .theta 1]
    constant := ![2, -1, -2, -1]
    coefficient := ![1, 0, 0, 0]
    strict := ![false, false, false, false] }
  origin := ![.gapLower 1 6, .triangle 2 0, .gapLower 1 4, .corridorLower 1 6]

-- Cycle fingerprint 03c47046f7e05877a51d898810632daeffdc30b21f12253f6db94af585c67aa7.
def localCycle00006 : Cycle where
  length := 5
  data := {
    node := ![.distance 1 2, .theta 1, .distance 0 1, .distance 1 4, .distance 1 6, .distance 1 2]
    constant := ![-2, 3, -1, -2, 0]
    coefficient := ![0, 1, 0, 0, 0]
    strict := ![false, false, false, false, true] }
  origin := ![.gapLower 1 0, .corridorUpper 0 1, .triangle 2 0, .gapLower 1 4, .triangle 18 1]

-- Cycle fingerprint 044020b637dc16150e616d6b21f0d8e7671d9b33f8e2089ce631d3ed49a42946.
def localCycle00007 : Cycle where
  length := 8
  data := {
    node := ![.distance 5 6, .distance 4 6, .distance 3 4, .distance 2 3, .distance 1 2, .theta 1, .zero, .theta 6, .distance 5 6]
    constant := ![0, -1, -1, -1, -3, 0, 0, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 1]
    strict := ![true, false, false, false, false, false, false, false] }
  origin := ![.triangle 34 2, .triangle 32 0, .triangle 25 0, .triangle 15 0, .gapLower 1 0, .thetaLower 1, .thetaUpper 6, .corridorUpper 5 6]

-- Cycle fingerprint 05a2d36fa6d0bde4651f10da4d306254a009cd05f8dd87faa12a058604872f7f.
def localCycle00008 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 4, .distance 4 6, .distance 4 5, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1, .distance 0 1, .distance 0 4]
    constant := ![-1, 0, -1, 0, -3, -1, 3, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 0]
    strict := ![false, true, false, false, false, false, false, true] }
  origin := ![.triangle 13 0, .triangle 34 1, .triangle 22 0, .gapLower 1 2, .gapLower 1 1, .corridorLower 1 2, .corridorUpper 0 1, .triangle 2 2]

-- Cycle fingerprint 05be4b8280dd62e559e7eae6eccca7a902dfcc8cf37354b7283d5a0666c7e497.
def localCycle00009 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 6, .distance 1 5, .distance 1 4, .theta 1, .distance 0 1, .distance 0 4, .distance 4 6, .distance 1 6]
    constant := ![-2, -2, -1, 3, 0, -1, 0]
    coefficient := ![0, 0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, false, true, false, true] }
  origin := ![.gapLower 1 4, .gapLower 1 3, .corridorLower 1 4, .corridorUpper 0 1, .triangle 2 2, .triangle 13 0, .triangle 23 2]

-- Cycle fingerprint 0625f28701ed9aaf86a20dd5087323a4311453cfe893a8a3da0a3edb8061ac90.
def localCycle00010 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 3, .distance 1 2, .theta 1, .zero, .theta 6, .distance 1 6, .distance 1 4, .distance 1 3]
    constant := ![-2, -2, 0, 0, 2, 0, 0]
    coefficient := ![0, 0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, false, true, true, true] }
  origin := ![.gapLower 1 1, .gapLower 1 0, .thetaLower 1, .thetaUpper 6, .gapUpper 6 0, .triangle 23 1, .triangle 19 1]

-- Cycle fingerprint 0648486c8d52a96ddb39e786d2d965de27fba9586b6ab2f7c0fcea5035e9d076.
def localCycle00011 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 5, .distance 5 6, .distance 1 5, .distance 1 4, .theta 1, .distance 0 1, .distance 0 5]
    constant := ![-1, -1, 0, -1, 2, 0]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![false, false, true, false, false, true] }
  origin := ![.triangle 14 0, .triangle 24 0, .triangle 22 1, .corridorLower 1 4, .gapLower 1 6, .triangle 3 2]

-- Cycle fingerprint 066ec91c44f745de7ab9f2fdfb156a53b1501b7b1ad494e7b11f9cfc435262bb.
def localCycle00012 : Cycle where
  length := 7
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 4, .distance 4 5, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1]
    constant := ![1, 0, -1, -1, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, true, false] }
  origin := ![.gapLower 1 6, .triangle 2 2, .triangle 12 0, .triangle 22 0, .gapLower 1 2, .triangle 15 1, .corridorLower 1 2]

-- Cycle fingerprint 06730242989941dbff2fade7f7299ceaa8afbe07f39f0d5107e58fd10a551dfa.
def localCycle00013 : Cycle where
  length := 6
  data := {
    node := ![.distance 1 4, .distance 1 3, .distance 1 2, .theta 1, .distance 0 1, .distance 1 6, .distance 1 4]
    constant := ![0, 0, -1, 3, -3, 0]
    coefficient := ![0, 0, 0, 1, 0, 0]
    strict := ![true, true, false, false, false, true] }
  origin := ![.triangle 19 1, .triangle 15 1, .corridorLower 1 2, .corridorUpper 0 1, .gapLower 1 5, .triangle 23 1]

-- Cycle fingerprint 075839057fd939e335ff6529513a7b3b2f1f2335ed10d894ab166511dc2e7fa9.
def localCycle00014 : Cycle where
  length := 6
  data := {
    node := ![.theta 4, .distance 3 4, .distance 4 6, .distance 2 4, .distance 0 4, .distance 4 5, .theta 4]
    constant := ![3, -1, -1, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 32 0, .triangle 29 0, .triangle 6 2, .triangle 12 0, .corridorLower 4 5]

-- Cycle fingerprint 079d244a867b77da8a8a6855d72500fd34b51f44195c7c71391c4319c2891fb7.
def localCycle00015 : Cycle where
  length := 8
  data := {
    node := ![.distance 4 5, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1, .distance 0 1, .distance 0 6, .distance 0 4, .distance 4 5]
    constant := ![-1, 0, 0, -1, 2, 0, 0, -1]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![false, false, true, false, false, true, true, false] }
  origin := ![.triangle 22 0, .gapLower 1 2, .triangle 15 1, .corridorLower 1 2, .gapLower 1 6, .triangle 4 2, .triangle 13 1, .triangle 12 0]

-- Cycle fingerprint 07a978c3c9c6183724e92af296a2ea282f69eb273b55865f202306c04c1e2a54.
def localCycle00016 : Cycle where
  length := 5
  data := {
    node := ![.distance 1 6, .distance 1 4, .theta 1, .distance 0 1, .distance 1 5, .distance 1 6]
    constant := ![-2, -1, 3, -2, 0]
    coefficient := ![0, 0, 1, 0, 0]
    strict := ![false, false, false, false, true] }
  origin := ![.gapLower 1 3, .corridorLower 1 4, .corridorUpper 0 1, .gapLower 1 5, .triangle 24 2]

-- Cycle fingerprint 0828610ff5e98a697371091d73d174540220c2091e773a5a384ddf1ba462a946.
def localCycle00017 : Cycle where
  length := 7
  data := {
    node := ![.theta 1, .distance 0 1, .distance 1 6, .distance 1 5, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1]
    constant := ![2, -1, 0, -2, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, true, false] }
  origin := ![.gapLower 1 6, .triangle 4 0, .triangle 24 1, .gapLower 1 3, .triangle 19 1, .triangle 15 1, .corridorLower 1 2]

-- Cycle fingerprint 086fae9efce582a1683bdcef7bd91b027f8070895e821c8c0845cf5661e5921e.
def localCycle00018 : Cycle where
  length := 6
  data := {
    node := ![.distance 4 5, .theta 4, .zero, .theta 6, .distance 1 6, .distance 1 4, .distance 4 5]
    constant := ![-1, 0, 0, 2, -2, -1]
    coefficient := ![0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, true, false, false] }
  origin := ![.corridorLower 4 5, .thetaLower 4, .thetaUpper 6, .gapUpper 6 0, .gapLower 1 4, .triangle 22 0]

-- Cycle fingerprint 0901217d3198c56f64423816dd219cc3c21dfd81216b4ef3aff566f7495510ae.
def localCycle00019 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 2 4, .distance 4 5, .distance 5 6, .distance 1 5, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, 0, -1, -1, -1, -2, -2, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false, true, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 28 0, .triangle 34 0, .triangle 24 0, .gapLower 1 3, .gapLower 1 2, .triangle 15 1, .corridorLower 1 2, .thetaLower 1]

-- Cycle fingerprint 0a0bee7146b072bfa2cf294e9fc513ae5ab31663bba07056fa4370020ee645ad.
def localCycle00020 : Cycle where
  length := 3
  data := {
    node := ![.distance 4 5, .distance 1 5, .distance 1 4, .distance 4 5]
    constant := ![0, -3, 2]
    coefficient := ![0, 0, 0]
    strict := ![false, false, true] }
  origin := ![.gapLower 5 1, .gapLower 1 3, .gapUpper 4 1]

-- Cycle fingerprint 0acc8b0362d317eae717b57c1f899f6b4a26a6f95a0d8554852dfb23fda3b57e.
def localCycle00021 : Cycle where
  length := 10
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 4 5, .distance 5 6, .distance 1 5, .distance 1 4, .theta 1, .theta 0, .zero, .theta 4]
    constant := ![3, 0, -1, -1, -1, -2, -1, 0, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, false, false, false, false, false, true, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 28 0, .triangle 34 0, .triangle 24 0, .gapLower 1 3, .corridorLower 1 4, .thetaNext 0, .thetaLower 0, .thetaUpper 4]

-- Cycle fingerprint 0b1bbb13877d7d2972ddedc830630fd2a803646fc6242eb5eccc3cdfb168b40f.
def localCycle00022 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 5, .distance 5 6, .distance 1 5, .distance 1 3, .distance 1 2, .theta 1, .distance 0 1, .distance 0 4, .distance 0 5]
    constant := ![-1, -1, 0, 0, -3, 3, 0, 0]
    coefficient := ![0, 0, 0, 0, 0, 1, 0, 0]
    strict := ![false, false, false, true, false, false, true, true] }
  origin := ![.triangle 14 0, .triangle 24 0, .gapLower 1 2, .triangle 15 1, .gapLower 1 0, .corridorUpper 0 1, .triangle 2 2, .triangle 12 2]

-- Cycle fingerprint 0b36a762c2ea95477bb23fe83b0cc16f3eed8175af8ace166ed2e47ff74c5ff1.
def localCycle00023 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 2, .theta 1, .distance 0 1, .distance 0 5, .distance 5 6, .distance 1 6, .distance 1 5, .distance 1 4, .distance 1 3, .distance 1 2]
    constant := ![-1, 2, 0, -1, 0, -2, 0, 0, 0]
    coefficient := ![0, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false, true, true] }
  origin := ![.corridorLower 1 2, .gapLower 1 6, .triangle 3 2, .triangle 14 0, .triangle 24 2, .gapLower 1 4, .gapLower 1 3, .triangle 19 1, .triangle 15 1]

-- Cycle fingerprint 0e0dfeee4cfa81d0dd53e8dcd5aa5c05dcc6ee3487d84302237c1c2c61c39a70.
def localCycle00024 : Cycle where
  length := 6
  data := {
    node := ![.distance 1 6, .distance 1 5, .distance 1 4, .distance 1 3, .theta 1, .distance 0 1, .distance 1 6]
    constant := ![0, 0, -2, -1, 2, -1]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![true, true, false, false, false, false] }
  origin := ![.triangle 24 1, .triangle 22 1, .gapLower 1 2, .corridorLower 1 3, .gapLower 1 6, .triangle 4 0]

-- Cycle fingerprint 0e26812f6a303863180cc14f21195c06c0352d63fa110b1c36bd75b1f5e41434.
def localCycle00025 : Cycle where
  length := 12
  data := {
    node := ![.theta 5, .theta 4, .distance 3 4, .distance 2 3, .distance 3 6, .distance 1 3, .distance 1 2, .theta 1, .distance 0 1, .distance 1 4, .distance 4 5, .distance 5 6, .theta 5]
    constant := ![0, 3, -1, -1, -1, 0, -1, 3, -1, -1, -1, -1]
    coefficient := ![0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0]
    strict := ![true, false, false, false, false, false, false, false, false, false, false, false] }
  origin := ![.thetaNext 4, .corridorUpper 3 4, .triangle 25 0, .triangle 27 0, .triangle 21 0, .gapLower 1 1, .corridorLower 1 2, .corridorUpper 0 1, .triangle 2 0, .triangle 22 0, .triangle 34 0, .corridorLower 5 6]

-- Cycle fingerprint 0f3d5357c57c667a9c9d7379996062fd36461bf1c5c2082b2e4ea250418198e8.
def localCycle00026 : Cycle where
  length := 13
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 5 6, .distance 3 6, .distance 2 6, .distance 1 6, .distance 0 1, .distance 1 2, .distance 2 5, .distance 2 3, .distance 3 4, .theta 3, .zero]
    constant := ![0, 3, -1, 0, 0, 0, -1, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, true, false, false, false, true, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 34 0, .triangle 33 2, .triangle 27 2, .triangle 18 2, .triangle 4 0, .triangle 0 0, .triangle 17 0, .triangle 26 1, .triangle 25 0, .corridorLower 3 4, .thetaLower 3]

-- Cycle fingerprint 0ff1fcbadcd05b5087ee7fb0df9029157acd6763d83d81cff45a4aedbb91006e.
def localCycle00027 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 6, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1, .zero, .theta 6, .distance 1 6]
    constant := ![-2, 0, 0, -2, 0, 0, 2]
    coefficient := ![0, 0, 0, 0, 0, 1, 0]
    strict := ![false, true, true, false, false, false, true] }
  origin := ![.gapLower 1 4, .triangle 19 1, .triangle 15 1, .gapLower 1 0, .thetaLower 1, .thetaUpper 6, .gapUpper 6 0]

-- Cycle fingerprint 10c7320e4c3e3129127a3fbc0465f3805f3feabfa7a0e7c18d752392af6dd801.
def localCycle00028 : Cycle where
  length := 10
  data := {
    node := ![.theta 4, .distance 3 4, .distance 3 5, .distance 5 6, .distance 4 5, .distance 1 4, .distance 1 3, .theta 1, .theta 0, .zero, .theta 4]
    constant := ![3, 0, -1, -1, -1, -2, -1, 0, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, false, false, false, false, false, true, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 31 2, .triangle 33 0, .triangle 34 0, .triangle 22 0, .gapLower 1 2, .corridorLower 1 3, .thetaNext 0, .thetaLower 0, .thetaUpper 4]

-- Cycle fingerprint 10c92406e05f0d3d5862da82cd74ae987efdd53da7d5b8ab88fc3b05add81910.
def localCycle00029 : Cycle where
  length := 8
  data := {
    node := ![.distance 4 5, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1, .distance 0 1, .distance 0 6, .distance 0 4, .distance 4 5]
    constant := ![-1, 0, 0, -2, 2, 0, 0, -1]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![false, false, true, false, false, true, true, false] }
  origin := ![.triangle 22 0, .gapLower 1 2, .triangle 15 1, .gapLower 1 0, .gapLower 1 6, .triangle 4 2, .triangle 13 1, .triangle 12 0]

-- Cycle fingerprint 10ee33bdce84d389205361984001b82cdc04097b97847f513349c9ba7368315e.
def localCycle00030 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 3 5, .distance 5 6, .distance 4 5, .distance 2 4, .distance 2 3, .distance 0 2, .distance 1 2, .theta 1, .theta 0, .zero]
    constant := ![0, 3, 0, -1, -1, -1, 0, -1, 0, -1, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, true, false, true, false, true, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 31 2, .triangle 33 0, .triangle 34 0, .triangle 28 0, .triangle 25 1, .triangle 5 0, .triangle 0 1, .corridorLower 1 2, .thetaNext 0, .thetaLower 0]

-- Cycle fingerprint 11ca1fb6bcbf6abd76d1466af0c5c4b3fc6d0a070144129d4fcab13ffe3a7371.
def localCycle00031 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 3, .distance 1 2, .theta 1, .distance 0 1, .distance 1 4, .distance 1 6, .distance 1 5, .distance 1 3]
    constant := ![-2, -1, 3, -1, 0, 0, -2]
    coefficient := ![0, 0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, false] }
  origin := ![.gapLower 1 1, .corridorLower 1 2, .corridorUpper 0 1, .triangle 2 0, .triangle 23 2, .triangle 24 1, .gapLower 1 2]

-- Cycle fingerprint 11f8f91107aca6832d33208252a4f018e7c9ba2f95f020963e6477b122994019.
def localCycle00032 : Cycle where
  length := 3
  data := {
    node := ![.distance 4 6, .distance 1 6, .distance 1 4, .distance 4 6]
    constant := ![0, -3, 2]
    coefficient := ![0, 0, 0]
    strict := ![false, false, true] }
  origin := ![.gapLower 6 2, .gapLower 1 3, .gapUpper 4 1]

-- Cycle fingerprint 12e767f2540fa38c7767e89d43e08510f1d0615d0e17a277d80b35d876fb2f17.
def localCycle00033 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 4 6, .distance 1 6, .distance 1 5, .distance 1 4, .distance 1 3, .theta 1, .distance 0 1]
    constant := ![0, -1, 0, 0, -2, -2, -1, 4]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![true, false, true, true, false, false, false, false] }
  origin := ![.triangle 2 2, .triangle 13 0, .triangle 23 2, .triangle 24 1, .gapLower 1 3, .gapLower 1 2, .corridorLower 1 3, .gapLower 1 6]

-- Cycle fingerprint 137c6f3c9da073b91f2772dd3451f20f56e6dc65b3fb44569210d2ae5639f069.
def localCycle00034 : Cycle where
  length := 11
  data := {
    node := ![.distance 5 6, .distance 4 5, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1, .zero, .theta 4, .distance 3 4, .distance 2 4, .distance 2 5, .distance 5 6]
    constant := ![-1, -1, 0, -2, -1, 0, 0, 3, 0, 0, -1]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false, true, true, false] }
  origin := ![.triangle 34 0, .triangle 22 0, .gapLower 1 2, .gapLower 1 1, .corridorLower 1 2, .thetaLower 1, .thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 28 2, .triangle 30 0]

-- Cycle fingerprint 13cfc6c1ef424113de01fe3ff46d62830c7d355135bb0e8a33f566d58001e819.
def localCycle00035 : Cycle where
  length := 3
  data := {
    node := ![.theta 1, .distance 0 1, .distance 1 6, .theta 1]
    constant := ![3, -3, -1]
    coefficient := ![1, 0, 0]
    strict := ![false, false, false] }
  origin := ![.corridorUpper 0 1, .gapLower 1 5, .corridorLower 1 6]

-- Cycle fingerprint 1424df68603d978fd39b1fcf2c8f2a1a7bfcd214641e06be01de1d9b4fcc49db.
def localCycle00036 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 5, .distance 1 5, .distance 1 4, .theta 4, .distance 3 4, .distance 2 4, .distance 2 5, .distance 5 6, .distance 4 5, .distance 0 5]
    constant := ![0, -3, 0, 3, 0, 0, -1, -1, 0]
    coefficient := ![0, 0, 0, 1, 0, 0, 0, 0, 0]
    strict := ![true, false, false, false, true, true, false, false, false] }
  origin := ![.triangle 3 1, .gapLower 1 3, .gapLower 4 0, .corridorUpper 3 4, .triangle 25 2, .triangle 28 2, .triangle 30 0, .triangle 34 0, .gapLower 5 2]

-- Cycle fingerprint 1507574cf625adb871faa7326dd78eb5b9419adcc9f22d1a96f6173ac35fb53f.
def localCycle00037 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 6, .distance 1 6, .distance 1 4, .distance 1 5, .distance 1 3, .distance 1 2, .theta 1, .zero]
    constant := ![0, 2, 0, 0, -3, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, true, false, false] }
  origin := ![.thetaUpper 6, .gapUpper 6 0, .triangle 23 1, .triangle 22 2, .gapLower 1 2, .triangle 15 1, .corridorLower 1 2, .thetaLower 1]

-- Cycle fingerprint 16a128c9bdd81f0fd1382acc8bc919878a71328fcb4c69fe893b1087053c5903.
def localCycle00038 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 4, .distance 1 6, .distance 1 5, .distance 1 3, .distance 1 2, .theta 1, .distance 0 1]
    constant := ![-2, 0, 0, 0, -2, -1, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, true, false, false, false, false] }
  origin := ![.gapLower 1 5, .triangle 23 2, .triangle 24 1, .gapLower 1 2, .gapLower 1 1, .corridorLower 1 2, .corridorUpper 0 1]

-- Cycle fingerprint 16cbf8a76d02fe1937746a483ea787cd2ac8b16b28a549d5c3bb603c583e2157.
def localCycle00039 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 3, .theta 1, .zero, .theta 4, .distance 3 4, .distance 4 5, .distance 5 6, .distance 1 5, .distance 1 4, .distance 1 3]
    constant := ![-1, 0, 0, 3, -1, -1, -1, 0, -2]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, true, false] }
  origin := ![.corridorLower 1 3, .thetaLower 1, .thetaUpper 4, .corridorUpper 3 4, .triangle 31 0, .triangle 34 0, .triangle 24 0, .triangle 22 1, .gapLower 1 2]

-- Cycle fingerprint 16e9a7044a17c268384bc44d854ae1732eb16338f27a22d899241105dcca9c44.
def localCycle00040 : Cycle where
  length := 6
  data := {
    node := ![.theta 1, .distance 0 1, .distance 1 5, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1]
    constant := ![3, -1, 0, 0, -2, -2]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false] }
  origin := ![.corridorUpper 0 1, .triangle 3 0, .triangle 22 1, .triangle 19 1, .gapLower 1 1, .gapLower 1 0]

-- Cycle fingerprint 178e06d6e799d9b912e6ab55343599f7588973bd0523a16da8452428970ecddd.
def localCycle00041 : Cycle where
  length := 10
  data := {
    node := ![.distance 5 6, .distance 4 6, .distance 0 4, .distance 4 5, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1, .zero, .theta 6, .distance 5 6]
    constant := ![0, -1, -1, -1, 0, -2, -1, 0, 0, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 1, 1]
    strict := ![true, false, false, false, false, false, false, false, false, false] }
  origin := ![.triangle 34 2, .triangle 13 0, .triangle 12 0, .triangle 22 0, .gapLower 1 2, .gapLower 1 1, .corridorLower 1 2, .thetaLower 1, .thetaUpper 6, .corridorUpper 5 6]

-- Cycle fingerprint 179a23178912cf1459ee19d36a1b2aea640ec110c0ca68f480372d6b5b24861e.
def localCycle00042 : Cycle where
  length := 5
  data := {
    node := ![.distance 1 6, .distance 1 5, .theta 1, .distance 0 1, .distance 1 4, .distance 1 6]
    constant := ![-2, -1, 3, -2, 0]
    coefficient := ![0, 0, 1, 0, 0]
    strict := ![false, false, false, false, true] }
  origin := ![.gapLower 1 3, .corridorLower 1 5, .corridorUpper 0 1, .gapLower 1 5, .triangle 23 2]

-- Cycle fingerprint 195be1b48aa6290b889b664d65a2459be4f142f6536b3f7ef7e12d0a8923af58.
def localCycle00043 : Cycle where
  length := 4
  data := {
    node := ![.distance 0 1, .distance 1 6, .distance 1 5, .theta 1, .distance 0 1]
    constant := ![-2, -2, -1, 3]
    coefficient := ![0, 0, 0, 1]
    strict := ![false, false, false, false] }
  origin := ![.gapLower 1 5, .gapLower 1 4, .corridorLower 1 5, .corridorUpper 0 1]

-- Cycle fingerprint 1968ecb24ee1f5f8afc477f598b6c81b965ef3f6ebc63abd0be1c4ea149e66ad.
def localCycle00044 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 2, .theta 1, .zero, .theta 4, .distance 3 4, .distance 2 4, .distance 4 6, .distance 4 5, .distance 1 4, .distance 1 3, .distance 1 2]
    constant := ![-2, 0, 0, 3, 0, -1, 0, -1, -2, 0]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, true, false, false, true] }
  origin := ![.gapLower 1 0, .thetaLower 1, .thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 29 0, .triangle 34 1, .triangle 22 0, .gapLower 1 2, .triangle 15 1]

-- Cycle fingerprint 196e89634f0b909815a13395fa68b1b4bce2142a26687711baf70d7b4409d98f.
def localCycle00045 : Cycle where
  length := 7
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 6, .distance 0 4, .distance 4 5, .distance 1 4, .distance 1 3, .theta 1]
    constant := ![1, 0, 0, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, false, false] }
  origin := ![.gapLower 1 6, .triangle 4 2, .triangle 13 1, .triangle 12 0, .triangle 22 0, .gapLower 1 2, .corridorLower 1 3]

-- Cycle fingerprint 19ab206d08cf1c9370b0874bcec7b14705a08d19d34b1255902ddc7c43821c4b.
def localCycle00046 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 2, .theta 1, .zero, .theta 5, .distance 4 5, .distance 3 4, .distance 2 3, .distance 1 2]
    constant := ![-3, 0, 0, 3, -1, -1, -1]
    coefficient := ![0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 1 0, .thetaLower 1, .thetaUpper 5, .corridorUpper 4 5, .triangle 31 0, .triangle 25 0, .triangle 15 0]

-- Cycle fingerprint 1b219c3de0d691d7d7b43f3f2517c023d68dce81f6f40394c3f243e2a8cedbaa.
def localCycle00047 : Cycle where
  length := 6
  data := {
    node := ![.distance 1 6, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1, .distance 0 1, .distance 1 6]
    constant := ![0, 0, -2, -1, 2, -1]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![true, true, false, false, false, false] }
  origin := ![.triangle 23 1, .triangle 19 1, .gapLower 1 1, .corridorLower 1 2, .gapLower 1 6, .triangle 4 0]

-- Cycle fingerprint 1b4315f4a9f6d6f352fca5fa0cdb1e1462af6701c7d2249cd744a9226bb96d95.
def localCycle00048 : Cycle where
  length := 5
  data := {
    node := ![.distance 1 4, .distance 1 5, .theta 1, .distance 0 1, .distance 1 6, .distance 1 4]
    constant := ![-2, -1, 3, -2, 0]
    coefficient := ![0, 0, 1, 0, 0]
    strict := ![false, false, false, false, true] }
  origin := ![.gapLower 1 3, .corridorLower 1 5, .corridorUpper 0 1, .gapLower 1 5, .triangle 23 1]

-- Cycle fingerprint 1bd023635034b6546b6d2f007af687d7aced96001ace1132edbcaae27c197f0b.
def localCycle00049 : Cycle where
  length := 12
  data := {
    node := ![.distance 1 5, .distance 1 4, .distance 1 2, .theta 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 2 4, .distance 4 5, .distance 0 5, .distance 5 6, .distance 1 5]
    constant := ![0, 0, -2, 0, 0, 0, 3, 0, -1, 0, -1, -1]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, false, true, false, true, false, false] }
  origin := ![.gapLower 1 3, .triangle 16 1, .gapLower 1 0, .thetaNext 0, .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 28 0, .triangle 12 2, .triangle 14 0, .triangle 24 0]

-- Cycle fingerprint 1c38d59da718b4a31083185ddbf88f2a822221dc38b574d3d1004670808a0976.
def localCycle00050 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 4, .distance 1 3, .distance 1 2, .theta 1, .distance 0 1, .distance 0 4, .distance 4 5, .distance 1 4]
    constant := ![-3, 0, -1, 3, 0, -1, -1]
    coefficient := ![0, 0, 0, 1, 0, 0, 0]
    strict := ![false, true, false, false, true, false, false] }
  origin := ![.gapLower 1 2, .triangle 15 1, .corridorLower 1 2, .corridorUpper 0 1, .triangle 2 2, .triangle 12 0, .triangle 22 0]

-- Cycle fingerprint 1c6818e100a2efe82b88f41ce0b9ae6ad67c2532e433035edef1b0b3cb144d4d.
def localCycle00051 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 0 5, .distance 5 6, .distance 1 5, .distance 1 3, .distance 1 2, .theta 1, .distance 0 1]
    constant := ![0, 0, -1, -1, -2, -2, -1, 4]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![true, true, false, false, false, false, false, false] }
  origin := ![.triangle 2 2, .triangle 12 2, .triangle 14 0, .triangle 24 0, .gapLower 1 2, .gapLower 1 1, .corridorLower 1 2, .gapLower 1 6]

-- Cycle fingerprint 1ccd9a0ba815cf2714d88025b3b62c6affac4dbdf44cc5b0a5febf9689d7ce49.
def localCycle00052 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 5, .distance 5 6, .distance 1 5, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1, .distance 0 1]
    constant := ![0, -1, -1, 0, -2, 0, -2, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![true, false, false, false, false, true, false, false] }
  origin := ![.triangle 3 2, .triangle 14 0, .triangle 24 0, .gapLower 1 3, .gapLower 1 2, .triangle 15 1, .gapLower 1 0, .corridorUpper 0 1]

-- Cycle fingerprint 1e821c515b758adf9a2f25a55398d72d0afc3a4b1832e0b8c743d4434002da72.
def localCycle00053 : Cycle where
  length := 8
  data := {
    node := ![.distance 3 4, .distance 4 5, .distance 5 6, .distance 0 6, .distance 1 6, .distance 1 5, .distance 1 4, .theta 4, .distance 3 4]
    constant := ![-1, -1, 0, 0, -3, 0, 0, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![false, false, false, true, false, true, false, false] }
  origin := ![.triangle 31 0, .triangle 34 0, .gapLower 6 2, .triangle 4 1, .gapLower 1 4, .triangle 22 1, .gapLower 4 0, .corridorUpper 3 4]

-- Cycle fingerprint 1eaad0c2d768dd30ac0a3195420a27892b487c002ebf11e6b42b3c59182f1b07.
def localCycle00054 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 4 5, .distance 0 4, .distance 4 6, .distance 5 6, .theta 5, .theta 4]
    constant := ![3, 0, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, true, false, true] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 28 0, .triangle 12 0, .triangle 13 0, .triangle 34 1, .corridorLower 5 6, .thetaNext 4]

-- Cycle fingerprint 1f44573aa32a8dea428162ff58be8e2a1b9dc99cef20f32d8d4fab060fa775ac.
def localCycle00055 : Cycle where
  length := 8
  data := {
    node := ![.theta 1, .zero, .theta 6, .distance 1 6, .distance 1 5, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1]
    constant := ![0, 0, 2, 0, -2, 0, -2, -1]
    coefficient := ![0, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, true, false, false] }
  origin := ![.thetaLower 1, .thetaUpper 6, .gapUpper 6 0, .triangle 24 1, .gapLower 1 3, .triangle 19 1, .gapLower 1 1, .corridorLower 1 2]

-- Cycle fingerprint 1fb5d2e091078dd56f40a1ce8b079473587c9a6c7fc68f51cf39e4ffdde9d37a.
def localCycle00056 : Cycle where
  length := 14
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 2 6, .distance 1 6, .distance 0 1, .distance 1 2, .distance 2 5, .distance 2 3, .distance 3 4, .theta 3, .theta 2, .zero]
    constant := ![0, 3, 0, 0, 0, 0, -1, -1, -1, 0, -1, -1, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, true, true, false, false, false, true, false, false, true, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 27 2, .triangle 18 2, .triangle 4 0, .triangle 0 0, .triangle 17 0, .triangle 26 1, .triangle 25 0, .corridorLower 3 4, .thetaNext 2, .thetaLower 2]

-- Cycle fingerprint 22989cd31e1b4b98987ac1c897f1a68648604908ec6c079cc3a3309fff8be402.
def localCycle00057 : Cycle where
  length := 6
  data := {
    node := ![.distance 1 2, .theta 1, .distance 0 1, .distance 1 5, .distance 1 4, .distance 1 3, .distance 1 2]
    constant := ![-1, 3, -1, 0, -3, 0]
    coefficient := ![0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true] }
  origin := ![.corridorLower 1 2, .corridorUpper 0 1, .triangle 3 0, .triangle 22 1, .gapLower 1 2, .triangle 15 1]

-- Cycle fingerprint 22b93a04d6bcf616afd154483b9cb8e5d63c4e6e41ca9c309da04439f5402cd9.
def localCycle00058 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 4 6, .distance 4 5, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1, .distance 0 1]
    constant := ![0, -1, 0, -1, -2, 0, -2, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![true, false, true, false, false, true, false, false] }
  origin := ![.triangle 2 2, .triangle 13 0, .triangle 34 1, .triangle 22 0, .gapLower 1 2, .triangle 15 1, .gapLower 1 0, .corridorUpper 0 1]

-- Cycle fingerprint 23296c87f1613e5736ece29e36513eeb69431af9b56fa59e8e7aeac097c7a9d0.
def localCycle00059 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 5, .distance 5 6, .distance 1 5, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1, .distance 0 1, .distance 0 5]
    constant := ![-1, -1, 0, 0, -2, -2, 3, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 0]
    strict := ![false, false, false, true, false, false, false, true] }
  origin := ![.triangle 14 0, .triangle 24 0, .gapLower 1 3, .triangle 19 1, .gapLower 1 1, .gapLower 1 0, .corridorUpper 0 1, .triangle 3 2]

-- Cycle fingerprint 235f430e7594acb9eb48e502d0c4b7836e507f8f7c9385194ceafddb80b0f047.
def localCycle00060 : Cycle where
  length := 9
  data := {
    node := ![.distance 4 5, .distance 1 4, .distance 1 3, .theta 1, .zero, .theta 4, .distance 3 4, .distance 3 5, .distance 5 6, .distance 4 5]
    constant := ![-1, -3, -1, 0, 0, 3, 0, -1, -1]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, false, false] }
  origin := ![.triangle 22 0, .gapLower 1 2, .corridorLower 1 3, .thetaLower 1, .thetaUpper 4, .corridorUpper 3 4, .triangle 31 2, .triangle 33 0, .triangle 34 0]

-- Cycle fingerprint 23bc5ab5326a0c6945e73a69e38cb5fa4b992481271ad0e0bf262fcdc20d46a7.
def localCycle00061 : Cycle where
  length := 9
  data := {
    node := ![.theta 1, .distance 0 1, .distance 1 5, .distance 5 6, .theta 5, .distance 4 5, .distance 3 4, .distance 2 3, .distance 1 2, .theta 1]
    constant := ![3, -3, -1, -1, 3, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false, false] }
  origin := ![.corridorUpper 0 1, .gapLower 1 5, .triangle 24 0, .corridorLower 5 6, .corridorUpper 4 5, .triangle 31 0, .triangle 25 0, .triangle 15 0, .corridorLower 1 2]

-- Cycle fingerprint 23e55a5b68b41d16c50ce74166babf6bb5885e57fc52f1eb188f45e8ae957c65.
def localCycle00062 : Cycle where
  length := 4
  data := {
    node := ![.distance 0 1, .distance 1 5, .distance 1 2, .theta 1, .distance 0 1]
    constant := ![-2, 0, -2, 3]
    coefficient := ![0, 0, 0, 1]
    strict := ![false, true, false, false] }
  origin := ![.gapLower 1 5, .triangle 17 1, .gapLower 1 0, .corridorUpper 0 1]

-- Cycle fingerprint 2526a229cf707470781d74d48e39d0da716fd5c5c1629759077cf3faf07fc412.
def localCycle00063 : Cycle where
  length := 3
  data := {
    node := ![.theta 1, .distance 0 1, .distance 1 5, .theta 1]
    constant := ![3, -3, -1]
    coefficient := ![1, 0, 0]
    strict := ![false, false, false] }
  origin := ![.corridorUpper 0 1, .gapLower 1 5, .corridorLower 1 5]

-- Cycle fingerprint 2532fd1b29839657493e3218245f6ec48974e3cff81bf60f10fe8a3b7f1663d4.
def localCycle00064 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 5, .distance 1 4, .theta 1, .distance 0 1, .distance 0 4, .distance 4 5, .distance 5 6, .distance 1 5]
    constant := ![0, -1, 3, 0, -1, -1, -1]
    coefficient := ![0, 0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false] }
  origin := ![.gapLower 1 3, .corridorLower 1 4, .corridorUpper 0 1, .triangle 2 2, .triangle 12 0, .triangle 34 0, .triangle 24 0]

-- Cycle fingerprint 264e47301366559ddde99e2f4709999261c2bc2e4ebaa32986631e7c8755db6e.
def localCycle00065 : Cycle where
  length := 10
  data := {
    node := ![.distance 3 4, .distance 3 5, .distance 5 6, .distance 4 5, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1, .zero, .theta 4, .distance 3 4]
    constant := ![0, -1, -1, -1, 0, -2, -1, 0, 0, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 1, 1]
    strict := ![true, false, false, false, false, false, false, false, false, false] }
  origin := ![.triangle 31 2, .triangle 33 0, .triangle 34 0, .triangle 22 0, .gapLower 1 2, .gapLower 1 1, .corridorLower 1 2, .thetaLower 1, .thetaUpper 4, .corridorUpper 3 4]

-- Cycle fingerprint 265286f33e94e8d1084daa31fa5ef40991ba6de8e52eaf39d9d82c3f7e0f2190.
def localCycle00066 : Cycle where
  length := 8
  data := {
    node := ![.distance 1 4, .distance 1 3, .distance 1 2, .theta 1, .distance 0 1, .distance 0 5, .distance 5 6, .distance 1 5, .distance 1 4]
    constant := ![0, 0, -1, 3, 0, -1, -1, -2]
    coefficient := ![0, 0, 0, 1, 0, 0, 0, 0]
    strict := ![true, true, false, false, true, false, false, false] }
  origin := ![.triangle 19 1, .triangle 15 1, .corridorLower 1 2, .corridorUpper 0 1, .triangle 3 2, .triangle 14 0, .triangle 24 0, .gapLower 1 3]

-- Cycle fingerprint 275f0f2eb2a867dd4a591ef2ce5f59fff2a5c6f62a2173bcf4c874aba91fef50.
def localCycle00067 : Cycle where
  length := 8
  data := {
    node := ![.distance 4 5, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1, .distance 0 1, .distance 0 4, .distance 4 6, .distance 4 5]
    constant := ![-1, -2, 0, -1, 2, 0, -1, 0]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![false, false, true, false, false, true, false, true] }
  origin := ![.triangle 22 0, .gapLower 1 2, .triangle 15 1, .corridorLower 1 2, .gapLower 1 6, .triangle 2 2, .triangle 13 0, .triangle 34 1]

-- Cycle fingerprint 27846db695dc0bf5519279349c6c104c5dbbc8735f8d6771f390971f4d97aa37.
def localCycle00068 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 2, .theta 1, .distance 0 1, .distance 0 4, .distance 0 5, .distance 5 6, .distance 1 6, .distance 1 5, .distance 1 3, .distance 1 2]
    constant := ![-1, 2, 0, 0, -1, 0, -2, 0, 0]
    coefficient := ![0, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, true, false, false, true] }
  origin := ![.corridorLower 1 2, .gapLower 1 6, .triangle 2 2, .triangle 12 2, .triangle 14 0, .triangle 24 2, .gapLower 1 3, .gapLower 1 2, .triangle 15 1]

-- Cycle fingerprint 28ac6a5a3c92c47169eb0a76931f35bfcfc8e38f42a542807238934ed6b89292.
def localCycle00069 : Cycle where
  length := 9
  data := {
    node := ![.distance 4 5, .distance 1 4, .distance 1 3, .theta 1, .zero, .theta 4, .distance 3 4, .distance 2 4, .distance 4 6, .distance 4 5]
    constant := ![-1, -3, -1, 0, 0, 3, 0, -1, 0]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, false, true] }
  origin := ![.triangle 22 0, .gapLower 1 2, .corridorLower 1 3, .thetaLower 1, .thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 29 0, .triangle 34 1]

-- Cycle fingerprint 293774f7563ac226b31d0b5317db194a3d3db9f28cf2429566469f25f7435b94.
def localCycle00070 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 5, .distance 1 4, .theta 4, .distance 3 4, .distance 2 4, .distance 4 5, .distance 5 6, .distance 1 5]
    constant := ![-3, 0, 3, 0, -1, -1, -1]
    coefficient := ![0, 0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false] }
  origin := ![.gapLower 1 3, .gapLower 4 0, .corridorUpper 3 4, .triangle 25 2, .triangle 28 0, .triangle 34 0, .triangle 24 0]

-- Cycle fingerprint 29ace2b2287ba0c078048717a60b5b1d18bb5717861751cb901302848705daa2.
def localCycle00071 : Cycle where
  length := 11
  data := {
    node := ![.distance 1 3, .distance 1 2, .theta 1, .zero, .theta 4, .distance 3 4, .distance 2 4, .distance 2 5, .distance 5 6, .distance 4 5, .distance 1 4, .distance 1 3]
    constant := ![0, -2, 0, 0, 3, 0, 0, -1, -1, -1, 0]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![true, false, false, false, false, true, true, false, false, false, false] }
  origin := ![.triangle 15 1, .gapLower 1 0, .thetaLower 1, .thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 28 2, .triangle 30 0, .triangle 34 0, .triangle 22 0, .gapLower 1 2]

-- Cycle fingerprint 29b464c44cc99ed840560af69e32727584e95e268246dc60502e3bf69daa4715.
def localCycle00072 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 0 3, .distance 0 4, .distance 4 5, .distance 3 5, .distance 2 3, .distance 3 4, .theta 3, .zero]
    constant := ![0, 3, 0, 0, -1, 0, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, true, false, true, false, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 11 0, .triangle 9 2, .triangle 12 0, .triangle 31 2, .triangle 26 0, .triangle 25 0, .corridorLower 3 4, .thetaLower 3]

-- Cycle fingerprint 2a37af1dfd2fb9da94e6bffcb59511bda4def4be29ac95b97409ea96ad8d30f0.
def localCycle00073 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 4 6, .distance 0 4, .distance 1 4, .distance 4 5, .theta 4]
    constant := ![3, 0, -1, -1, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 29 0, .triangle 13 0, .triangle 2 1, .triangle 22 0, .corridorLower 4 5]

-- Cycle fingerprint 2e3982b548ef7f7934643d13045c9d582adee9244be3860fc3f1bd88deace285.
def localCycle00074 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 4, .distance 1 5, .distance 1 3, .theta 1, .zero, .theta 6, .distance 1 6, .distance 1 4]
    constant := ![-2, -2, -1, 0, 0, 2, 0]
    coefficient := ![0, 0, 0, 0, 1, 0, 0]
    strict := ![false, false, false, false, false, true, true] }
  origin := ![.gapLower 1 3, .gapLower 1 2, .corridorLower 1 3, .thetaLower 1, .thetaUpper 6, .gapUpper 6 0, .triangle 23 1]

-- Cycle fingerprint 2e5a7e1ac3db6a1317b9155f0906b86c04d4d9b85e58b2008df6876c7c057135.
def localCycle00075 : Cycle where
  length := 8
  data := {
    node := ![.distance 1 2, .theta 1, .zero, .theta 6, .distance 1 6, .distance 1 5, .distance 1 4, .distance 1 3, .distance 1 2]
    constant := ![-2, 0, 0, 2, -2, 0, 0, 0]
    coefficient := ![0, 0, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true, true, true] }
  origin := ![.gapLower 1 0, .thetaLower 1, .thetaUpper 6, .gapUpper 6 0, .gapLower 1 4, .triangle 22 1, .triangle 19 1, .triangle 15 1]

-- Cycle fingerprint 2ef4d6ba371fb6ae11ef9ec23931b48774bbd45bda7d7ab176cdc604e0df6119.
def localCycle00076 : Cycle where
  length := 14
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 2 6, .distance 1 6, .distance 0 1, .distance 1 2, .distance 1 3, .distance 1 4, .distance 4 5, .distance 2 4, .theta 2, .zero]
    constant := ![0, 3, 0, 0, 0, 0, -1, -1, 0, 0, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, true, true, false, false, true, true, false, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 27 2, .triangle 18 2, .triangle 4 0, .triangle 0 0, .triangle 15 2, .triangle 19 2, .triangle 22 0, .triangle 28 0, .corridorLower 2 4, .thetaLower 2]

-- Cycle fingerprint 2ef9b1d04c4770dbafec947d49c76e6d463221a7463615b7c3b1f60d45a0a891.
def localCycle00077 : Cycle where
  length := 5
  data := {
    node := ![.theta 1, .distance 0 1, .distance 1 5, .distance 1 6, .distance 1 4, .theta 1]
    constant := ![3, -1, 0, -3, -1]
    coefficient := ![1, 0, 0, 0, 0]
    strict := ![false, false, true, false, false] }
  origin := ![.corridorUpper 0 1, .triangle 3 0, .triangle 24 2, .gapLower 1 3, .corridorLower 1 4]

-- Cycle fingerprint 2f1124a54bf45740fbeea5cac3addeefc3ea21d5c9d18f7aa99bd89b7645a019.
def localCycle00078 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 3 4, .distance 4 5, .distance 0 4, .distance 4 6, .distance 5 6, .theta 5, .theta 4]
    constant := ![3, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, true] }
  origin := ![.corridorUpper 3 4, .triangle 31 0, .triangle 12 0, .triangle 13 0, .triangle 34 1, .corridorLower 5 6, .thetaNext 4]

-- Cycle fingerprint 2fcfcc87cce986f59eed78d4e7032540685e1645c590bff0bfba401fb907cbfc.
def localCycle00079 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 3 4, .distance 3 5, .distance 5 6, .distance 4 6, .distance 2 4, .distance 4 5, .theta 4]
    constant := ![3, 0, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 31 2, .triangle 33 0, .triangle 34 2, .triangle 29 0, .triangle 28 0, .corridorLower 4 5]

-- Cycle fingerprint 2fed0393e78f96c84544a71e9dbb5a9b7587dfe8a1769682af8d762a77eda1ba.
def localCycle00080 : Cycle where
  length := 13
  data := {
    node := ![.distance 1 2, .theta 1, .distance 0 1, .distance 1 5, .distance 5 6, .theta 5, .theta 4, .distance 3 4, .distance 2 4, .distance 4 5, .distance 4 6, .distance 1 4, .distance 1 3, .distance 1 2]
    constant := ![-1, 3, -3, -1, -1, 0, 3, 0, -1, 0, -1, 0, 0]
    coefficient := ![0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, true, false, true, false, false, true] }
  origin := ![.corridorLower 1 2, .corridorUpper 0 1, .gapLower 1 5, .triangle 24 0, .corridorLower 5 6, .thetaNext 4, .corridorUpper 3 4, .triangle 25 2, .triangle 28 0, .triangle 34 2, .triangle 23 0, .gapLower 1 2, .triangle 15 1]

-- Cycle fingerprint 303f639aaa116bcd5e0b2afa3b5ca53b35602e6b82b3da39e906d55480079ee3.
def localCycle00081 : Cycle where
  length := 8
  data := {
    node := ![.distance 1 5, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1, .distance 0 1, .distance 0 5, .distance 5 6, .distance 1 5]
    constant := ![0, 0, 0, -1, 1, 0, -1, -1]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![false, true, true, false, false, true, false, false] }
  origin := ![.gapLower 1 3, .triangle 19 1, .triangle 15 1, .corridorLower 1 2, .gapLower 1 6, .triangle 3 2, .triangle 14 0, .triangle 24 0]

-- Cycle fingerprint 310776a7341351b263bc27384eb5960ce272cd248f2d67478f9a21c064f1f84e.
def localCycle00082 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 4 5, .distance 0 4, .distance 4 6, .distance 1 4, .theta 4]
    constant := ![3, 0, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 28 0, .triangle 12 0, .triangle 13 0, .triangle 23 0, .gapLower 4 0]

-- Cycle fingerprint 31fb9e3542a7931ef5521b2453fe336a30fd4c8c390eb4b22cca04d102e0d044.
def localCycle00083 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 4, .distance 2 3, .distance 3 6, .distance 4 6, .distance 5 6, .distance 0 5, .theta 0, .zero]
    constant := ![0, 3, -1, -1, -1, 0, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 0, .triangle 25 0, .triangle 27 0, .triangle 32 1, .triangle 34 1, .triangle 14 0, .corridorLower 0 5, .thetaLower 0]

-- Cycle fingerprint 324c61adc1c903635ae9d0a82c66207120121939fa76b145e7ef2972f5b2f180.
def localCycle00084 : Cycle where
  length := 8
  data := {
    node := ![.distance 1 2, .theta 1, .zero, .theta 6, .distance 1 6, .distance 1 5, .distance 1 4, .distance 1 3, .distance 1 2]
    constant := ![-1, 0, 0, 2, -3, 0, 0, 0]
    coefficient := ![0, 0, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true, true, true] }
  origin := ![.corridorLower 1 2, .thetaLower 1, .thetaUpper 6, .gapUpper 6 0, .gapLower 1 4, .triangle 22 1, .triangle 19 1, .triangle 15 1]

-- Cycle fingerprint 32986ea872f4f6ffb473ec1a870de0ed9612f54bc29d196bf2d13ac824446cc5.
def localCycle00085 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 3, .distance 1 2, .theta 1, .distance 0 1, .distance 0 4, .distance 4 5, .distance 1 4, .distance 1 3]
    constant := ![-2, -2, 3, 0, -1, -1, 0]
    coefficient := ![0, 0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false] }
  origin := ![.gapLower 1 1, .gapLower 1 0, .corridorUpper 0 1, .triangle 2 2, .triangle 12 0, .triangle 22 0, .gapLower 1 2]

-- Cycle fingerprint 338d23e6e9740c4d4c84973a1075bc555c6c392ba957cc391254fd6aaffd9928.
def localCycle00086 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 5, .distance 1 3, .distance 1 2, .theta 1, .distance 0 1, .distance 1 4, .distance 1 6, .distance 1 5]
    constant := ![-2, 0, -2, 3, -1, 0, 0]
    coefficient := ![0, 0, 0, 1, 0, 0, 0]
    strict := ![false, true, false, false, false, true, true] }
  origin := ![.gapLower 1 2, .triangle 15 1, .gapLower 1 0, .corridorUpper 0 1, .triangle 2 0, .triangle 23 2, .triangle 24 1]

-- Cycle fingerprint 34dca43ad63e96983599d899d4d34161514ae3820241bb76487304ad700e73e8.
def localCycle00087 : Cycle where
  length := 8
  data := {
    node := ![.distance 1 5, .distance 1 3, .distance 1 2, .theta 1, .distance 0 1, .distance 0 4, .distance 0 5, .distance 5 6, .distance 1 5]
    constant := ![0, 0, -2, 3, 0, 0, -1, -1]
    coefficient := ![0, 0, 0, 1, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, true, false, false] }
  origin := ![.gapLower 1 2, .triangle 15 1, .gapLower 1 0, .corridorUpper 0 1, .triangle 2 2, .triangle 12 2, .triangle 14 0, .triangle 24 0]

-- Cycle fingerprint 355741cb5d23afd546d805f0b8a47c9a7d1aeee343c2a42698388788c0bb4ef1.
def localCycle00088 : Cycle where
  length := 5
  data := {
    node := ![.distance 1 5, .distance 1 6, .distance 1 4, .theta 1, .distance 0 1, .distance 1 5]
    constant := ![0, -2, -1, 2, -1]
    coefficient := ![0, 0, 0, 1, 0]
    strict := ![true, false, false, false, false] }
  origin := ![.triangle 24 2, .gapLower 1 3, .corridorLower 1 4, .gapLower 1 6, .triangle 3 0]

-- Cycle fingerprint 364359bdca56063752587979ae8e8b66baa5f98995b802c3932514482da7a9ab.
def localCycle00089 : Cycle where
  length := 5
  data := {
    node := ![.distance 1 2, .theta 1, .distance 0 1, .distance 1 5, .distance 1 6, .distance 1 2]
    constant := ![-2, 3, -1, -2, 0]
    coefficient := ![0, 1, 0, 0, 0]
    strict := ![false, false, false, false, true] }
  origin := ![.gapLower 1 0, .corridorUpper 0 1, .triangle 3 0, .gapLower 1 4, .triangle 18 1]

-- Cycle fingerprint 37cc5361e0a9c4f34f564d19a69ef3f6fe6d8c5f5a955f5424248cc330f02d6f.
def localCycle00090 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 5, .distance 5 6, .distance 1 6, .distance 1 5, .theta 1, .distance 0 1, .distance 0 5]
    constant := ![-1, 0, -2, -1, 2, 0]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![false, true, false, false, false, true] }
  origin := ![.triangle 14 0, .triangle 24 2, .gapLower 1 4, .corridorLower 1 5, .gapLower 1 6, .triangle 3 2]

-- Cycle fingerprint 38e02d66ba3be761f7927c597ebb47351fe6a6659cccc42cf34f6d91da773baa.
def localCycle00091 : Cycle where
  length := 6
  data := {
    node := ![.distance 1 3, .distance 1 2, .theta 1, .distance 0 1, .distance 1 4, .distance 1 6, .distance 1 3]
    constant := ![-2, -1, 3, -1, -2, 0]
    coefficient := ![0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, true] }
  origin := ![.gapLower 1 1, .corridorLower 1 2, .corridorUpper 0 1, .triangle 2 0, .gapLower 1 4, .triangle 21 1]

-- Cycle fingerprint 39cdd7d03efa793f5c229414114ab697ecf4afc1a2f4cb1c109141c603c574ba.
def localCycle00092 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 0 3, .distance 3 6, .distance 5 6, .distance 4 6, .distance 1 4, .distance 4 5, .theta 4]
    constant := ![3, -1, -1, 0, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 9 0, .triangle 11 0, .triangle 33 1, .triangle 34 2, .triangle 23 0, .triangle 22 0, .corridorLower 4 5]

-- Cycle fingerprint 3a0a46d67be0670b4f5aa3d6f44f8f9f19ee78e8ae758ce9bc440d8f5a71da1b.
def localCycle00093 : Cycle where
  length := 6
  data := {
    node := ![.distance 1 5, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1, .distance 0 1, .distance 1 5]
    constant := ![0, 0, -2, -1, 2, -1]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![true, true, false, false, false, false] }
  origin := ![.triangle 22 1, .triangle 19 1, .gapLower 1 1, .corridorLower 1 2, .gapLower 1 6, .triangle 3 0]

-- Cycle fingerprint 3a6f5b12b7a4e15bff10ff8e32a77d271dceaa340ce665845b7afff0f4f38766.
def localCycle00094 : Cycle where
  length := 8
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 4, .distance 4 6, .distance 1 6, .distance 1 5, .distance 1 3, .distance 1 2, .theta 1]
    constant := ![4, 0, -1, 0, -2, 0, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, true, false, false] }
  origin := ![.gapLower 1 6, .triangle 2 2, .triangle 13 0, .triangle 23 2, .gapLower 1 4, .triangle 20 1, .gapLower 1 1, .corridorLower 1 2]

-- Cycle fingerprint 3abe8c8100ea5532b37d2f2e38019e02c96e490d89d0b3e058481bf101e3e20c.
def localCycle00095 : Cycle where
  length := 8
  data := {
    node := ![.theta 1, .theta 0, .zero, .theta 6, .distance 1 6, .distance 1 5, .distance 1 3, .distance 1 2, .theta 1]
    constant := ![0, 0, 0, 2, -2, 0, -2, -1]
    coefficient := ![0, 0, 1, 0, 0, 0, 0, 0]
    strict := ![true, false, false, true, false, true, false, false] }
  origin := ![.thetaNext 0, .thetaLower 0, .thetaUpper 6, .gapUpper 6 0, .gapLower 1 4, .triangle 20 1, .gapLower 1 1, .corridorLower 1 2]

-- Cycle fingerprint 3c18901d4f5112342afe61e1620eb572eace3472819777c6f38a5105a578d5ec.
def localCycle00096 : Cycle where
  length := 3
  data := {
    node := ![.distance 4 5, .distance 1 4, .distance 1 5, .distance 4 5]
    constant := ![2, -3, 0]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.gapUpper 4 1, .gapLower 1 3, .triangle 22 1]

-- Cycle fingerprint 3c4092c8607660df58e3d5f77f13e6e2e86f1d1274040278c4037b6bd2a85a79.
def localCycle00097 : Cycle where
  length := 11
  data := {
    node := ![.distance 3 4, .distance 2 4, .distance 4 5, .distance 5 6, .distance 1 5, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1, .zero, .theta 4, .distance 3 4]
    constant := ![0, -1, -1, -1, 0, 0, -3, -1, 0, 0, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1]
    strict := ![true, false, false, false, false, true, false, false, false, false, false] }
  origin := ![.triangle 25 2, .triangle 28 0, .triangle 34 0, .triangle 24 0, .gapLower 1 3, .triangle 19 1, .gapLower 1 1, .corridorLower 1 2, .thetaLower 1, .thetaUpper 4, .corridorUpper 3 4]

-- Cycle fingerprint 3cefce68e971f6cca44e6e63c7d803b41eefbf1c5fddabdcb899f10fd6eab8ec.
def localCycle00098 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 2, .theta 1, .zero, .theta 4, .distance 3 4, .distance 2 4, .distance 4 5, .distance 5 6, .distance 1 5, .distance 1 4, .distance 1 2]
    constant := ![-2, 0, 0, 3, 0, -1, -1, -1, -2, 0]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, false, false, true] }
  origin := ![.gapLower 1 0, .thetaLower 1, .thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 28 0, .triangle 34 0, .triangle 24 0, .gapLower 1 3, .triangle 16 1]

-- Cycle fingerprint 3dd28893ad5ca60e6acb5a73419f3f20ce63767f09f3854a73ac836f4d1860bf.
def localCycle00099 : Cycle where
  length := 8
  data := {
    node := ![.distance 3 4, .distance 2 4, .distance 4 5, .distance 5 6, .distance 1 6, .distance 1 5, .distance 1 4, .theta 4, .distance 3 4]
    constant := ![0, -1, -1, 0, -2, -2, 0, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![true, false, false, true, false, false, false, false] }
  origin := ![.triangle 25 2, .triangle 28 0, .triangle 34 0, .triangle 24 2, .gapLower 1 4, .gapLower 1 3, .gapLower 4 0, .corridorUpper 3 4]

-- Cycle fingerprint 3eacdadbd742648a1db99659e6d128a2307cd5dcddc63d953308296bb467f8f2.
def localCycle00100 : Cycle where
  length := 11
  data := {
    node := ![.distance 3 4, .distance 2 4, .distance 2 5, .distance 5 6, .distance 4 5, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1, .zero, .theta 4, .distance 3 4]
    constant := ![0, 0, -1, -1, -1, 0, -2, -2, 0, 0, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1]
    strict := ![true, true, false, false, false, false, false, false, false, false, false] }
  origin := ![.triangle 25 2, .triangle 28 2, .triangle 30 0, .triangle 34 0, .triangle 22 0, .gapLower 1 2, .gapLower 1 1, .gapLower 1 0, .thetaLower 1, .thetaUpper 4, .corridorUpper 3 4]

-- Cycle fingerprint 3edfbb414a9ed1428fb73a696246277c8e8241fce083b210e990b97f38251a39.
def localCycle00101 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 0 5, .distance 5 6, .distance 1 5, .distance 1 3, .distance 1 2, .theta 1, .distance 0 1]
    constant := ![0, 0, -1, -1, -3, 0, -1, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![true, true, false, false, false, true, false, false] }
  origin := ![.triangle 2 2, .triangle 12 2, .triangle 14 0, .triangle 24 0, .gapLower 1 2, .triangle 15 1, .corridorLower 1 2, .corridorUpper 0 1]

-- Cycle fingerprint 3f2ef9f0a7539d7f52f56ff96dfe3fa19bd064d91358622de05420b951dc202a.
def localCycle00102 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 4, .distance 1 5, .distance 1 2, .theta 1, .zero, .theta 6, .distance 1 6, .distance 1 4]
    constant := ![-2, 0, -2, 0, 0, 2, 0]
    coefficient := ![0, 0, 0, 0, 1, 0, 0]
    strict := ![false, true, false, false, false, true, true] }
  origin := ![.gapLower 1 3, .triangle 17 1, .gapLower 1 0, .thetaLower 1, .thetaUpper 6, .gapUpper 6 0, .triangle 23 1]

-- Cycle fingerprint 409adc83e671cd5faaa3136c211ccc3e3d71e2aab79462510d8fa86c5a85ec70.
def localCycle00103 : Cycle where
  length := 8
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 4, .distance 4 6, .distance 4 5, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1]
    constant := ![3, 0, -1, 0, -1, 0, 0, -2]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, true, false] }
  origin := ![.corridorUpper 0 1, .triangle 2 2, .triangle 13 0, .triangle 34 1, .triangle 22 0, .gapLower 1 2, .triangle 15 1, .gapLower 1 0]

-- Cycle fingerprint 409ec057968c4e727f43aca6015de1fbf05e7fd32c24283b9f345857e1f9df6e.
def localCycle00104 : Cycle where
  length := 14
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 4 6, .distance 3 6, .distance 2 6, .distance 1 6, .distance 0 1, .distance 1 2, .distance 1 3, .distance 3 5, .distance 2 3, .distance 3 4, .theta 3, .zero]
    constant := ![0, 3, 0, 0, 0, 0, -1, -1, 0, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, true, true, false, false, true, false, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 34 2, .triangle 32 2, .triangle 27 2, .triangle 18 2, .triangle 4 0, .triangle 0 0, .triangle 15 2, .triangle 20 0, .triangle 26 0, .triangle 25 0, .corridorLower 3 4, .thetaLower 3]

-- Cycle fingerprint 40d61a7afef54a75a9b2d5c280cbfceab5ed9a42c6bb77f576af6b2e6ee341fa.
def localCycle00105 : Cycle where
  length := 7
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 6, .distance 0 4, .distance 4 5, .distance 1 4, .distance 1 3, .theta 1]
    constant := ![2, 0, 0, -1, -1, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, false, false] }
  origin := ![.gapLower 1 6, .triangle 4 2, .triangle 13 1, .triangle 12 0, .triangle 22 0, .gapLower 1 2, .corridorLower 1 3]

-- Cycle fingerprint 42c4f749911dc0b70d32e8de6a6e18bea0a5be6ed6c851cbda476b702ce591a0.
def localCycle00106 : Cycle where
  length := 9
  data := {
    node := ![.theta 1, .zero, .theta 6, .distance 5 6, .distance 4 6, .distance 0 4, .distance 4 5, .distance 1 4, .distance 1 3, .theta 1]
    constant := ![0, 0, 3, 0, -1, -1, -1, -2, -1]
    coefficient := ![0, 1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, false, false] }
  origin := ![.thetaLower 1, .thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 13 0, .triangle 12 0, .triangle 22 0, .gapLower 1 2, .corridorLower 1 3]

-- Cycle fingerprint 43022028b7fb80c1ac0df59132a6ac3b89bf16e0c8d30b138d5c04be48725160.
def localCycle00107 : Cycle where
  length := 10
  data := {
    node := ![.theta 1, .zero, .theta 6, .distance 5 6, .distance 4 6, .distance 0 4, .distance 4 5, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1]
    constant := ![0, 0, 3, 0, -1, -1, -1, 0, -2, -2]
    coefficient := ![0, 1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, false, false, false] }
  origin := ![.thetaLower 1, .thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 13 0, .triangle 12 0, .triangle 22 0, .gapLower 1 2, .gapLower 1 1, .gapLower 1 0]

-- Cycle fingerprint 43e923c3071f34d098a6f6ed7997a8e4e7e01a03ee497c78ac25b60218c73c68.
def localCycle00108 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 3 5, .distance 5 6, .distance 4 6, .distance 0 4, .distance 1 4, .distance 4 5, .theta 4]
    constant := ![3, 0, -1, 0, -1, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, true, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 31 2, .triangle 33 0, .triangle 34 2, .triangle 13 0, .triangle 2 1, .triangle 22 0, .corridorLower 4 5]

-- Cycle fingerprint 443821ca6f245f1ddefa413d1f9b60a58aa944fb6e54c8ba6d36a4bcfa97ffb7.
def localCycle00109 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 5, .distance 5 6, .theta 5, .distance 4 5, .distance 3 4, .distance 2 3, .distance 0 2, .distance 1 2, .theta 1, .distance 0 1, .distance 1 5]
    constant := ![-1, -1, 3, -1, -1, -1, 0, -1, 2, -2]
    coefficient := ![0, 0, 1, 0, 0, 0, 0, 0, 1, 0]
    strict := ![false, false, false, false, false, false, true, false, false, false] }
  origin := ![.triangle 24 0, .corridorLower 5 6, .corridorUpper 4 5, .triangle 31 0, .triangle 25 0, .triangle 5 0, .triangle 0 1, .corridorLower 1 2, .gapLower 1 6, .gapLower 1 5]

-- Cycle fingerprint 4502c2d72ed1a54bd68e623de9c1bb17533edd8ac96c346d29a46db262195cbc.
def localCycle00110 : Cycle where
  length := 8
  data := {
    node := ![.distance 4 5, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1, .distance 0 1, .distance 0 4, .distance 4 6, .distance 4 5]
    constant := ![-1, 0, 0, -2, 2, 0, -1, 0]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![false, false, true, false, false, true, false, true] }
  origin := ![.triangle 22 0, .gapLower 1 2, .triangle 15 1, .gapLower 1 0, .gapLower 1 6, .triangle 2 2, .triangle 13 0, .triangle 34 1]

-- Cycle fingerprint 457851eb0f235e19d0b207f62147d787091449673190f5995b58e586263b137c.
def localCycle00111 : Cycle where
  length := 11
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 4 5, .distance 5 6, .distance 0 6, .distance 1 6, .distance 1 5, .distance 1 2, .theta 1, .zero, .theta 4]
    constant := ![3, 0, -1, -1, 0, 0, -2, 0, -2, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, false, false, false, true, false, true, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 28 0, .triangle 34 0, .gapLower 6 2, .triangle 4 1, .gapLower 1 4, .triangle 17 1, .gapLower 1 0, .thetaLower 1, .thetaUpper 4]

-- Cycle fingerprint 45916ec02d2f3bc90ada47c71df493867f4e7520c6e84c16da6bfecab368e068.
def localCycle00112 : Cycle where
  length := 8
  data := {
    node := ![.theta 1, .theta 0, .zero, .theta 6, .distance 1 6, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1]
    constant := ![0, 0, 0, 2, -2, 0, -2, -1]
    coefficient := ![0, 0, 1, 0, 0, 0, 0, 0]
    strict := ![true, false, false, true, false, true, false, false] }
  origin := ![.thetaNext 0, .thetaLower 0, .thetaUpper 6, .gapUpper 6 0, .gapLower 1 4, .triangle 19 1, .gapLower 1 1, .corridorLower 1 2]

-- Cycle fingerprint 4637cb59f85e97591845526875b032931a153d065b78f935d457ba29e75075e4.
def localCycle00113 : Cycle where
  length := 13
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 5 6, .distance 2 6, .distance 1 6, .distance 0 1, .distance 1 2, .distance 2 5, .distance 2 3, .distance 3 4, .theta 3, .zero]
    constant := ![0, 3, 0, -1, 0, 0, -1, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, true, false, false, false, true, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 33 0, .triangle 30 2, .triangle 18 2, .triangle 4 0, .triangle 0 0, .triangle 17 0, .triangle 26 1, .triangle 25 0, .corridorLower 3 4, .thetaLower 3]

-- Cycle fingerprint 4640637b3485742c5da251fb23b0ba7f2688f44ca589e3699c066709fd42703f.
def localCycle00114 : Cycle where
  length := 13
  data := {
    node := ![.distance 2 5, .distance 5 6, .distance 4 6, .distance 0 4, .distance 4 5, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1, .zero, .theta 4, .distance 3 4, .distance 2 4, .distance 2 5]
    constant := ![-1, 0, -1, -1, -1, 0, 0, -1, 0, 0, 3, 0, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![false, true, false, false, false, false, true, false, false, false, false, true, true] }
  origin := ![.triangle 30 0, .triangle 34 2, .triangle 13 0, .triangle 12 0, .triangle 22 0, .gapLower 1 2, .triangle 15 1, .corridorLower 1 2, .thetaLower 1, .thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 28 2]

-- Cycle fingerprint 48776341b4c65438d7559008ccd2577a03bd271ec81dbc075ddbed4e63b0a45f.
def localCycle00115 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 2, .theta 1, .distance 0 1, .distance 1 4, .distance 1 6, .distance 1 5, .distance 1 3, .distance 1 2]
    constant := ![-3, 3, -1, 0, 0, 0, 0]
    coefficient := ![0, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false, true] }
  origin := ![.gapLower 1 0, .corridorUpper 0 1, .triangle 2 0, .triangle 23 2, .triangle 24 1, .gapLower 1 2, .triangle 15 1]

-- Cycle fingerprint 49f00a41309252c3f02f9f0c71f7439f2dca30612468882ea43c880438f89982.
def localCycle00116 : Cycle where
  length := 11
  data := {
    node := ![.distance 5 6, .distance 4 5, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 3 5, .distance 5 6]
    constant := ![-1, -1, 0, 0, -2, 0, 0, 0, 3, 0, -1]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, true, false, true, false, false, false, true, false] }
  origin := ![.triangle 34 0, .triangle 22 0, .gapLower 1 2, .triangle 15 1, .gapLower 1 0, .thetaNext 0, .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 31 2, .triangle 33 0]

-- Cycle fingerprint 4a27cd20946dc4f4a1758dfabc4782c40c4158e8130e48ea7e103974dd76785a.
def localCycle00117 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 4, .distance 4 5, .distance 1 5, .distance 1 6, .theta 1, .distance 0 1, .distance 0 4]
    constant := ![-1, 0, -2, -1, 2, 0]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![false, true, false, false, false, true] }
  origin := ![.triangle 12 0, .triangle 22 2, .gapLower 1 4, .corridorLower 1 6, .gapLower 1 6, .triangle 2 2]

-- Cycle fingerprint 4b6ff5946818c8e5db48bb9c0dc302ed605b8374d2856566150e6bf57f1f0994.
def localCycle00118 : Cycle where
  length := 7
  data := {
    node := ![.theta 1, .distance 0 1, .distance 1 6, .distance 1 5, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1]
    constant := ![2, -1, 0, 0, 0, 0, -2]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, true, true, false] }
  origin := ![.gapLower 1 6, .triangle 4 0, .triangle 24 1, .triangle 22 1, .triangle 19 1, .triangle 15 1, .gapLower 1 0]

-- Cycle fingerprint 4c3922fd7fdabc73c8c042ff833147d956d4b146c4f919dc69868ad78018986b.
def localCycle00119 : Cycle where
  length := 11
  data := {
    node := ![.distance 2 4, .distance 2 5, .distance 5 6, .distance 4 5, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1, .zero, .theta 4, .distance 3 4, .distance 2 4]
    constant := ![0, -1, -1, -1, 0, 0, -3, 0, 0, 3, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![true, false, false, false, false, true, false, false, false, false, true] }
  origin := ![.triangle 28 2, .triangle 30 0, .triangle 34 0, .triangle 22 0, .gapLower 1 2, .triangle 15 1, .gapLower 1 0, .thetaLower 1, .thetaUpper 4, .corridorUpper 3 4, .triangle 25 2]

-- Cycle fingerprint 4c3bfc841962c90f386e5558285ee1e7b5ddb1db3c6b2c1d6b230d84f9594b55.
def localCycle00120 : Cycle where
  length := 8
  data := {
    node := ![.theta 1, .zero, .theta 6, .distance 1 6, .distance 1 5, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1]
    constant := ![0, 0, 2, 0, -2, 0, 0, -2]
    coefficient := ![0, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, true, true, false] }
  origin := ![.thetaLower 1, .thetaUpper 6, .gapUpper 6 0, .triangle 24 1, .gapLower 1 3, .triangle 19 1, .triangle 15 1, .gapLower 1 0]

-- Cycle fingerprint 4ed17b4f4f89e21b43fe71f36123baaf426a2d3d468c382c9d9835013f208a84.
def localCycle00121 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 3, .distance 3 6, .distance 5 6, .distance 4 5, .distance 1 4, .theta 4]
    constant := ![3, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 0, .triangle 27 0, .triangle 33 1, .triangle 34 0, .triangle 22 0, .gapLower 4 0]

-- Cycle fingerprint 4fad6d8c6e3e593c5ee5f70b7f2ca4c5a28048cf50c8611f4defee85eddebd4e.
def localCycle00122 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .theta 3, .theta 2, .theta 1, .distance 0 1, .distance 1 5, .distance 5 6, .theta 5, .theta 4]
    constant := ![0, 0, 0, 2, -2, -1, -1, 0]
    coefficient := ![0, 0, 0, 1, 0, 0, 0, 0]
    strict := ![true, true, true, false, false, false, false, true] }
  origin := ![.thetaNext 3, .thetaNext 2, .thetaNext 1, .gapLower 1 6, .gapLower 1 5, .triangle 24 0, .corridorLower 5 6, .thetaNext 4]

-- Cycle fingerprint 50391b31f056452a728307c39e475e6aa3a6df8b73ab5d1b1b5dd16c94a89d29.
def localCycle00123 : Cycle where
  length := 6
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 3, .distance 3 6, .distance 5 6, .distance 4 5, .theta 4]
    constant := ![3, -1, -1, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 0, .triangle 27 0, .triangle 33 1, .triangle 34 0, .corridorLower 4 5]

-- Cycle fingerprint 50a0140179814941d1e3e209d2e93e0aef1648ef1388c34e5478f3c4284ca285.
def localCycle00124 : Cycle where
  length := 6
  data := {
    node := ![.distance 1 3, .theta 1, .distance 0 1, .distance 1 4, .distance 1 6, .distance 1 5, .distance 1 3]
    constant := ![-1, 3, -1, 0, -2, -2]
    coefficient := ![0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false] }
  origin := ![.corridorLower 1 3, .corridorUpper 0 1, .triangle 2 0, .triangle 23 2, .gapLower 1 3, .gapLower 1 2]

-- Cycle fingerprint 5123fa93a3572e78f3608cc2a177f81ec9474f8e1e5ab56b43696340782960eb.
def localCycle00125 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 4 5, .distance 5 6, .distance 1 5, .distance 1 4, .theta 4]
    constant := ![3, 0, -1, -1, -1, -2, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 28 0, .triangle 34 0, .triangle 24 0, .gapLower 1 3, .gapLower 4 0]

-- Cycle fingerprint 52343fdf9aadb8b938e292b0fb4c44a86707308323135600d1d486ce2c8ed06f.
def localCycle00126 : Cycle where
  length := 10
  data := {
    node := ![.theta 4, .distance 3 4, .distance 4 5, .distance 4 6, .distance 2 4, .distance 2 3, .distance 1 2, .theta 1, .theta 0, .zero, .theta 4]
    constant := ![3, -1, 0, -1, 0, -1, -2, 0, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![false, false, true, false, false, false, false, true, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 31 0, .triangle 34 2, .triangle 29 0, .gapLower 2 3, .triangle 15 0, .gapLower 1 0, .thetaNext 0, .thetaLower 0, .thetaUpper 4]

-- Cycle fingerprint 52515d53cd1e314d50830254f88966acf5a0a0469a8afc817beec53485a771fa.
def localCycle00127 : Cycle where
  length := 8
  data := {
    node := ![.theta 1, .theta 0, .zero, .theta 6, .distance 1 6, .distance 1 5, .distance 1 4, .distance 1 3, .theta 1]
    constant := ![0, 0, 0, 2, -2, 0, -2, -1]
    coefficient := ![0, 0, 1, 0, 0, 0, 0, 0]
    strict := ![true, false, false, true, false, true, false, false] }
  origin := ![.thetaNext 0, .thetaLower 0, .thetaUpper 6, .gapUpper 6 0, .gapLower 1 4, .triangle 22 1, .gapLower 1 2, .corridorLower 1 3]

-- Cycle fingerprint 5312309406c4b4e27c2eeababb40b8164433127539b2623b754a54445f448eb9.
def localCycle00128 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 3 5, .distance 5 6, .distance 4 6, .distance 0 4, .distance 4 5, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, 0, -1, 0, -1, -1, -1, 0, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false, false, true, true, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 31 2, .triangle 33 0, .triangle 34 2, .triangle 13 0, .triangle 12 0, .triangle 22 0, .triangle 19 1, .triangle 15 1, .corridorLower 1 2, .thetaLower 1]

-- Cycle fingerprint 542bf5c7167afe4b615bfd125cfa833eca9bf3722ba80179cd6ab5ef97e17979.
def localCycle00129 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 2, .theta 1, .distance 0 1, .distance 1 5, .distance 5 6, .theta 5, .distance 4 5, .distance 3 4, .distance 2 3, .distance 1 2]
    constant := ![-2, 2, -1, -1, -1, 3, -1, -1, -1]
    coefficient := ![0, 1, 0, 0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false, false] }
  origin := ![.gapLower 1 0, .gapLower 1 6, .triangle 3 0, .triangle 24 0, .corridorLower 5 6, .corridorUpper 4 5, .triangle 31 0, .triangle 25 0, .triangle 15 0]

-- Cycle fingerprint 54a548c01dd81cdf698fe5106df2a8ddeead83f7853cfb1ba4503d116073d5fe.
def localCycle00130 : Cycle where
  length := 3
  data := {
    node := ![.distance 5 6, .distance 1 6, .distance 1 5, .distance 5 6]
    constant := ![0, -3, 2]
    coefficient := ![0, 0, 0]
    strict := ![false, false, true] }
  origin := ![.gapLower 6 1, .gapLower 1 4, .gapUpper 5 1]

-- Cycle fingerprint 54de1644b425488cd3d5f8159eac4c81c8e868b94673d0ecc75ed7f760651e22.
def localCycle00131 : Cycle where
  length := 12
  data := {
    node := ![.distance 4 6, .distance 2 4, .distance 2 3, .distance 1 2, .theta 1, .distance 0 1, .distance 1 5, .distance 5 6, .theta 5, .theta 4, .distance 3 4, .distance 4 5, .distance 4 6]
    constant := ![-1, 0, -1, -2, 2, -1, -1, -1, 0, 3, -1, 0]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0]
    strict := ![false, false, false, false, false, false, false, false, true, false, false, true] }
  origin := ![.triangle 29 0, .gapLower 2 3, .triangle 15 0, .gapLower 1 0, .gapLower 1 6, .triangle 3 0, .triangle 24 0, .corridorLower 5 6, .thetaNext 4, .corridorUpper 3 4, .triangle 31 0, .triangle 34 2]

-- Cycle fingerprint 5630c832a69850495cc9ec12ae6687e0a578d5479288742f84ec52b59b368c91.
def localCycle00132 : Cycle where
  length := 7
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 4, .distance 4 5, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1]
    constant := ![2, 0, -1, -1, 0, 0, -2]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, true, false] }
  origin := ![.gapLower 1 6, .triangle 2 2, .triangle 12 0, .triangle 22 0, .gapLower 1 2, .triangle 15 1, .gapLower 1 0]

-- Cycle fingerprint 568f19a51fe8cb7b67eb35c53ee3427bd1eb55df49451e8a8420a5f982bfa041.
def localCycle00133 : Cycle where
  length := 10
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 2 5, .distance 5 6, .distance 4 5, .distance 1 4, .distance 1 3, .theta 1, .zero, .theta 4]
    constant := ![3, 0, 0, -1, -1, -1, -2, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, true, false, false, false, false, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 28 2, .triangle 30 0, .triangle 34 0, .triangle 22 0, .gapLower 1 2, .corridorLower 1 3, .thetaLower 1, .thetaUpper 4]

-- Cycle fingerprint 574ddc68d34b3b067e3d57460d4f5f76965571f0d3093aa02b11f85874d63114.
def localCycle00134 : Cycle where
  length := 10
  data := {
    node := ![.theta 3, .distance 3 6, .distance 2 6, .distance 1 6, .distance 0 1, .distance 1 2, .distance 1 3, .distance 3 4, .distance 2 3, .distance 3 5, .theta 3]
    constant := ![4, 0, 0, -1, -1, 0, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, true, false, false, false, false] }
  origin := ![.gapLower 3 6, .triangle 27 2, .triangle 18 2, .triangle 4 0, .triangle 0 0, .triangle 15 2, .triangle 19 0, .triangle 25 0, .triangle 26 0, .corridorLower 3 5]

-- Cycle fingerprint 5794cc39360a7167603070caf1a046dbbecbb3fbb0fdcf130d2f78f39bc1a572.
def localCycle00135 : Cycle where
  length := 7
  data := {
    node := ![.theta 1, .distance 0 1, .distance 1 4, .distance 1 6, .distance 1 5, .distance 1 3, .distance 1 2, .theta 1]
    constant := ![2, -1, 0, 0, 0, 0, -2]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, true, false] }
  origin := ![.gapLower 1 6, .triangle 2 0, .triangle 23 2, .triangle 24 1, .gapLower 1 2, .triangle 15 1, .gapLower 1 0]

-- Cycle fingerprint 57e116fb4946ca29596ca8d61682c97d467cb6469828953cdc947a04a5ff70ad.
def localCycle00136 : Cycle where
  length := 5
  data := {
    node := ![.distance 1 4, .distance 1 3, .theta 1, .distance 0 1, .distance 1 5, .distance 1 4]
    constant := ![-2, -1, 3, -2, 0]
    coefficient := ![0, 0, 1, 0, 0]
    strict := ![false, false, false, false, true] }
  origin := ![.gapLower 1 2, .corridorLower 1 3, .corridorUpper 0 1, .gapLower 1 5, .triangle 22 1]

-- Cycle fingerprint 5824a38ea53b7a44e05a8288e4a9067c11158cff2cab520c3557ac2fc9fc1134.
def localCycle00137 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 3, .distance 1 2, .theta 1, .distance 0 1, .distance 1 4, .distance 1 6, .distance 1 5, .distance 1 3]
    constant := ![-3, -1, 3, -1, 0, 0, 0]
    coefficient := ![0, 0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, false] }
  origin := ![.gapLower 1 1, .corridorLower 1 2, .corridorUpper 0 1, .triangle 2 0, .triangle 23 2, .triangle 24 1, .gapLower 1 2]

-- Cycle fingerprint 58cfdd84858c172bf5c64ef937373ae3bd16fdd5a3257337c535ac52eda6b784.
def localCycle00138 : Cycle where
  length := 7
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 4, .distance 4 6, .distance 4 5, .distance 1 4, .distance 1 3, .theta 1]
    constant := ![1, 0, -1, 0, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, false] }
  origin := ![.gapLower 1 6, .triangle 2 2, .triangle 13 0, .triangle 34 1, .triangle 22 0, .gapLower 1 2, .corridorLower 1 3]

-- Cycle fingerprint 596005461dd59ec778ebd07bf283f7de8dba507757dce9fb97422bb6662b481a.
def localCycle00139 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 0 5, .distance 5 6, .distance 1 5, .distance 1 3, .distance 1 2, .theta 1, .distance 0 1]
    constant := ![0, 0, -1, -1, -2, 0, -2, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![true, true, false, false, false, true, false, false] }
  origin := ![.triangle 2 2, .triangle 12 2, .triangle 14 0, .triangle 24 0, .gapLower 1 2, .triangle 15 1, .gapLower 1 0, .corridorUpper 0 1]

-- Cycle fingerprint 598293ca09f94b2798cf4db4f6e8b1ab33f327291be3d0dc3e34f5f7481b2273.
def localCycle00140 : Cycle where
  length := 6
  data := {
    node := ![.distance 1 4, .distance 1 3, .theta 1, .distance 0 1, .distance 1 5, .distance 1 6, .distance 1 4]
    constant := ![-2, -1, 3, -1, -2, 0]
    coefficient := ![0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, true] }
  origin := ![.gapLower 1 2, .corridorLower 1 3, .corridorUpper 0 1, .triangle 3 0, .gapLower 1 4, .triangle 23 1]

-- Cycle fingerprint 59af7a0e5e0557fe72c55251baeef1451f0ff9e449cb65a35f142723f8c4ea9b.
def localCycle00141 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 2, .theta 1, .distance 0 1, .distance 0 4, .distance 4 5, .distance 1 4, .distance 1 3, .distance 1 2]
    constant := ![-3, 3, 0, -1, -1, 0, 0]
    coefficient := ![0, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, true] }
  origin := ![.gapLower 1 0, .corridorUpper 0 1, .triangle 2 2, .triangle 12 0, .triangle 22 0, .gapLower 1 2, .triangle 15 1]

-- Cycle fingerprint 5a28d79874061aa88c97bb8cfb69957fd192b0ba3bcd40830a8ac0da13553ac0.
def localCycle00142 : Cycle where
  length := 4
  data := {
    node := ![.distance 0 1, .distance 1 4, .distance 1 6, .theta 1, .distance 0 1]
    constant := ![-2, -2, -1, 3]
    coefficient := ![0, 0, 0, 1]
    strict := ![false, false, false, false] }
  origin := ![.gapLower 1 5, .gapLower 1 4, .corridorLower 1 6, .corridorUpper 0 1]

-- Cycle fingerprint 5af6f01d292144522b040357d6b78e7214dedb7b3a9dd01810d85f426db37479.
def localCycle00143 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 2, .theta 1, .distance 0 1, .distance 0 4, .distance 4 5, .distance 1 5, .distance 1 6, .distance 1 4, .distance 1 3, .distance 1 2]
    constant := ![-1, 2, 0, -1, 0, 0, -2, 0, 0]
    coefficient := ![0, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, true, false, false, true] }
  origin := ![.corridorLower 1 2, .gapLower 1 6, .triangle 2 2, .triangle 12 0, .triangle 22 2, .triangle 24 2, .gapLower 1 3, .gapLower 1 2, .triangle 15 1]

-- Cycle fingerprint 5b98ddfc98ef442a81a78cda18f579801a762c50da4daac9ea58bca87cf903e1.
def localCycle00144 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 6, .distance 1 5, .distance 1 3, .distance 1 2, .theta 1, .zero, .theta 6, .distance 1 6]
    constant := ![-2, 0, -2, -1, 0, 0, 2]
    coefficient := ![0, 0, 0, 0, 0, 1, 0]
    strict := ![false, true, false, false, false, false, true] }
  origin := ![.gapLower 1 4, .triangle 20 1, .gapLower 1 1, .corridorLower 1 2, .thetaLower 1, .thetaUpper 6, .gapUpper 6 0]

-- Cycle fingerprint 5bac2612b7da3af0b7bbb6ead873970df39d57a8a156e8c6627cefbb8bf9f830.
def localCycle00145 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 3, .distance 3 6, .distance 0 6, .distance 5 6, .distance 4 5, .theta 4]
    constant := ![3, -1, -1, 0, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 0, .triangle 27 0, .triangle 11 2, .triangle 14 1, .triangle 34 0, .corridorLower 4 5]

-- Cycle fingerprint 5beefed54fde0d5502626bda2dab9d68af06945cb6d55de73c3b1accaa20b476.
def localCycle00146 : Cycle where
  length := 6
  data := {
    node := ![.theta 4, .distance 3 4, .distance 4 5, .distance 0 4, .distance 4 6, .distance 1 4, .theta 4]
    constant := ![3, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 31 0, .triangle 12 0, .triangle 13 0, .triangle 23 0, .gapLower 4 0]

-- Cycle fingerprint 5c097f5ddb0bfac562e97851537830f6f981c38c4e20124478f68a0bb841ec47.
def localCycle00147 : Cycle where
  length := 11
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 2 5, .distance 5 6, .distance 4 5, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1, .zero, .theta 4]
    constant := ![3, 0, 0, -1, -1, -1, -2, -2, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, true, false, false, false, false, false, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 28 2, .triangle 30 0, .triangle 34 0, .triangle 22 0, .gapLower 1 2, .gapLower 1 1, .corridorLower 1 2, .thetaLower 1, .thetaUpper 4]

-- Cycle fingerprint 5c50bc32c0ea756cc8ac4cf8218a7c1eae0094b17806d6430d256238bf6e7055.
def localCycle00148 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 6, .distance 1 5, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1, .distance 0 1, .distance 0 4, .distance 4 6, .distance 1 6]
    constant := ![0, -2, 0, 0, -2, 3, 0, -1, 0]
    coefficient := ![0, 0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![true, false, false, true, false, false, true, false, true] }
  origin := ![.triangle 24 1, .gapLower 1 3, .gapLower 1 2, .triangle 15 1, .gapLower 1 0, .corridorUpper 0 1, .triangle 2 2, .triangle 13 0, .triangle 23 2]

-- Cycle fingerprint 5c96f37054b7bac940bc67395f93a0343906f24aef0015b313d6ef0038777f6e.
def localCycle00149 : Cycle where
  length := 5
  data := {
    node := ![.distance 1 5, .distance 1 4, .theta 1, .distance 0 1, .distance 1 6, .distance 1 5]
    constant := ![-2, -1, 3, -2, 0]
    coefficient := ![0, 0, 1, 0, 0]
    strict := ![false, false, false, false, true] }
  origin := ![.gapLower 1 3, .corridorLower 1 4, .corridorUpper 0 1, .gapLower 1 5, .triangle 24 1]

-- Cycle fingerprint 5d7c718573f66d0c974cbf5d5f57fe51706d0504c4d55141e89c3a4b06a083ec.
def localCycle00150 : Cycle where
  length := 7
  data := {
    node := ![.theta 1, .distance 0 1, .distance 1 4, .distance 1 6, .distance 1 5, .distance 1 3, .distance 1 2, .theta 1]
    constant := ![2, -1, 0, -2, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, true, false] }
  origin := ![.gapLower 1 6, .triangle 2 0, .triangle 23 2, .gapLower 1 3, .triangle 20 1, .triangle 15 1, .corridorLower 1 2]

-- Cycle fingerprint 62553236ae4e48984e455dbd9c35e1108d1ae81038d53a8350c112a65dfb3b1f.
def localCycle00151 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 6, .distance 1 6, .distance 1 5, .distance 1 4, .theta 4, .distance 3 4, .distance 2 4, .distance 4 5, .distance 5 6, .distance 0 6]
    constant := ![0, -3, 0, 0, 3, 0, -1, -1, 0]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0, 0]
    strict := ![true, false, true, false, false, true, false, false, false] }
  origin := ![.triangle 4 1, .gapLower 1 4, .triangle 22 1, .gapLower 4 0, .corridorUpper 3 4, .triangle 25 2, .triangle 28 0, .triangle 34 0, .gapLower 6 2]

-- Cycle fingerprint 62ab26ffff57b6041a9135e3c77a54d9ee960e40e786680411fc93ac7a8c9155.
def localCycle00152 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 0 4, .distance 4 5, .distance 1 4, .distance 4 6, .distance 5 6, .theta 5, .theta 4]
    constant := ![3, 0, 0, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, false, true, false, true] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 6 2, .triangle 12 0, .triangle 22 0, .triangle 23 0, .triangle 34 1, .corridorLower 5 6, .thetaNext 4]

-- Cycle fingerprint 631c4daf1c050edff9e565f036a802e9b76e57b3227bbc7396cb37b0c287c4ee.
def localCycle00153 : Cycle where
  length := 7
  data := {
    node := ![.theta 1, .distance 0 1, .distance 1 6, .distance 1 5, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1]
    constant := ![2, -1, -2, 0, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, true, false] }
  origin := ![.gapLower 1 6, .triangle 4 0, .gapLower 1 4, .triangle 22 1, .triangle 19 1, .triangle 15 1, .corridorLower 1 2]

-- Cycle fingerprint 6368863ed9c57673b24e207e8f6844ee71f58544a0a838aace1fe1e36137dc35.
def localCycle00154 : Cycle where
  length := 10
  data := {
    node := ![.theta 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 3 5, .distance 5 6, .distance 4 5, .distance 1 4, .distance 1 3, .theta 1]
    constant := ![0, 0, 0, 3, 0, -1, -1, -1, -3, -1]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![true, false, false, false, true, false, false, false, false, false] }
  origin := ![.thetaNext 0, .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 31 2, .triangle 33 0, .triangle 34 0, .triangle 22 0, .gapLower 1 2, .corridorLower 1 3]

-- Cycle fingerprint 64f61d124f6de9e8d0f6a34c12a8af017f0944b03dab5d7e97ac653536a57a60.
def localCycle00155 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 6, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1, .distance 0 1, .distance 1 5, .distance 1 6]
    constant := ![-3, 0, 0, -1, 3, -1, 0]
    coefficient := ![0, 0, 0, 0, 1, 0, 0]
    strict := ![false, true, true, false, false, false, true] }
  origin := ![.gapLower 1 3, .triangle 19 1, .triangle 15 1, .corridorLower 1 2, .corridorUpper 0 1, .triangle 3 0, .triangle 24 2]

-- Cycle fingerprint 65138438b4e31e994e6a0fba0feb80cd7491a7686173119ff10068f8a81566c3.
def localCycle00156 : Cycle where
  length := 8
  data := {
    node := ![.distance 5 6, .distance 1 5, .distance 1 3, .distance 1 2, .theta 1, .distance 0 1, .distance 0 4, .distance 0 5, .distance 5 6]
    constant := ![-1, 0, -2, -1, 2, 0, 0, -1]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, false] }
  origin := ![.triangle 24 0, .gapLower 1 2, .gapLower 1 1, .corridorLower 1 2, .gapLower 1 6, .triangle 2 2, .triangle 12 2, .triangle 14 0]

-- Cycle fingerprint 65b452fe0f7ad806ae70db5f18844b849b0dd01c0b31d1535a5462c846bcc3c7.
def localCycle00157 : Cycle where
  length := 8
  data := {
    node := ![.distance 1 5, .distance 1 3, .distance 1 2, .theta 1, .distance 0 1, .distance 0 4, .distance 0 5, .distance 5 6, .distance 1 5]
    constant := ![-2, 0, -1, 3, 0, 0, -1, -1]
    coefficient := ![0, 0, 0, 1, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, true, false, false] }
  origin := ![.gapLower 1 2, .triangle 15 1, .corridorLower 1 2, .corridorUpper 0 1, .triangle 2 2, .triangle 12 2, .triangle 14 0, .triangle 24 0]

-- Cycle fingerprint 66418fa9293373ee06089a3027c038efef1d1ba6e599557b0eb1b955803e1cb9.
def localCycle00158 : Cycle where
  length := 3
  data := {
    node := ![.distance 5 6, .distance 1 6, .distance 1 5, .distance 5 6]
    constant := ![0, -3, 2]
    coefficient := ![0, 0, 0]
    strict := ![false, false, true] }
  origin := ![.gapLower 6 2, .gapLower 1 3, .gapUpper 5 2]

-- Cycle fingerprint 6665ca803be2b6e7555998b14a52ffe471495f1d55b2aa79b87631dc1f61b976.
def localCycle00159 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 2, .theta 1, .zero, .theta 4, .distance 3 4, .distance 4 5, .distance 5 6, .distance 1 5, .distance 1 4, .distance 1 3, .distance 1 2]
    constant := ![-1, 0, 0, 3, -1, -1, -1, 0, -2, -2]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, true, false, false] }
  origin := ![.corridorLower 1 2, .thetaLower 1, .thetaUpper 4, .corridorUpper 3 4, .triangle 31 0, .triangle 34 0, .triangle 24 0, .triangle 22 1, .gapLower 1 2, .gapLower 1 1]

-- Cycle fingerprint 694047e6014902fc144cd77870340bf9ed3d5373ebc347cba453a50746cf1496.
def localCycle00160 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 0 3, .distance 3 5, .distance 2 3, .distance 3 4, .theta 3, .zero]
    constant := ![0, 3, 0, 0, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 11 0, .triangle 10 0, .triangle 26 0, .triangle 25 0, .corridorLower 3 4, .thetaLower 3]

-- Cycle fingerprint 695a3f5673868e765d496ec46936a5bf647d391104084b1761aef4b084b4b73a.
def localCycle00161 : Cycle where
  length := 6
  data := {
    node := ![.distance 1 4, .distance 1 6, .distance 1 5, .distance 1 3, .theta 1, .distance 0 1, .distance 1 4]
    constant := ![0, 0, -2, -1, 2, -1]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![true, true, false, false, false, false] }
  origin := ![.triangle 23 2, .triangle 24 1, .gapLower 1 2, .corridorLower 1 3, .gapLower 1 6, .triangle 2 0]

-- Cycle fingerprint 698313b21102abb9b46619179b695f1337ac7eb024b88d958452c247c326ad27.
def localCycle00162 : Cycle where
  length := 6
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 4, .distance 2 3, .distance 2 6, .theta 6, .theta 5]
    constant := ![3, -1, -1, 0, -2, 0]
    coefficient := ![1, 0, 0, 0, -1, 0]
    strict := ![false, false, false, true, true, true] }
  origin := ![.corridorUpper 4 5, .triangle 31 0, .triangle 25 0, .triangle 27 2, .gapUpper 6 6, .thetaNext 5]

-- Cycle fingerprint 698828e8d032767924612ef50d952d2c17988ec264a1e5b6b1aca35b7469c09e.
def localCycle00163 : Cycle where
  length := 10
  data := {
    node := ![.theta 4, .distance 3 4, .distance 3 5, .distance 5 6, .distance 4 5, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1, .zero, .theta 4]
    constant := ![3, 0, -1, -1, -1, 0, -2, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, false, false, false, true, false, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 31 2, .triangle 33 0, .triangle 34 0, .triangle 22 0, .triangle 19 1, .gapLower 1 1, .corridorLower 1 2, .thetaLower 1, .thetaUpper 4]

-- Cycle fingerprint 6a61c602276640d12ac27ffccb393c44857865c0ea0f86a068538656253e1430.
def localCycle00164 : Cycle where
  length := 8
  data := {
    node := ![.distance 3 4, .distance 2 4, .distance 4 5, .distance 5 6, .distance 1 5, .distance 1 4, .distance 1 3, .theta 3, .distance 3 4]
    constant := ![0, -1, -1, -1, -3, 0, 0, 4]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![true, false, false, false, false, true, false, false] }
  origin := ![.triangle 25 2, .triangle 28 0, .triangle 34 0, .triangle 24 0, .gapLower 1 3, .triangle 19 1, .gapLower 3 0, .gapLower 3 6]

-- Cycle fingerprint 6b880b4ccbe86cdab03fd91dd185daa8e715f9e7a05e992700c2f2f69334d4fd.
def localCycle00165 : Cycle where
  length := 9
  data := {
    node := ![.distance 2 3, .distance 1 2, .theta 1, .zero, .theta 4, .distance 3 4, .distance 4 6, .distance 4 5, .distance 2 4, .distance 2 3]
    constant := ![-1, -3, 0, 0, 3, -1, 0, -1, 0]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, false, false] }
  origin := ![.triangle 15 0, .gapLower 1 0, .thetaLower 1, .thetaUpper 4, .corridorUpper 3 4, .triangle 32 0, .triangle 34 1, .triangle 28 0, .gapLower 2 3]

-- Cycle fingerprint 6ca81b38d1e831ec079b2ef634511710fc6e0e7caa264f69c1e8aabf0bc3a89b.
def localCycle00166 : Cycle where
  length := 8
  data := {
    node := ![.distance 1 5, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1, .distance 0 1, .distance 0 5, .distance 5 6, .distance 1 5]
    constant := ![0, -2, 0, -1, 2, 0, -1, -1]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![false, false, true, false, false, true, false, false] }
  origin := ![.gapLower 1 3, .gapLower 1 2, .triangle 15 1, .corridorLower 1 2, .gapLower 1 6, .triangle 3 2, .triangle 14 0, .triangle 24 0]

-- Cycle fingerprint 6d132e698840411674130d2f88078ba8acd9586b4589b9f2a806593df5ceff0a.
def localCycle00167 : Cycle where
  length := 4
  data := {
    node := ![.distance 0 1, .distance 1 4, .distance 1 2, .theta 1, .distance 0 1]
    constant := ![-2, 0, -2, 3]
    coefficient := ![0, 0, 0, 1]
    strict := ![false, true, false, false] }
  origin := ![.gapLower 1 5, .triangle 16 1, .gapLower 1 0, .corridorUpper 0 1]

-- Cycle fingerprint 6d33455c867c8e9241ed7e26f028fc8670f1425d72189db6be8421bef3c1e425.
def localCycle00168 : Cycle where
  length := 10
  data := {
    node := ![.distance 3 4, .distance 3 5, .distance 5 6, .distance 4 5, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1, .zero, .theta 4, .distance 3 4]
    constant := ![0, -1, -1, -1, 0, 0, -2, 0, 0, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 1, 1]
    strict := ![true, false, false, false, false, true, false, false, false, false] }
  origin := ![.triangle 31 2, .triangle 33 0, .triangle 34 0, .triangle 22 0, .gapLower 1 2, .triangle 15 1, .gapLower 1 0, .thetaLower 1, .thetaUpper 4, .corridorUpper 3 4]

-- Cycle fingerprint 6da17ea09e8552b3ef4369340a2aa6ef1209a95f1d4488ed66489b5b618d6143.
def localCycle00169 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 3, .distance 1 2, .theta 1, .distance 0 1, .distance 1 4, .distance 1 6, .distance 1 5, .distance 1 3]
    constant := ![-2, -1, 3, -1, 0, -2, 0]
    coefficient := ![0, 0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, true] }
  origin := ![.gapLower 1 1, .corridorLower 1 2, .corridorUpper 0 1, .triangle 2 0, .triangle 23 2, .gapLower 1 3, .triangle 20 1]

-- Cycle fingerprint 6eb890f5fbbf0cc81d97613b220173bc2f1022c3c6ae76169cb6d79a9d35cb24.
def localCycle00170 : Cycle where
  length := 3
  data := {
    node := ![.distance 5 6, .distance 1 6, .distance 1 5, .distance 5 6]
    constant := ![0, -2, 2]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.triangle 24 2, .gapLower 1 4, .gapUpper 5 1]

-- Cycle fingerprint 6f1696a9bc4288e3d6fdae7493e2ff48fe9cbc1bab7f05881a8f611409aa4dea.
def localCycle00171 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 5, .distance 5 6, .theta 5, .theta 4, .distance 3 4, .distance 4 5, .distance 2 5, .theta 2, .theta 1, .distance 0 1, .distance 1 5]
    constant := ![-1, -1, 0, 3, -1, 0, -2, 0, 2, -2]
    coefficient := ![0, 0, 0, 1, 0, 0, -1, 0, 1, 0]
    strict := ![false, false, true, false, false, false, true, true, false, false] }
  origin := ![.triangle 24 0, .corridorLower 5 6, .thetaNext 4, .corridorUpper 3 4, .triangle 31 0, .gapLower 5 4, .gapUpper 2 6, .thetaNext 1, .gapLower 1 6, .gapLower 1 5]

-- Cycle fingerprint 71097c19433b6ce3f3872b0c196a83484db92e411413b6954a1829967339d594.
def localCycle00172 : Cycle where
  length := 8
  data := {
    node := ![.distance 1 5, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1, .distance 0 1, .distance 0 5, .distance 5 6, .distance 1 5]
    constant := ![-2, 0, 0, -1, 2, 0, -1, -1]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![false, true, true, false, false, true, false, false] }
  origin := ![.gapLower 1 3, .triangle 19 1, .triangle 15 1, .corridorLower 1 2, .gapLower 1 6, .triangle 3 2, .triangle 14 0, .triangle 24 0]

-- Cycle fingerprint 71f66dcaa20977570ee30b5dc28d428068596f111abbb633ce27cb0dc0134994.
def localCycle00173 : Cycle where
  length := 9
  data := {
    node := ![.distance 5 6, .distance 1 6, .distance 1 5, .distance 1 3, .distance 1 2, .theta 1, .distance 0 1, .distance 0 4, .distance 0 5, .distance 5 6]
    constant := ![0, -2, 0, -2, -1, 4, 0, 0, -1]
    coefficient := ![0, 0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![true, false, true, false, false, false, true, true, false] }
  origin := ![.triangle 24 2, .gapLower 1 3, .triangle 20 1, .gapLower 1 1, .corridorLower 1 2, .gapLower 1 6, .triangle 2 2, .triangle 12 2, .triangle 14 0]

-- Cycle fingerprint 71fd014da2d7af22be62a59d832fd75bd8883eef350bc29b7fbfff5c12bb561d.
def localCycle00174 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 3, .distance 1 2, .theta 1, .distance 0 1, .distance 1 4, .distance 1 6, .distance 1 5, .distance 1 3]
    constant := ![-2, -2, 3, -1, 0, 0, 0]
    coefficient := ![0, 0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, false] }
  origin := ![.gapLower 1 1, .gapLower 1 0, .corridorUpper 0 1, .triangle 2 0, .triangle 23 2, .triangle 24 1, .gapLower 1 2]

-- Cycle fingerprint 7259d913abf72cf39e13ef91f091ddc0e73ba3cfbd4c0a36d2bd31fc9ebc02a4.
def localCycle00175 : Cycle where
  length := 3
  data := {
    node := ![.distance 5 6, .distance 1 5, .distance 1 6, .distance 5 6]
    constant := ![2, -3, 0]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.gapUpper 5 1, .gapLower 1 4, .triangle 24 1]

-- Cycle fingerprint 7325a92c6a8e2609d202bd7b4eb46cbd0ff82bebf4e070c4f52a943ff5195d3b.
def localCycle00176 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 4, .distance 1 2, .theta 1, .zero, .theta 4, .distance 3 4, .distance 4 5, .distance 5 6, .distance 1 5, .distance 1 4]
    constant := ![0, -3, 0, 0, 3, -1, -1, -1, 0]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![true, false, false, false, false, false, false, false, false] }
  origin := ![.triangle 16 1, .gapLower 1 0, .thetaLower 1, .thetaUpper 4, .corridorUpper 3 4, .triangle 31 0, .triangle 34 0, .triangle 24 0, .gapLower 1 3]

-- Cycle fingerprint 732fbfcc196f89ee4b1f73b850af47cec8d65f7821dd6990e93a581b50806bc2.
def localCycle00177 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 2 5, .distance 5 6, .distance 4 6, .distance 0 4, .distance 1 4, .distance 4 5, .theta 4]
    constant := ![3, 0, 0, -1, 0, -1, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, true, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 28 2, .triangle 30 0, .triangle 34 2, .triangle 13 0, .triangle 2 1, .triangle 22 0, .corridorLower 4 5]

-- Cycle fingerprint 73f028b8165c84340ef330b85e66187ec19edfd7340563a62df9b3951c0b8fb5.
def localCycle00178 : Cycle where
  length := 5
  data := {
    node := ![.theta 5, .distance 3 5, .distance 2 3, .distance 2 6, .theta 6, .theta 5]
    constant := ![3, -1, 0, -2, 0]
    coefficient := ![1, 0, 0, -1, 0]
    strict := ![false, false, true, true, true] }
  origin := ![.corridorUpper 3 5, .triangle 26 0, .triangle 27 2, .gapUpper 6 6, .thetaNext 5]

-- Cycle fingerprint 7412e55ec03db0a2d1a782c6d06cff9324c7eed6ad78d974f3af6fe27b664ddb.
def localCycle00179 : Cycle where
  length := 9
  data := {
    node := ![.distance 4 6, .distance 1 6, .distance 1 5, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1, .distance 0 1, .distance 0 4, .distance 4 6]
    constant := ![0, -3, 0, 0, 0, -1, 3, 0, -1]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 0, 0]
    strict := ![true, false, true, true, true, false, false, true, false] }
  origin := ![.triangle 23 2, .gapLower 1 4, .triangle 22 1, .triangle 19 1, .triangle 15 1, .corridorLower 1 2, .corridorUpper 0 1, .triangle 2 2, .triangle 13 0]

-- Cycle fingerprint 7492e3a819d1556446959fcbc2bc7c9711a00986b8f56ca21fb06994558653ea.
def localCycle00180 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 5, .distance 1 4, .distance 1 3, .theta 1, .zero, .theta 4, .distance 3 4, .distance 4 5, .distance 5 6, .distance 1 5]
    constant := ![0, -3, -1, 0, 0, 3, -1, -1, -1]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false, false] }
  origin := ![.gapLower 1 3, .gapLower 1 2, .corridorLower 1 3, .thetaLower 1, .thetaUpper 4, .corridorUpper 3 4, .triangle 31 0, .triangle 34 0, .triangle 24 0]

-- Cycle fingerprint 74f321547ef23b4b1b7b49e1657c95d48d497c9739100d7873f719dbd683de75.
def localCycle00181 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 3, .theta 1, .zero, .theta 4, .distance 3 4, .distance 3 5, .distance 5 6, .distance 4 5, .distance 1 4, .distance 1 3]
    constant := ![-1, 0, 0, 3, 0, -1, -1, -1, -2]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, false, false] }
  origin := ![.corridorLower 1 3, .thetaLower 1, .thetaUpper 4, .corridorUpper 3 4, .triangle 31 2, .triangle 33 0, .triangle 34 0, .triangle 22 0, .gapLower 1 2]

-- Cycle fingerprint 758716ccad9237240c7679a9ec728cfdf2679c184e1d4976dc97b0640baf426d.
def localCycle00182 : Cycle where
  length := 8
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 4, .distance 4 5, .distance 1 5, .distance 1 6, .distance 1 4, .distance 1 3, .theta 1]
    constant := ![4, 0, -1, 0, -2, 0, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, true, false, false] }
  origin := ![.gapLower 1 6, .triangle 2 2, .triangle 12 0, .triangle 22 2, .gapLower 1 4, .triangle 23 1, .gapLower 1 2, .corridorLower 1 3]

-- Cycle fingerprint 75d4de5640580d0f7b579f397aa176262bb6c009488e2a3d6f50e94cdc382e26.
def localCycle00183 : Cycle where
  length := 5
  data := {
    node := ![.distance 1 5, .distance 1 4, .distance 1 3, .theta 1, .distance 0 1, .distance 1 5]
    constant := ![0, -2, -1, 2, -1]
    coefficient := ![0, 0, 0, 1, 0]
    strict := ![true, false, false, false, false] }
  origin := ![.triangle 22 1, .gapLower 1 2, .corridorLower 1 3, .gapLower 1 6, .triangle 3 0]

-- Cycle fingerprint 75e4631cdd36576d47845123a61ddfa54b95fda22f798fd232dcad844d4d8723.
def localCycle00184 : Cycle where
  length := 7
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 3 5, .distance 2 3, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, -1, -1, -1, -2, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 33 0, .triangle 26 0, .triangle 15 0, .gapLower 1 0, .thetaLower 1]

-- Cycle fingerprint 7659fc9be1e009e6f5b0a0952660d900b8a218347c645d8e10621bcbe5c84652.
def localCycle00185 : Cycle where
  length := 8
  data := {
    node := ![.distance 3 4, .distance 2 3, .distance 1 2, .theta 1, .zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 4]
    constant := ![-1, -1, -2, 0, 0, 3, 0, -1]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, false, false, false, true, false] }
  origin := ![.triangle 25 0, .triangle 15 0, .gapLower 1 0, .thetaLower 1, .thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 0]

-- Cycle fingerprint 766ed4c78e3a994f69ac590f4f9e85006dd5ad386e8787b3778f43dce687f400.
def localCycle00186 : Cycle where
  length := 7
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 4, .distance 4 6, .distance 4 5, .distance 1 4, .distance 1 3, .theta 1]
    constant := ![2, 0, -1, 0, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, true, false] }
  origin := ![.gapLower 1 6, .triangle 2 2, .triangle 13 0, .triangle 34 1, .triangle 22 0, .triangle 19 1, .corridorLower 1 3]

-- Cycle fingerprint 76c633b4b9b2539c6c2919d0ae28e4a276b115cee7c6ee1745d4f6ea41d0d2d1.
def localCycle00187 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 5, .distance 5 6, .distance 1 5, .distance 1 4, .theta 1, .distance 0 1, .distance 0 5]
    constant := ![-1, -1, 0, -1, 1, 0]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![false, false, false, false, false, true] }
  origin := ![.triangle 14 0, .triangle 24 0, .gapLower 1 3, .corridorLower 1 4, .gapLower 1 6, .triangle 3 2]

-- Cycle fingerprint 77236d6af1163e1ea58535534ce07fdfffee09cfbbbe836934b4f508a6e1fcbc.
def localCycle00188 : Cycle where
  length := 6
  data := {
    node := ![.distance 1 2, .theta 1, .zero, .theta 6, .distance 1 6, .distance 1 5, .distance 1 2]
    constant := ![-2, 0, 0, 2, -2, 0]
    coefficient := ![0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, true, false, true] }
  origin := ![.gapLower 1 0, .thetaLower 1, .thetaUpper 6, .gapUpper 6 0, .gapLower 1 4, .triangle 17 1]

-- Cycle fingerprint 77b5fac0a59e2d49dd95fbd5b2bbb501cfb98722f97177e21c4b12ee947e8634.
def localCycle00189 : Cycle where
  length := 7
  data := {
    node := ![.theta 1, .distance 0 1, .distance 1 4, .distance 1 6, .distance 1 5, .distance 1 3, .distance 1 2, .theta 1]
    constant := ![2, -1, 0, 0, 0, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false] }
  origin := ![.gapLower 1 6, .triangle 2 0, .triangle 23 2, .triangle 24 1, .gapLower 1 2, .gapLower 1 1, .corridorLower 1 2]

-- Cycle fingerprint 77ca3b2b6d0cfc7d5217fdee0c02346ac835ede9be684ff260dd2a9ebac8dc12.
def localCycle00190 : Cycle where
  length := 6
  data := {
    node := ![.distance 1 2, .theta 1, .distance 0 1, .distance 1 5, .distance 1 6, .distance 1 4, .distance 1 2]
    constant := ![-2, 3, -1, 0, -2, 0]
    coefficient := ![0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true] }
  origin := ![.gapLower 1 0, .corridorUpper 0 1, .triangle 3 0, .triangle 24 2, .gapLower 1 3, .triangle 16 1]

-- Cycle fingerprint 78bdd04d644d55dd26cef1d94939704b3fdfb9bd1e4f8fc63adaa2a3a18e7601.
def localCycle00191 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 4 5, .distance 2 4, .distance 4 6, .distance 5 6, .distance 0 5, .theta 0, .zero]
    constant := ![0, 3, -1, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 31 0, .triangle 28 0, .triangle 29 0, .triangle 34 1, .triangle 14 0, .corridorLower 0 5, .thetaLower 0]

-- Cycle fingerprint 7a599a3c8311138c10d39ace607bfd4f1c70996723136750febcec32882724cb.
def localCycle00192 : Cycle where
  length := 8
  data := {
    node := ![.distance 4 5, .theta 4, .theta 3, .theta 2, .theta 1, .distance 0 1, .distance 1 4, .distance 4 6, .distance 4 5]
    constant := ![-1, 0, 0, 0, 2, -2, -1, 0]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![false, true, true, true, false, false, false, true] }
  origin := ![.corridorLower 4 5, .thetaNext 3, .thetaNext 2, .thetaNext 1, .gapLower 1 6, .gapLower 1 5, .triangle 23 0, .triangle 34 1]

-- Cycle fingerprint 7a97380a18b2db7726c182c42d9ab0f8803b841a4056016c8fcddf0a07ab89a6.
def localCycle00193 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 6, .distance 1 5, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1, .theta 0, .zero, .theta 6, .distance 1 6]
    constant := ![0, -2, 0, -2, -1, 0, 0, 0, 2]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1, 0]
    strict := ![true, false, true, false, false, true, false, false, true] }
  origin := ![.triangle 24 1, .gapLower 1 3, .triangle 19 1, .gapLower 1 1, .corridorLower 1 2, .thetaNext 0, .thetaLower 0, .thetaUpper 6, .gapUpper 6 0]

-- Cycle fingerprint 7ae405a6e9b0f59c9358d551a19dc946921350d8ef021fb2148e68317f0cf170.
def localCycle00194 : Cycle where
  length := 9
  data := {
    node := ![.theta 1, .distance 0 1, .distance 1 4, .distance 1 5, .distance 5 6, .distance 4 5, .theta 4, .theta 3, .theta 2, .theta 1]
    constant := ![3, -1, 0, -1, -1, -1, 0, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, true, true, true] }
  origin := ![.corridorUpper 0 1, .triangle 2 0, .triangle 22 2, .triangle 24 0, .triangle 34 0, .corridorLower 4 5, .thetaNext 3, .thetaNext 2, .thetaNext 1]

-- Cycle fingerprint 7b2011fa748549f54ab8630f02abf00b1e2fce5a727b6635e9ff9a19fb0b57c0.
def localCycle00195 : Cycle where
  length := 6
  data := {
    node := ![.distance 1 3, .distance 1 2, .theta 1, .distance 0 1, .distance 1 5, .distance 1 6, .distance 1 3]
    constant := ![-2, -1, 3, -1, -2, 0]
    coefficient := ![0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, true] }
  origin := ![.gapLower 1 1, .corridorLower 1 2, .corridorUpper 0 1, .triangle 3 0, .gapLower 1 4, .triangle 21 1]

-- Cycle fingerprint 7b2def11da7c61e7c2529bb9e8098e60404f0bb8533268f2946ee0bb9b830c3d.
def localCycle00196 : Cycle where
  length := 9
  data := {
    node := ![.distance 2 3, .distance 1 2, .theta 1, .zero, .theta 4, .distance 3 4, .distance 4 5, .distance 4 6, .distance 2 4, .distance 2 3]
    constant := ![-1, -3, 0, 0, 3, -1, 0, -1, 0]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, false, false] }
  origin := ![.triangle 15 0, .gapLower 1 0, .thetaLower 1, .thetaUpper 4, .corridorUpper 3 4, .triangle 31 0, .triangle 34 2, .triangle 29 0, .gapLower 2 3]

-- Cycle fingerprint 7bd5a92605492ad3fb9b93c76a50d9e50ef2b7f39792e514ae13739fa4a21863.
def localCycle00197 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 2, .theta 1, .zero, .theta 6, .distance 5 6, .distance 4 6, .distance 0 4, .distance 4 5, .distance 1 4, .distance 1 3, .distance 1 2]
    constant := ![-2, 0, 0, 3, 0, -1, -1, -1, -2, 0]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, false, false, true] }
  origin := ![.gapLower 1 0, .thetaLower 1, .thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 13 0, .triangle 12 0, .triangle 22 0, .gapLower 1 2, .triangle 15 1]

-- Cycle fingerprint 7c13259e8efefcd8369b052ff4523756e6fedd31effe1932e49fda4ecc9a6f3c.
def localCycle00198 : Cycle where
  length := 10
  data := {
    node := ![.theta 4, .distance 4 6, .distance 3 6, .distance 2 6, .distance 1 6, .distance 0 1, .distance 1 2, .distance 2 3, .distance 3 4, .distance 4 5, .theta 4]
    constant := ![4, 0, 0, 0, -1, -1, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, false, false, false, false, false] }
  origin := ![.gapLower 4 6, .triangle 32 2, .triangle 27 2, .triangle 18 2, .triangle 4 0, .triangle 0 0, .triangle 15 0, .triangle 25 0, .triangle 31 0, .corridorLower 4 5]

-- Cycle fingerprint 7c44682d38844d59f025a1966b72e4f0df2047c81c92e7f3877200eee3206821.
def localCycle00199 : Cycle where
  length := 5
  data := {
    node := ![.theta 4, .distance 3 4, .distance 4 6, .distance 2 4, .distance 4 5, .theta 4]
    constant := ![3, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 32 0, .triangle 29 0, .triangle 28 0, .corridorLower 4 5]

-- Cycle fingerprint 7c8a1f6a5cc1cd65232b11ee1a648b569c6242dabe4cbacbafed1afe3cdfa2c8.
def localCycle00200 : Cycle where
  length := 11
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 2 5, .distance 5 6, .distance 4 5, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1, .zero, .theta 4]
    constant := ![3, 0, 0, -1, -1, -1, -2, 0, -2, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, true, false, false, false, false, true, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 28 2, .triangle 30 0, .triangle 34 0, .triangle 22 0, .gapLower 1 2, .triangle 15 1, .gapLower 1 0, .thetaLower 1, .thetaUpper 4]

-- Cycle fingerprint 7c9819791ded06f8dc12c455a696bc05c8b323ac8b5886dd6bcd9b5de7a298ed.
def localCycle00201 : Cycle where
  length := 12
  data := {
    node := ![.theta 4, .distance 3 4, .distance 3 5, .distance 5 6, .distance 4 6, .distance 0 4, .distance 4 5, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1, .zero, .theta 4]
    constant := ![3, 0, -1, 0, -1, -1, -1, 0, 0, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, false, true, false, false, false, false, true, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 31 2, .triangle 33 0, .triangle 34 2, .triangle 13 0, .triangle 12 0, .triangle 22 0, .gapLower 1 2, .triangle 15 1, .corridorLower 1 2, .thetaLower 1, .thetaUpper 4]

-- Cycle fingerprint 7d2a19cbb47ed4982bf8a488f8fb0a6d5425b14d61a509dfa215ff7aa6fe1e16.
def localCycle00202 : Cycle where
  length := 8
  data := {
    node := ![.theta 6, .distance 1 6, .distance 1 5, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1, .zero, .theta 6]
    constant := ![2, 0, 0, 0, -3, -1, 0, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![true, true, true, true, false, false, false, false] }
  origin := ![.gapUpper 6 0, .triangle 24 1, .triangle 22 1, .triangle 19 1, .gapLower 1 1, .corridorLower 1 2, .thetaLower 1, .thetaUpper 6]

-- Cycle fingerprint 7e22910268efce15e37226e39b9a03775a57eeb8b909cd0e4ff0e4308ecb3df1.
def localCycle00203 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 5, .distance 5 6, .theta 5, .theta 4, .distance 3 4, .distance 4 5, .distance 2 5, .theta 2, .theta 1, .distance 0 1, .distance 1 5]
    constant := ![-1, -1, 0, 3, -1, 0, -2, 0, 1, -1]
    coefficient := ![0, 0, 0, 1, 0, 0, -1, 0, 1, 0]
    strict := ![false, false, true, false, false, false, true, true, false, false] }
  origin := ![.triangle 24 0, .corridorLower 5 6, .thetaNext 4, .corridorUpper 3 4, .triangle 31 0, .gapLower 5 4, .gapUpper 2 6, .thetaNext 1, .gapLower 1 6, .triangle 3 0]

-- Cycle fingerprint 7e641a7693f361b1d97e8b3044b51cdd7437d61c0fe80958c87fe7d3e1068eef.
def localCycle00204 : Cycle where
  length := 9
  data := {
    node := ![.theta 1, .zero, .theta 4, .distance 3 4, .distance 4 5, .distance 5 6, .distance 1 5, .distance 1 4, .distance 1 3, .theta 1]
    constant := ![0, 0, 3, -1, -1, -1, 0, -2, -1]
    coefficient := ![0, 1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false, false] }
  origin := ![.thetaLower 1, .thetaUpper 4, .corridorUpper 3 4, .triangle 31 0, .triangle 34 0, .triangle 24 0, .gapLower 1 3, .gapLower 1 2, .corridorLower 1 3]

-- Cycle fingerprint 7e88b1e4b6928dd6a7de1002a53cb88d23bde80d6d09e4a201569a55ebfa504b.
def localCycle00205 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 3, .distance 1 2, .theta 1, .zero, .theta 4, .distance 3 4, .distance 4 5, .distance 5 6, .distance 1 5, .distance 1 4, .distance 1 3]
    constant := ![0, -1, 0, 0, 3, -1, -1, -1, -2, -2]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![true, false, false, false, false, false, false, false, false, false] }
  origin := ![.triangle 15 1, .corridorLower 1 2, .thetaLower 1, .thetaUpper 4, .corridorUpper 3 4, .triangle 31 0, .triangle 34 0, .triangle 24 0, .gapLower 1 3, .gapLower 1 2]

-- Cycle fingerprint 7e91d33d72cd50bd55c310c5785b26aa7ccc0a52bfc2948352f2a77fddc65cbe.
def localCycle00206 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 3, .theta 1, .zero, .theta 6, .distance 5 6, .distance 4 6, .distance 0 4, .distance 4 5, .distance 1 5, .distance 1 4, .distance 1 3]
    constant := ![-1, 0, 0, 3, 0, -1, -1, 0, -2, -2]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, true, false, false] }
  origin := ![.corridorLower 1 3, .thetaLower 1, .thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 13 0, .triangle 12 0, .triangle 22 2, .gapLower 1 3, .gapLower 1 2]

-- Cycle fingerprint 7ed3322de65c476be9e83dc701da2ab07df6411f57c0941f57f0509dcd689c6f.
def localCycle00207 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 4, .distance 1 3, .distance 1 2, .theta 1, .distance 0 1, .distance 0 4, .distance 4 5, .distance 1 4]
    constant := ![-2, 0, -2, 3, 0, -1, -1]
    coefficient := ![0, 0, 0, 1, 0, 0, 0]
    strict := ![false, true, false, false, true, false, false] }
  origin := ![.gapLower 1 2, .triangle 15 1, .gapLower 1 0, .corridorUpper 0 1, .triangle 2 2, .triangle 12 0, .triangle 22 0]

-- Cycle fingerprint 7f2f3bd70286c37199f4c5877255133ac87fdf8c87038b41e3f3d0c3071776d4.
def localCycle00208 : Cycle where
  length := 16
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 2 6, .distance 1 6, .distance 0 1, .distance 1 2, .distance 1 3, .distance 1 4, .distance 4 5, .distance 3 5, .distance 2 3, .distance 3 4, .theta 3, .zero]
    constant := ![0, 3, 0, 0, 0, 0, -1, -1, 0, 0, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, true, true, false, false, true, true, false, true, false, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 27 2, .triangle 18 2, .triangle 4 0, .triangle 0 0, .triangle 15 2, .triangle 19 2, .triangle 22 0, .triangle 31 2, .triangle 26 0, .triangle 25 0, .corridorLower 3 4, .thetaLower 3]

-- Cycle fingerprint 804a19b92781c58d5e41050d8c0014c5d550600d61f23ac40e5ddd95291ad2af.
def localCycle00209 : Cycle where
  length := 9
  data := {
    node := ![.theta 1, .zero, .theta 6, .distance 5 6, .distance 4 6, .distance 2 4, .distance 4 5, .distance 1 4, .distance 1 3, .theta 1]
    constant := ![0, 0, 3, 0, -1, -1, -1, -2, -1]
    coefficient := ![0, 1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, false, false] }
  origin := ![.thetaLower 1, .thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 29 0, .triangle 28 0, .triangle 22 0, .gapLower 1 2, .corridorLower 1 3]

-- Cycle fingerprint 80a1231f5cd2d856752f924be872877a8ce3a0cc797f22a05ffc0ca7b8a0c788.
def localCycle00210 : Cycle where
  length := 12
  data := {
    node := ![.distance 4 5, .distance 1 4, .distance 1 3, .theta 1, .distance 0 1, .distance 1 5, .distance 5 6, .theta 5, .theta 4, .distance 3 4, .distance 2 4, .distance 0 4, .distance 4 5]
    constant := ![-1, 0, -1, 3, -3, -1, -1, 0, 3, 0, 0, -1]
    coefficient := ![0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false, true, false, true, true, false] }
  origin := ![.triangle 22 0, .triangle 19 1, .corridorLower 1 3, .corridorUpper 0 1, .gapLower 1 5, .triangle 24 0, .corridorLower 5 6, .thetaNext 4, .corridorUpper 3 4, .triangle 25 2, .triangle 6 2, .triangle 12 0]

-- Cycle fingerprint 80a7976cd090a254d5fd9642082c58933985bad57c6263f057b3fab02fcef0a7.
def localCycle00211 : Cycle where
  length := 5
  data := {
    node := ![.theta 1, .zero, .theta 6, .distance 1 6, .distance 1 5, .theta 1]
    constant := ![0, 0, 2, -3, -1]
    coefficient := ![0, 1, 0, 0, 0]
    strict := ![false, false, true, false, false] }
  origin := ![.thetaLower 1, .thetaUpper 6, .gapUpper 6 0, .gapLower 1 4, .corridorLower 1 5]

-- Cycle fingerprint 80b64f93d5ab6fb541c4e0aed54cb0ffeb47e63308aea6240181e6678517d932.
def localCycle00212 : Cycle where
  length := 14
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 2 6, .distance 1 6, .distance 0 1, .distance 1 2, .distance 1 3, .distance 3 5, .distance 2 3, .distance 3 4, .theta 3, .zero]
    constant := ![0, 3, 0, 0, 0, 0, -1, -1, 0, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, true, true, false, false, true, false, false, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 27 2, .triangle 18 2, .triangle 4 0, .triangle 0 0, .triangle 15 2, .triangle 20 0, .triangle 26 0, .triangle 25 0, .corridorLower 3 4, .thetaLower 3]

-- Cycle fingerprint 81343619877afd78519b3e008fa7e9c90ef43e615d6f22cbdb27312077535758.
def localCycle00213 : Cycle where
  length := 9
  data := {
    node := ![.theta 1, .distance 0 1, .distance 1 5, .distance 5 6, .theta 5, .distance 4 5, .distance 3 4, .distance 2 3, .distance 1 2, .theta 1]
    constant := ![3, -2, -1, -1, 3, -1, -1, -1, -2]
    coefficient := ![1, 0, 0, 0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false, false] }
  origin := ![.corridorUpper 0 1, .gapLower 1 5, .triangle 24 0, .corridorLower 5 6, .corridorUpper 4 5, .triangle 31 0, .triangle 25 0, .triangle 15 0, .gapLower 1 0]

-- Cycle fingerprint 81427d2c78f03357e25cb8b2c043c7a1e3b435cde1d8656cc1b5fb9f6de8aae7.
def localCycle00214 : Cycle where
  length := 3
  data := {
    node := ![.theta 1, .distance 0 1, .distance 1 4, .theta 1]
    constant := ![3, -3, -1]
    coefficient := ![1, 0, 0]
    strict := ![false, false, false] }
  origin := ![.corridorUpper 0 1, .gapLower 1 5, .corridorLower 1 4]

-- Cycle fingerprint 830f1b7cf0ec3d0b0bdc5915b0ce4fbdf674a9915f9df14cd707daa994a4ddec.
def localCycle00215 : Cycle where
  length := 11
  data := {
    node := ![.distance 3 4, .distance 2 4, .distance 4 5, .distance 5 6, .distance 1 5, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1, .zero, .theta 4, .distance 3 4]
    constant := ![0, -1, -1, -1, 0, 0, -2, -2, 0, 0, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1]
    strict := ![true, false, false, false, false, true, false, false, false, false, false] }
  origin := ![.triangle 25 2, .triangle 28 0, .triangle 34 0, .triangle 24 0, .gapLower 1 3, .triangle 19 1, .gapLower 1 1, .gapLower 1 0, .thetaLower 1, .thetaUpper 4, .corridorUpper 3 4]

-- Cycle fingerprint 83194e16f3e419d0aa25b2597dcc3ff6a40dffd1404fd72b0c26b97a7a6bdf2c.
def localCycle00216 : Cycle where
  length := 10
  data := {
    node := ![.theta 4, .distance 3 4, .distance 4 5, .distance 2 5, .distance 5 6, .distance 1 5, .distance 1 4, .theta 1, .theta 0, .zero, .theta 4]
    constant := ![3, -1, 0, -1, -1, -2, -1, 0, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![false, false, true, false, false, false, false, true, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 31 0, .triangle 28 2, .triangle 30 0, .triangle 24 0, .gapLower 1 3, .corridorLower 1 4, .thetaNext 0, .thetaLower 0, .thetaUpper 4]

-- Cycle fingerprint 832ccd34c14d2048bbbdee92eec832163b6b0743452e03786f1cf306632b8c1d.
def localCycle00217 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 4 5, .distance 1 5, .distance 1 6, .distance 1 4, .distance 1 3, .theta 1, .distance 0 1]
    constant := ![0, -1, 0, 0, -2, -2, -1, 4]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![true, false, true, true, false, false, false, false] }
  origin := ![.triangle 2 2, .triangle 12 0, .triangle 22 2, .triangle 24 2, .gapLower 1 3, .gapLower 1 2, .corridorLower 1 3, .gapLower 1 6]

-- Cycle fingerprint 8384927893ed02164c671a15433732f062c5740aa78983b0f7eb850a810f6658.
def localCycle00218 : Cycle where
  length := 11
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 4 5, .distance 5 6, .distance 1 5, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1, .zero, .theta 4]
    constant := ![3, 0, -1, -1, -1, 0, -2, 0, -2, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, false, false, false, false, false, true, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 28 0, .triangle 34 0, .triangle 24 0, .gapLower 1 3, .gapLower 1 2, .triangle 15 1, .gapLower 1 0, .thetaLower 1, .thetaUpper 4]

-- Cycle fingerprint 84817e718f1b6ad422ff351542a4f4ccee51c78935d4c35255cea623c08e64b5.
def localCycle00219 : Cycle where
  length := 6
  data := {
    node := ![.distance 1 6, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1, .distance 0 1, .distance 1 6]
    constant := ![-2, 0, 0, -1, 2, -1]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![false, true, true, false, false, false] }
  origin := ![.gapLower 1 4, .triangle 19 1, .triangle 15 1, .corridorLower 1 2, .gapLower 1 6, .triangle 4 0]

-- Cycle fingerprint 84a6f82e2c5f1dbc6892ac91a536738d59c02c20fce3deb55b9f615280050e51.
def localCycle00220 : Cycle where
  length := 6
  data := {
    node := ![.distance 1 6, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1, .distance 0 1, .distance 1 6]
    constant := ![0, 0, 0, -2, 2, -1]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![true, true, true, false, false, false] }
  origin := ![.triangle 23 1, .triangle 19 1, .triangle 15 1, .gapLower 1 0, .gapLower 1 6, .triangle 4 0]

-- Cycle fingerprint 84f316731276eacd2fcb5f7e4f75a64207b69c85730d22ff24e75ad6e275dd3b.
def localCycle00221 : Cycle where
  length := 10
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 4 5, .distance 5 6, .distance 1 5, .distance 1 4, .distance 1 3, .theta 1, .zero, .theta 4]
    constant := ![3, 0, -1, -1, -1, 0, -2, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, false, false, false, true, false, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 28 0, .triangle 34 0, .triangle 24 0, .triangle 22 1, .gapLower 1 2, .corridorLower 1 3, .thetaLower 1, .thetaUpper 4]

-- Cycle fingerprint 84f58e864092b7d443071c11f8a64cb51addcaef32ec9ff2bd64527d9012f3ca.
def localCycle00222 : Cycle where
  length := 6
  data := {
    node := ![.distance 4 5, .distance 5 6, .distance 1 5, .distance 1 4, .theta 4, .distance 3 4, .distance 4 5]
    constant := ![-1, -1, -2, 0, 3, -1]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.triangle 34 0, .triangle 24 0, .gapLower 1 3, .gapLower 4 0, .corridorUpper 3 4, .triangle 31 0]

-- Cycle fingerprint 85b4190868325e7b091e8c9f6d7d86419c5996d3d32921365ccc2f4516e0aa99.
def localCycle00223 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 5, .distance 5 6, .distance 1 5, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1, .distance 0 1]
    constant := ![0, -1, -1, 0, -2, -2, -1, 4]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![true, false, false, true, false, false, false, false] }
  origin := ![.triangle 3 2, .triangle 14 0, .triangle 24 0, .triangle 22 1, .gapLower 1 2, .gapLower 1 1, .corridorLower 1 2, .gapLower 1 6]

-- Cycle fingerprint 862abae2cc39da018b23b386cfd91ef21edcf336c55033feaad805bf203e5a0a.
def localCycle00224 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 0 4, .distance 4 5, .distance 1 5, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, 0, -1, -1, 0, -2, 0, -2, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, false, true, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 13 0, .triangle 12 0, .triangle 22 2, .gapLower 1 3, .triangle 19 1, .gapLower 1 1, .corridorLower 1 2, .thetaLower 1]

-- Cycle fingerprint 8641ba6f8cc8c8b39f8cbc03c1091d0206d7e052790d33206262bf356ff24322.
def localCycle00225 : Cycle where
  length := 5
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 4, .distance 3 6, .theta 6, .theta 5]
    constant := ![3, -1, 0, -2, 0]
    coefficient := ![1, 0, 0, -1, 0]
    strict := ![false, false, true, true, true] }
  origin := ![.corridorUpper 4 5, .triangle 31 0, .triangle 32 2, .gapUpper 6 6, .thetaNext 5]

-- Cycle fingerprint 86bef04538bb77a1fcd2dc42b2226703e9269b3a876a8a89aa4047fd85954e1b.
def localCycle00226 : Cycle where
  length := 5
  data := {
    node := ![.theta 4, .distance 3 4, .distance 4 5, .distance 0 4, .distance 4 6, .theta 4]
    constant := ![3, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 31 0, .triangle 12 0, .triangle 13 0, .corridorLower 4 6]

-- Cycle fingerprint 86ce54513255824313cbcb0b3118c9e5bac8d6975527e0f458241b4074e27b2b.
def localCycle00227 : Cycle where
  length := 11
  data := {
    node := ![.theta 4, .distance 3 4, .distance 3 5, .distance 5 6, .distance 4 5, .distance 0 5, .distance 1 5, .distance 1 4, .distance 1 2, .theta 1, .zero, .theta 4]
    constant := ![3, 0, -1, -1, 0, 0, -2, 0, -2, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, false, false, false, true, false, true, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 31 2, .triangle 33 0, .triangle 34 0, .gapLower 5 2, .triangle 3 1, .gapLower 1 3, .triangle 16 1, .gapLower 1 0, .thetaLower 1, .thetaUpper 4]

-- Cycle fingerprint 876b495898da0aee2667ebb8d9211a01d6fe1b6488556d6d590a4fcfb4c27ba6.
def localCycle00228 : Cycle where
  length := 5
  data := {
    node := ![.distance 1 3, .distance 1 2, .theta 1, .distance 0 1, .distance 1 5, .distance 1 3]
    constant := ![-2, -1, 3, -2, 0]
    coefficient := ![0, 0, 1, 0, 0]
    strict := ![false, false, false, false, true] }
  origin := ![.gapLower 1 1, .corridorLower 1 2, .corridorUpper 0 1, .gapLower 1 5, .triangle 20 1]

-- Cycle fingerprint 879ad0d4c0aaf43e71d3013b20a9d0a8fb47a91b533237e094b69a4613632bd6.
def localCycle00229 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 2, .theta 1, .zero, .theta 6, .distance 5 6, .distance 4 6, .distance 0 4, .distance 4 5, .distance 1 5, .distance 1 4, .distance 1 2]
    constant := ![-2, 0, 0, 3, 0, -1, -1, 0, -2, 0]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, true, false, true] }
  origin := ![.gapLower 1 0, .thetaLower 1, .thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 13 0, .triangle 12 0, .triangle 22 2, .gapLower 1 3, .triangle 16 1]

-- Cycle fingerprint 884badf767322ce7cdaa61abd400d34356b9ace7f7b39f24fc2270dbea38bf4f.
def localCycle00230 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 6, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1, .distance 0 1, .distance 1 5, .distance 1 6]
    constant := ![-2, 0, 0, -2, 3, -1, 0]
    coefficient := ![0, 0, 0, 0, 1, 0, 0]
    strict := ![false, true, true, false, false, false, true] }
  origin := ![.gapLower 1 3, .triangle 19 1, .triangle 15 1, .gapLower 1 0, .corridorUpper 0 1, .triangle 3 0, .triangle 24 2]

-- Cycle fingerprint 8875a025ad420c8302a44f222defcca71d37c6e4880469e59a539ac79736eca9.
def localCycle00231 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 4, .distance 1 5, .distance 1 3, .distance 1 2, .theta 1, .theta 0, .zero, .theta 6, .distance 1 6, .distance 1 4]
    constant := ![0, -2, -2, -1, 0, 0, 0, 2, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 0, 0]
    strict := ![true, false, false, false, true, false, false, true, true] }
  origin := ![.triangle 22 2, .gapLower 1 2, .gapLower 1 1, .corridorLower 1 2, .thetaNext 0, .thetaLower 0, .thetaUpper 6, .gapUpper 6 0, .triangle 23 1]

-- Cycle fingerprint 8880090a011db507eaa7f4b1fbcfe3f90d63838000df9de17736a75c88400865.
def localCycle00232 : Cycle where
  length := 4
  data := {
    node := ![.theta 1, .distance 0 1, .distance 1 6, .distance 1 5, .theta 1]
    constant := ![2, -1, -2, -1]
    coefficient := ![1, 0, 0, 0]
    strict := ![false, false, false, false] }
  origin := ![.gapLower 1 6, .triangle 4 0, .gapLower 1 4, .corridorLower 1 5]

-- Cycle fingerprint 899744bbb0e0d98ce0db43c48a35fc74a75b6faea78a32b1a5c522d9cb4d368f.
def localCycle00233 : Cycle where
  length := 11
  data := {
    node := ![.distance 5 6, .distance 1 5, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1, .zero, .theta 4, .distance 3 4, .distance 2 4, .distance 4 5, .distance 5 6]
    constant := ![-1, 0, 0, -2, -1, 0, 0, 3, 0, -1, -1]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false, true, false, false] }
  origin := ![.triangle 24 0, .gapLower 1 3, .triangle 19 1, .gapLower 1 1, .corridorLower 1 2, .thetaLower 1, .thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 28 0, .triangle 34 0]

-- Cycle fingerprint 89b7fccacd29916c318f2495e401a00c7c668188114cf853f96143bfbc586e38.
def localCycle00234 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 5, .distance 5 6, .distance 1 5, .distance 1 4, .theta 1, .distance 0 1, .distance 0 5]
    constant := ![-1, -1, -2, -1, 2, 0]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![false, false, false, false, false, true] }
  origin := ![.triangle 14 0, .triangle 24 0, .gapLower 1 3, .corridorLower 1 4, .gapLower 1 6, .triangle 3 2]

-- Cycle fingerprint 8b9c184d6a130831dce2904b50e5e2d332a7d0344cbff9bfa19e4f6766349b77.
def localCycle00235 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 5, .distance 1 3, .distance 1 2, .theta 1, .distance 0 1, .distance 1 4, .distance 1 6, .distance 1 5]
    constant := ![-3, 0, -1, 3, -1, 0, 0]
    coefficient := ![0, 0, 0, 1, 0, 0, 0]
    strict := ![false, true, false, false, false, true, true] }
  origin := ![.gapLower 1 2, .triangle 15 1, .corridorLower 1 2, .corridorUpper 0 1, .triangle 2 0, .triangle 23 2, .triangle 24 1]

-- Cycle fingerprint 8c25530d378da2596e7c732930e6335feb8c73c05911c36eca6e643c28e04ce5.
def localCycle00236 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 6, .distance 1 6, .distance 1 5, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1, .zero]
    constant := ![0, 2, 0, 0, -2, -2, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, false, false, false] }
  origin := ![.thetaUpper 6, .gapUpper 6 0, .triangle 24 1, .triangle 22 1, .gapLower 1 2, .gapLower 1 1, .corridorLower 1 2, .thetaLower 1]

-- Cycle fingerprint 8cb95db2f9d934e8fdd429ada131a1bfd99c6a4c1ffdc7f028e163cd2748dace.
def localCycle00237 : Cycle where
  length := 3
  data := {
    node := ![.distance 1 6, .theta 1, .distance 0 1, .distance 1 6]
    constant := ![-1, 2, -2]
    coefficient := ![0, 1, 0]
    strict := ![false, false, false] }
  origin := ![.corridorLower 1 6, .gapLower 1 6, .gapLower 1 5]

-- Cycle fingerprint 8ceb54ad28dbcf3a26057101d111ec29d6597fdfbc75fca532758b5b124a0e9c.
def localCycle00238 : Cycle where
  length := 7
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 5, .distance 5 6, .distance 1 5, .distance 1 4, .distance 1 3, .theta 1]
    constant := ![2, 0, -1, -1, 0, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false] }
  origin := ![.gapLower 1 6, .triangle 3 2, .triangle 14 0, .triangle 24 0, .gapLower 1 3, .gapLower 1 2, .corridorLower 1 3]

-- Cycle fingerprint 8d39372ad21de445e74e1b9288cf4203101f15223aadb26cbf41dc63d9c352ec.
def localCycle00239 : Cycle where
  length := 6
  data := {
    node := ![.distance 1 2, .theta 1, .distance 0 1, .distance 1 5, .distance 1 4, .distance 1 3, .distance 1 2]
    constant := ![-1, 3, -1, 0, -2, -2]
    coefficient := ![0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false] }
  origin := ![.corridorLower 1 2, .corridorUpper 0 1, .triangle 3 0, .triangle 22 1, .gapLower 1 2, .gapLower 1 1]

-- Cycle fingerprint 8d9c3eb4c95705bb6aaf7bf3d8c95a3c69fca88717ffee73fa3d21d2dca7ffbf.
def localCycle00240 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 3, .distance 3 6, .distance 5 6, .distance 4 6, .distance 1 4, .distance 4 5, .theta 4]
    constant := ![3, -1, -1, 0, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 0, .triangle 27 0, .triangle 33 1, .triangle 34 2, .triangle 23 0, .triangle 22 0, .corridorLower 4 5]

-- Cycle fingerprint 8e7264ebafd39d70ab5912f14015d13bb10b7d54c1bd4d479a40e89e1d3fdd73.
def localCycle00241 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 2, .theta 1, .zero, .theta 6, .distance 5 6, .distance 4 6, .distance 0 4, .distance 4 5, .distance 1 4, .distance 1 3, .distance 1 2]
    constant := ![-1, 0, 0, 3, 0, -1, -1, -1, -2, -2]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, false, false, false] }
  origin := ![.corridorLower 1 2, .thetaLower 1, .thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 13 0, .triangle 12 0, .triangle 22 0, .gapLower 1 2, .gapLower 1 1]

-- Cycle fingerprint 8eb1865e034c9a292445901e623850874a1fbaa22909a734aa8b9ba19e9f9d86.
def localCycle00242 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 4, .distance 4 6, .distance 4 5, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1, .distance 0 1, .distance 0 4]
    constant := ![-1, 0, -1, 0, -2, -2, 3, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 0]
    strict := ![false, true, false, false, false, false, false, true] }
  origin := ![.triangle 13 0, .triangle 34 1, .triangle 22 0, .gapLower 1 2, .gapLower 1 1, .gapLower 1 0, .corridorUpper 0 1, .triangle 2 2]

-- Cycle fingerprint 8f1f066a607a0be9b80d13ee14be43a7c4403ee627599ddf44ef40c79b5f393b.
def localCycle00243 : Cycle where
  length := 8
  data := {
    node := ![.distance 4 5, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1, .distance 0 1, .distance 0 4, .distance 4 6, .distance 4 5]
    constant := ![-1, 0, 0, -1, 2, 0, -1, 0]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![false, false, true, false, false, true, false, true] }
  origin := ![.triangle 22 0, .gapLower 1 2, .triangle 15 1, .corridorLower 1 2, .gapLower 1 6, .triangle 2 2, .triangle 13 0, .triangle 34 1]

-- Cycle fingerprint 90b71747b3907efa42dc35f5d8b40bcc46cec9b310deab3097205c3be8f4ad42.
def localCycle00244 : Cycle where
  length := 8
  data := {
    node := ![.theta 1, .theta 0, .zero, .theta 6, .distance 1 6, .distance 1 4, .distance 1 5, .distance 1 3, .theta 1]
    constant := ![0, 0, 0, 2, -2, 0, -2, -1]
    coefficient := ![0, 0, 1, 0, 0, 0, 0, 0]
    strict := ![true, false, false, true, false, true, false, false] }
  origin := ![.thetaNext 0, .thetaLower 0, .thetaUpper 6, .gapUpper 6 0, .gapLower 1 4, .triangle 22 2, .gapLower 1 2, .corridorLower 1 3]

-- Cycle fingerprint 912ab15af976fb53ebdea86db36bcf1d5118c61a782a5b39e8217c1fe2516e10.
def localCycle00245 : Cycle where
  length := 9
  data := {
    node := ![.theta 1, .distance 0 1, .distance 1 4, .distance 4 5, .distance 5 6, .theta 5, .theta 4, .theta 3, .theta 2, .theta 1]
    constant := ![3, -1, -1, -1, -1, 0, 0, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, true, true] }
  origin := ![.corridorUpper 0 1, .triangle 2 0, .triangle 22 0, .triangle 34 0, .corridorLower 5 6, .thetaNext 4, .thetaNext 3, .thetaNext 2, .thetaNext 1]

-- Cycle fingerprint 91af99b5bc66b86d03535ea2724edbd81b65928d81920b30c95dfd4051e59187.
def localCycle00246 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 5 6, .distance 3 5, .distance 3 4, .distance 2 3, .distance 1 2, .theta 1, .theta 0, .zero]
    constant := ![0, 3, -1, -1, 0, -1, -1, -1, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, false, true, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 34 0, .triangle 33 0, .triangle 31 1, .triangle 25 0, .triangle 15 0, .corridorLower 1 2, .thetaNext 0, .thetaLower 0]

-- Cycle fingerprint 93414166f86daeaa195e2342a4abaae1d4da762fe8b0629be8ad4b6c89e39027.
def localCycle00247 : Cycle where
  length := 8
  data := {
    node := ![.distance 1 5, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1, .distance 0 1, .distance 0 5, .distance 5 6, .distance 1 5]
    constant := ![0, 0, -2, -1, 2, 0, -1, -1]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![false, true, false, false, false, true, false, false] }
  origin := ![.gapLower 1 3, .triangle 19 1, .gapLower 1 1, .corridorLower 1 2, .gapLower 1 6, .triangle 3 2, .triangle 14 0, .triangle 24 0]

-- Cycle fingerprint 935ebe763e61a18bdc6bd3e5c64bc94544015eb7f724e1b4ded9650e063a633c.
def localCycle00248 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 5, .distance 3 4, .distance 2 3, .distance 1 2, .theta 1, .theta 0, .zero]
    constant := ![0, 3, -1, -1, -1, -1, -1, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, true, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 0, .triangle 31 0, .triangle 25 0, .triangle 15 0, .corridorLower 1 2, .thetaNext 0, .thetaLower 0]

-- Cycle fingerprint 938efa9cd2c4130c5fbac5be372a610ef7d1e3b8f5274141ba466223cf408213.
def localCycle00249 : Cycle where
  length := 8
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 5, .distance 5 6, .distance 1 5, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1]
    constant := ![3, 0, -1, -1, -3, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, true, true, false] }
  origin := ![.corridorUpper 0 1, .triangle 3 2, .triangle 14 0, .triangle 24 0, .gapLower 1 3, .triangle 19 1, .triangle 15 1, .corridorLower 1 2]

-- Cycle fingerprint 9401df9f55a7e1dc97343f310fc54546b694684a2f69801677109f4b9f176781.
def localCycle00250 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 4, .distance 4 6, .distance 2 4, .distance 2 3, .distance 0 2, .distance 1 2, .theta 1, .theta 0, .zero]
    constant := ![0, 3, -1, -1, -1, 0, -1, 0, -1, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, true, false, true, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 0, .triangle 32 0, .triangle 29 0, .triangle 25 1, .triangle 5 0, .triangle 0 1, .corridorLower 1 2, .thetaNext 0, .thetaLower 0]

-- Cycle fingerprint 95cc6f205af33f9188bf7736ad9f84c1b8c5084d3ecc40cabfd7f4fd12000260.
def localCycle00251 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 6, .distance 1 5, .distance 1 4, .theta 1, .distance 0 1, .distance 0 4, .distance 4 6, .distance 1 6]
    constant := ![-2, -2, -1, 4, 0, -1, 0]
    coefficient := ![0, 0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, false, true, false, true] }
  origin := ![.gapLower 1 4, .gapLower 1 3, .corridorLower 1 4, .gapLower 1 6, .triangle 2 2, .triangle 13 0, .triangle 23 2]

-- Cycle fingerprint 95ea25f447289f83cb18b1be63d43c88d9ed1e27ef9e1b106334fb3a8c933620.
def localCycle00252 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 6, .distance 1 5, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1, .distance 0 1, .distance 0 4, .distance 4 6, .distance 1 6]
    constant := ![0, -2, 0, -2, -1, 4, 0, -1, 0]
    coefficient := ![0, 0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![true, false, true, false, false, false, true, false, true] }
  origin := ![.triangle 24 1, .gapLower 1 3, .triangle 19 1, .gapLower 1 1, .corridorLower 1 2, .gapLower 1 6, .triangle 2 2, .triangle 13 0, .triangle 23 2]

-- Cycle fingerprint 9676868dcc1b4563fa3922c6d792c979c94f4d76dc09fca447259701a82fa639.
def localCycle00253 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 2, .theta 1, .zero, .theta 4, .distance 3 4, .distance 4 5, .distance 5 6, .distance 1 5, .distance 1 4, .distance 1 3, .distance 1 2]
    constant := ![-2, 0, 0, 3, -1, -1, -1, 0, -2, 0]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false, false, true] }
  origin := ![.gapLower 1 0, .thetaLower 1, .thetaUpper 4, .corridorUpper 3 4, .triangle 31 0, .triangle 34 0, .triangle 24 0, .gapLower 1 3, .gapLower 1 2, .triangle 15 1]

-- Cycle fingerprint 97de4fc0e94c305c014ac99e0012ea1133aad56fe2b225c507ac6675a603c55e.
def localCycle00254 : Cycle where
  length := 5
  data := {
    node := ![.distance 1 4, .distance 1 6, .distance 1 5, .theta 1, .distance 0 1, .distance 1 4]
    constant := ![0, -2, -1, 2, -1]
    coefficient := ![0, 0, 0, 1, 0]
    strict := ![true, false, false, false, false] }
  origin := ![.triangle 23 2, .gapLower 1 3, .corridorLower 1 5, .gapLower 1 6, .triangle 2 0]

-- Cycle fingerprint 983019023df081092857bde20c38852fce82f75df944fc8da90adbdc6601682d.
def localCycle00255 : Cycle where
  length := 10
  data := {
    node := ![.theta 1, .zero, .theta 6, .distance 5 6, .distance 4 6, .distance 0 4, .distance 4 5, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1]
    constant := ![0, 0, 3, 0, -1, -1, -1, 0, -3, -1]
    coefficient := ![0, 1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, false, false, false] }
  origin := ![.thetaLower 1, .thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 13 0, .triangle 12 0, .triangle 22 0, .gapLower 1 2, .gapLower 1 1, .corridorLower 1 2]

-- Cycle fingerprint 98e07c01b5a0605a635912a221fbec5fd6b4a83c3589cdc46fae2388b177a1a2.
def localCycle00256 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 3, .distance 1 2, .theta 1, .zero, .theta 6, .distance 1 6, .distance 1 4, .distance 1 3]
    constant := ![-3, -1, 0, 0, 2, 0, 0]
    coefficient := ![0, 0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, false, true, true, true] }
  origin := ![.gapLower 1 1, .corridorLower 1 2, .thetaLower 1, .thetaUpper 6, .gapUpper 6 0, .triangle 23 1, .triangle 19 1]

-- Cycle fingerprint 9945524e1633ec19cddf27c716f6a4514303728075a38a3e1c8760499cc25e0a.
def localCycle00257 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 3, .theta 1, .zero, .theta 4, .distance 3 4, .distance 2 4, .distance 4 5, .distance 5 6, .distance 1 5, .distance 1 4, .distance 1 3]
    constant := ![-1, 0, 0, 3, 0, -1, -1, -1, -2, -2]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, false, false, false] }
  origin := ![.corridorLower 1 3, .thetaLower 1, .thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 28 0, .triangle 34 0, .triangle 24 0, .gapLower 1 3, .gapLower 1 2]

-- Cycle fingerprint 9a4345af08d8456a2ce2a39c3dee65fd51af6b32812d185415f0aa1f90a3279f.
def localCycle00258 : Cycle where
  length := 8
  data := {
    node := ![.distance 1 6, .distance 1 5, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1, .zero, .theta 6, .distance 1 6]
    constant := ![0, 0, 0, 0, -3, 0, 0, 2]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 0]
    strict := ![true, true, true, true, false, false, false, true] }
  origin := ![.triangle 24 1, .triangle 22 1, .triangle 19 1, .triangle 15 1, .gapLower 1 0, .thetaLower 1, .thetaUpper 6, .gapUpper 6 0]

-- Cycle fingerprint 9ab3708c1cdea560cdd9889c017b65a48f01aa33e0a3668655770dcf00d840e2.
def localCycle00259 : Cycle where
  length := 11
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 4 5, .distance 5 6, .distance 1 5, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1, .zero, .theta 4]
    constant := ![3, 0, -1, -1, -1, 0, -2, -2, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, false, false, false, false, false, false, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 28 0, .triangle 34 0, .triangle 24 0, .gapLower 1 3, .gapLower 1 2, .gapLower 1 1, .corridorLower 1 2, .thetaLower 1, .thetaUpper 4]

-- Cycle fingerprint 9b238f608bb8782490042f43757565a380d623d44c8ff7950f393566663c6d2b.
def localCycle00260 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 4, .distance 4 6, .distance 1 6, .distance 1 5, .theta 1, .distance 0 1, .distance 0 4]
    constant := ![-1, 0, -2, -1, 2, 0]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![false, true, false, false, false, true] }
  origin := ![.triangle 13 0, .triangle 23 2, .gapLower 1 4, .corridorLower 1 5, .gapLower 1 6, .triangle 2 2]

-- Cycle fingerprint 9bff553310ad322dde1a0496cf97f0be9a7784b2355b9f24e1257b080b0c9ffa.
def localCycle00261 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 2, .theta 1, .zero, .theta 4, .distance 3 4, .distance 4 5, .distance 5 6, .distance 1 5, .distance 1 4, .distance 1 3, .distance 1 2]
    constant := ![-1, 0, 0, 3, -1, -1, -1, 0, -2, -2]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false, false, false] }
  origin := ![.corridorLower 1 2, .thetaLower 1, .thetaUpper 4, .corridorUpper 3 4, .triangle 31 0, .triangle 34 0, .triangle 24 0, .gapLower 1 3, .gapLower 1 2, .gapLower 1 1]

-- Cycle fingerprint 9c5b25525b07bfa45de6b5f0dfeaec41450761703d0101a1f77b54c4af0807f8.
def localCycle00262 : Cycle where
  length := 8
  data := {
    node := ![.distance 1 4, .distance 1 3, .distance 1 2, .theta 1, .distance 0 1, .distance 0 4, .distance 4 6, .distance 4 5, .distance 1 4]
    constant := ![-2, 0, -1, 3, 0, -1, 0, -1]
    coefficient := ![0, 0, 0, 1, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, false, true, false] }
  origin := ![.gapLower 1 2, .triangle 15 1, .corridorLower 1 2, .corridorUpper 0 1, .triangle 2 2, .triangle 13 0, .triangle 34 1, .triangle 22 0]

-- Cycle fingerprint 9db69e107645e66b424c516477a93853d438ce49456b7f2b851e2a8ff376fe57.
def localCycle00263 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 5, .distance 1 4, .theta 4, .distance 3 4, .distance 3 5, .distance 5 6, .distance 4 5, .distance 1 5]
    constant := ![-2, 0, 3, 0, -1, -1, 0]
    coefficient := ![0, 0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, true] }
  origin := ![.gapLower 1 3, .gapLower 4 0, .corridorUpper 3 4, .triangle 31 2, .triangle 33 0, .triangle 34 0, .triangle 22 2]

-- Cycle fingerprint 9dcadb90fed05822daff9243a5afc107abb2dc32f3da63dd803836b180eabeb4.
def localCycle00264 : Cycle where
  length := 8
  data := {
    node := ![.distance 1 5, .distance 1 3, .distance 1 2, .theta 1, .distance 0 1, .distance 0 4, .distance 0 5, .distance 5 6, .distance 1 5]
    constant := ![0, -2, -1, 3, 0, 0, -1, -1]
    coefficient := ![0, 0, 0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, false, false] }
  origin := ![.gapLower 1 2, .gapLower 1 1, .corridorLower 1 2, .corridorUpper 0 1, .triangle 2 2, .triangle 12 2, .triangle 14 0, .triangle 24 0]

-- Cycle fingerprint 9dd93a425801d50dde3384d16249f5045de4f1f8a7c2803b9508b39f4f5e32a1.
def localCycle00265 : Cycle where
  length := 10
  data := {
    node := ![.theta 1, .zero, .theta 4, .distance 3 4, .distance 4 5, .distance 5 6, .distance 1 5, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1]
    constant := ![0, 0, 3, -1, -1, -1, 0, 0, -2, -2]
    coefficient := ![0, 1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, true, false, false] }
  origin := ![.thetaLower 1, .thetaUpper 4, .corridorUpper 3 4, .triangle 31 0, .triangle 34 0, .triangle 24 0, .gapLower 1 3, .triangle 19 1, .gapLower 1 1, .gapLower 1 0]

-- Cycle fingerprint 9e5d3f9eb9c9bafc73993f979befc5fd584028548dc55c604550d1c48e1d48a3.
def localCycle00266 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 5, .distance 1 4, .distance 1 3, .theta 1, .distance 0 1, .distance 0 5, .distance 5 6, .distance 1 5]
    constant := ![-2, -2, -1, 4, 0, -1, -1]
    coefficient := ![0, 0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false] }
  origin := ![.gapLower 1 3, .gapLower 1 2, .corridorLower 1 3, .gapLower 1 6, .triangle 3 2, .triangle 14 0, .triangle 24 0]

-- Cycle fingerprint 9edf9a47c299cb132865956363691d080740d1cec3fe055e5204333b47b6a2c5.
def localCycle00267 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 4 5, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1, .distance 0 1]
    constant := ![0, -1, -1, 0, -2, -1, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![true, false, false, false, false, false, false] }
  origin := ![.triangle 2 2, .triangle 12 0, .triangle 22 0, .gapLower 1 2, .gapLower 1 1, .corridorLower 1 2, .corridorUpper 0 1]

-- Cycle fingerprint 9fe0f54a3ebc44fa840a244caadbc818585b0b1d9ed6e4024c2bd43a2c690c39.
def localCycle00268 : Cycle where
  length := 12
  data := {
    node := ![.distance 5 6, .distance 2 5, .distance 2 3, .distance 1 2, .theta 1, .distance 0 1, .distance 1 4, .distance 4 6, .distance 4 5, .theta 4, .distance 3 4, .distance 3 5, .distance 5 6]
    constant := ![-1, 0, -1, -2, 2, -1, -1, 0, -1, 3, 0, -1]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0]
    strict := ![false, false, false, false, false, false, false, true, false, false, true, false] }
  origin := ![.triangle 30 0, .gapLower 2 3, .triangle 15 0, .gapLower 1 0, .gapLower 1 6, .triangle 2 0, .triangle 23 0, .triangle 34 1, .corridorLower 4 5, .corridorUpper 3 4, .triangle 31 2, .triangle 33 0]

-- Cycle fingerprint a01758ecaacae89ba9f7729e3dec06d2063d7694e009a428cc15649cae3bcb66.
def localCycle00269 : Cycle where
  length := 11
  data := {
    node := ![.distance 4 5, .distance 5 6, .distance 1 5, .distance 1 4, .distance 1 2, .theta 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 2 4, .distance 4 5]
    constant := ![-1, -1, 0, 0, -2, 0, 0, 0, 3, 0, -1]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, true, false, true, false, false, false, true, false] }
  origin := ![.triangle 34 0, .triangle 24 0, .gapLower 1 3, .triangle 16 1, .gapLower 1 0, .thetaNext 0, .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 28 0]

-- Cycle fingerprint a085cfe425f3c0f3d0d22567f0bbae22aba2ae7ce4cdbd726f099c63baddee64.
def localCycle00270 : Cycle where
  length := 6
  data := {
    node := ![.theta 1, .zero, .theta 6, .distance 1 6, .distance 1 5, .distance 1 4, .theta 1]
    constant := ![0, 0, 2, 0, -3, -1]
    coefficient := ![0, 1, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false] }
  origin := ![.thetaLower 1, .thetaUpper 6, .gapUpper 6 0, .triangle 24 1, .gapLower 1 3, .corridorLower 1 4]

-- Cycle fingerprint a1cd999522dc380a527b8e767839cdc343cfb7bfd6c6d9f917546034f5af22f9.
def localCycle00271 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 6, .distance 1 5, .distance 1 3, .distance 1 2, .theta 1, .distance 0 1, .distance 1 4, .distance 1 6]
    constant := ![-2, 0, 0, -2, 3, -1, 0]
    coefficient := ![0, 0, 0, 0, 1, 0, 0]
    strict := ![false, true, true, false, false, false, true] }
  origin := ![.gapLower 1 3, .triangle 20 1, .triangle 15 1, .gapLower 1 0, .corridorUpper 0 1, .triangle 2 0, .triangle 23 2]

-- Cycle fingerprint a225bc60687bc42b8851cc219f81e13734948ed6140a97d9db3ad0c5c88efeb4.
def localCycle00272 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 2, .theta 1, .distance 0 1, .distance 0 5, .distance 5 6, .distance 1 5, .distance 1 4, .distance 1 2]
    constant := ![-3, 3, 0, -1, -1, 0, 0]
    coefficient := ![0, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, true] }
  origin := ![.gapLower 1 0, .corridorUpper 0 1, .triangle 3 2, .triangle 14 0, .triangle 24 0, .gapLower 1 3, .triangle 16 1]

-- Cycle fingerprint a2601035bd31534f712076e0fa64b3538d32bf8ecf36befeb4c15c5b7709a115.
def localCycle00273 : Cycle where
  length := 8
  data := {
    node := ![.distance 4 5, .theta 4, .theta 3, .theta 2, .theta 1, .distance 0 1, .distance 1 6, .distance 1 4, .distance 4 5]
    constant := ![-1, 0, 0, 0, 2, -2, 0, -1]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![false, true, true, true, false, false, true, false] }
  origin := ![.corridorLower 4 5, .thetaNext 3, .thetaNext 2, .thetaNext 1, .gapLower 1 6, .gapLower 1 5, .triangle 23 1, .triangle 22 0]

-- Cycle fingerprint a2f863f9d8affe40d5ade94297d834904e01f541d700a6a9fa4bb812fdc54f38.
def localCycle00274 : Cycle where
  length := 12
  data := {
    node := ![.distance 2 5, .distance 5 6, .distance 4 5, .distance 0 5, .distance 1 5, .distance 1 4, .distance 1 2, .theta 1, .zero, .theta 4, .distance 3 4, .distance 2 4, .distance 2 5]
    constant := ![-1, -1, 0, 0, -2, 0, -2, 0, 0, 3, 0, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, true, false, true, false, false, false, false, true, true] }
  origin := ![.triangle 30 0, .triangle 34 0, .gapLower 5 2, .triangle 3 1, .gapLower 1 3, .triangle 16 1, .gapLower 1 0, .thetaLower 1, .thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 28 2]

-- Cycle fingerprint a3e1d19af2d4212344623456b2fe972c528f67f4a0f94c01da6119a4d221ae29.
def localCycle00275 : Cycle where
  length := 8
  data := {
    node := ![.distance 1 4, .distance 1 3, .distance 1 2, .theta 1, .distance 0 1, .distance 0 5, .distance 5 6, .distance 1 5, .distance 1 4]
    constant := ![0, -2, -1, 3, 0, -1, -1, 0]
    coefficient := ![0, 0, 0, 1, 0, 0, 0, 0]
    strict := ![true, false, false, false, true, false, false, true] }
  origin := ![.triangle 19 1, .gapLower 1 1, .corridorLower 1 2, .corridorUpper 0 1, .triangle 3 2, .triangle 14 0, .triangle 24 0, .triangle 22 1]

-- Cycle fingerprint a4b640daf3c62a2992fba5ce75815f39552d9b097230b68c8fbbb1c10b209510.
def localCycle00276 : Cycle where
  length := 8
  data := {
    node := ![.distance 4 6, .distance 4 5, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1, .distance 0 1, .distance 0 4, .distance 4 6]
    constant := ![0, -1, 0, 0, -3, 3, 0, -1]
    coefficient := ![0, 0, 0, 0, 0, 1, 0, 0]
    strict := ![true, false, false, true, false, false, true, false] }
  origin := ![.triangle 34 1, .triangle 22 0, .gapLower 1 2, .triangle 15 1, .gapLower 1 0, .corridorUpper 0 1, .triangle 2 2, .triangle 13 0]

-- Cycle fingerprint a4e83a4f4c211c395544e557bf0c56eeef26f3f5a3fa7d0cc91e758ad3310d26.
def localCycle00277 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 2, .theta 1, .zero, .theta 4, .distance 3 4, .distance 3 5, .distance 5 6, .distance 4 5, .distance 1 4, .distance 1 3, .distance 1 2]
    constant := ![-1, 0, 0, 3, 0, -1, -1, -1, -2, -2]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, false, false, false] }
  origin := ![.corridorLower 1 2, .thetaLower 1, .thetaUpper 4, .corridorUpper 3 4, .triangle 31 2, .triangle 33 0, .triangle 34 0, .triangle 22 0, .gapLower 1 2, .gapLower 1 1]

-- Cycle fingerprint a5f5cdf7663e757d3cb5afcb2dde2adeab87091822c8bbd3841958c209e2d206.
def localCycle00278 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 4, .distance 4 6, .distance 5 6, .distance 2 6, .theta 2, .zero]
    constant := ![0, 3, -1, -1, 0, 0, -2, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, -1, 0]
    strict := ![false, false, false, false, true, true, true, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 0, .triangle 32 0, .triangle 34 1, .triangle 30 2, .gapUpper 2 6, .thetaLower 2]

-- Cycle fingerprint a60cd12cd743aef8de2ec425d0740547afa2664fba993742bacef1c28e9e3c67.
def localCycle00279 : Cycle where
  length := 6
  data := {
    node := ![.distance 1 4, .theta 1, .zero, .theta 6, .distance 1 6, .distance 1 5, .distance 1 4]
    constant := ![-1, 0, 0, 2, -2, -2]
    coefficient := ![0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, true, false, false] }
  origin := ![.corridorLower 1 4, .thetaLower 1, .thetaUpper 6, .gapUpper 6 0, .gapLower 1 4, .gapLower 1 3]

-- Cycle fingerprint a730bc8e9d03eed700bb4ade8ce7f9b177e5748555fb49da6cd0c5b7764b90e8.
def localCycle00280 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 4 6, .distance 4 5, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1, .distance 0 1]
    constant := ![0, -1, 0, -1, -3, 0, -1, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![true, false, true, false, false, true, false, false] }
  origin := ![.triangle 2 2, .triangle 13 0, .triangle 34 1, .triangle 22 0, .gapLower 1 2, .triangle 15 1, .corridorLower 1 2, .corridorUpper 0 1]

-- Cycle fingerprint a799b8a8d4d4cf079c2c64a9bc190d4d07c8503d341b3bf94129f828996d4062.
def localCycle00281 : Cycle where
  length := 6
  data := {
    node := ![.theta 1, .distance 0 1, .distance 1 5, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1]
    constant := ![3, -1, 0, 0, -3, -1]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false] }
  origin := ![.corridorUpper 0 1, .triangle 3 0, .triangle 22 1, .triangle 19 1, .gapLower 1 1, .corridorLower 1 2]

-- Cycle fingerprint a79ba7c15995d7985de54baa1008658ad6bd62564226e85efb0a87240f5c24cb.
def localCycle00282 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 3 5, .distance 5 6, .distance 4 5, .distance 1 5, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, 0, -1, -1, 0, -2, 0, 0, -2, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false, true, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 31 2, .triangle 33 0, .triangle 34 0, .gapLower 5 1, .gapLower 1 3, .gapLower 1 2, .triangle 15 1, .gapLower 1 0, .thetaLower 1]

-- Cycle fingerprint a8daeceb860541ced2933832ba26f65bb42b012698b0776cd64fe1685e6b5c2d.
def localCycle00283 : Cycle where
  length := 8
  data := {
    node := ![.distance 4 5, .theta 4, .theta 3, .theta 2, .theta 1, .distance 0 1, .distance 1 4, .distance 4 6, .distance 4 5]
    constant := ![-1, 0, 0, 0, 1, -1, -1, 0]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![false, true, true, true, false, false, false, true] }
  origin := ![.corridorLower 4 5, .thetaNext 3, .thetaNext 2, .thetaNext 1, .gapLower 1 6, .triangle 2 0, .triangle 23 0, .triangle 34 1]

-- Cycle fingerprint aa1d454fa3ca329c60dfcf2feeff6250ba04d1f251e78d3839de6773824f3ce8.
def localCycle00284 : Cycle where
  length := 7
  data := {
    node := ![.theta 1, .distance 0 1, .distance 1 4, .distance 1 6, .distance 1 5, .distance 1 3, .distance 1 2, .theta 1]
    constant := ![2, -1, 0, 0, -2, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, true, false] }
  origin := ![.gapLower 1 6, .triangle 2 0, .triangle 23 2, .triangle 24 1, .gapLower 1 2, .triangle 15 1, .corridorLower 1 2]

-- Cycle fingerprint aad91457b352b1cf8c0215a5dd356e0fc9f41196558e338cec9f074c10057127.
def localCycle00285 : Cycle where
  length := 10
  data := {
    node := ![.theta 1, .zero, .theta 4, .distance 3 4, .distance 4 5, .distance 5 6, .distance 1 5, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1]
    constant := ![0, 0, 3, -1, -1, -1, 0, 0, -3, -1]
    coefficient := ![0, 1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, true, false, false] }
  origin := ![.thetaLower 1, .thetaUpper 4, .corridorUpper 3 4, .triangle 31 0, .triangle 34 0, .triangle 24 0, .gapLower 1 3, .triangle 19 1, .gapLower 1 1, .corridorLower 1 2]

-- Cycle fingerprint aaee1514a67cfc432df055932059c9b50b23e43f8766c5fbfa2517a06ba681d0.
def localCycle00286 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 2, .theta 1, .zero, .theta 4, .distance 3 4, .distance 2 4, .distance 4 5, .distance 5 6, .distance 1 6, .distance 1 5, .distance 1 2]
    constant := ![-2, 0, 0, 3, 0, -1, -1, 0, -2, 0]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, false, false, true] }
  origin := ![.gapLower 1 0, .thetaLower 1, .thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 28 0, .triangle 34 0, .gapLower 6 1, .gapLower 1 4, .triangle 17 1]

-- Cycle fingerprint ab5275811d89aa03bed341a4ed1d96f2538db7d77059d81adc7088538e523927.
def localCycle00287 : Cycle where
  length := 8
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 5, .distance 5 6, .distance 1 5, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1]
    constant := ![3, 0, -1, -1, -2, 0, 0, -2]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, true, true, false] }
  origin := ![.corridorUpper 0 1, .triangle 3 2, .triangle 14 0, .triangle 24 0, .gapLower 1 3, .triangle 19 1, .triangle 15 1, .gapLower 1 0]

-- Cycle fingerprint abc16edd0c948ac3afdfd9d017420f81668cd08f68a49944e1cacb5ac13eff4e.
def localCycle00288 : Cycle where
  length := 11
  data := {
    node := ![.distance 2 5, .distance 5 6, .distance 4 5, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1, .zero, .theta 4, .distance 3 4, .distance 2 4, .distance 2 5]
    constant := ![-1, -1, -1, 0, 0, -2, 0, 0, 3, 0, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, true, true, false, false, false, false, true, true] }
  origin := ![.triangle 30 0, .triangle 34 0, .triangle 22 0, .triangle 19 1, .triangle 15 1, .gapLower 1 0, .thetaLower 1, .thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 28 2]

-- Cycle fingerprint abdfcec01cfada06eed77082a54cb99a6d18a87872e0ae499a81deded7da3b3a.
def localCycle00289 : Cycle where
  length := 10
  data := {
    node := ![.theta 4, .distance 3 4, .distance 4 6, .distance 4 5, .distance 2 4, .distance 2 3, .distance 1 2, .theta 1, .theta 0, .zero, .theta 4]
    constant := ![3, -1, 0, -1, 0, -1, -2, 0, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![false, false, true, false, false, false, false, true, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 32 0, .triangle 34 1, .triangle 28 0, .gapLower 2 3, .triangle 15 0, .gapLower 1 0, .thetaNext 0, .thetaLower 0, .thetaUpper 4]

-- Cycle fingerprint ad3f8471895a31e3246c58640a9d2258da1c4345598a1b61db79a0f80ad969b4.
def localCycle00290 : Cycle where
  length := 8
  data := {
    node := ![.theta 6, .distance 1 6, .distance 1 5, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1, .zero, .theta 6]
    constant := ![2, 0, 0, 0, -2, -2, 0, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![true, true, true, true, false, false, false, false] }
  origin := ![.gapUpper 6 0, .triangle 24 1, .triangle 22 1, .triangle 19 1, .gapLower 1 1, .gapLower 1 0, .thetaLower 1, .thetaUpper 6]

-- Cycle fingerprint ad96661af8c64c8b3de3aa3048fafa7b6245237670e7b9b35bf4ac67bf9e7983.
def localCycle00291 : Cycle where
  length := 8
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 4, .distance 4 6, .distance 1 6, .distance 1 5, .distance 1 4, .distance 1 3, .theta 1]
    constant := ![4, 0, -1, 0, -2, 0, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, true, false, false] }
  origin := ![.gapLower 1 6, .triangle 2 2, .triangle 13 0, .triangle 23 2, .gapLower 1 4, .triangle 22 1, .gapLower 1 2, .corridorLower 1 3]

-- Cycle fingerprint ade9db40c64558513d051929e8d91fbe3df51e452de7a7ed9d4851b55d707791.
def localCycle00292 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 4 6, .distance 0 4, .distance 4 5, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, -1, -1, -1, -1, 0, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, true, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 32 0, .triangle 13 0, .triangle 12 0, .triangle 22 0, .triangle 19 1, .triangle 15 1, .corridorLower 1 2, .thetaLower 1]

-- Cycle fingerprint adfd05a054099e9a6e17d3cc5702c7430ac1b8e1808128f62e01592503229576.
def localCycle00293 : Cycle where
  length := 8
  data := {
    node := ![.distance 5 6, .distance 1 5, .distance 1 3, .distance 1 2, .theta 1, .distance 0 1, .distance 0 4, .distance 0 5, .distance 5 6]
    constant := ![-1, 0, 0, -2, 2, 0, 0, -1]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![false, false, true, false, false, true, true, false] }
  origin := ![.triangle 24 0, .gapLower 1 2, .triangle 15 1, .gapLower 1 0, .gapLower 1 6, .triangle 2 2, .triangle 12 2, .triangle 14 0]

-- Cycle fingerprint ae57e7d3b1b29345d7d1f8f14dcb2546d1a4ef917412898c190081a2cc3cd40a.
def localCycle00294 : Cycle where
  length := 8
  data := {
    node := ![.theta 1, .zero, .theta 6, .distance 1 6, .distance 1 5, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1]
    constant := ![0, 0, 2, 0, -3, 0, 0, -1]
    coefficient := ![0, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, true, true, false] }
  origin := ![.thetaLower 1, .thetaUpper 6, .gapUpper 6 0, .triangle 24 1, .gapLower 1 3, .triangle 19 1, .triangle 15 1, .corridorLower 1 2]

-- Cycle fingerprint af19982e99428b5d61a5c9540de55babe35f0d8602fe98dfb0003811cb86e62f.
def localCycle00295 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 6, .distance 1 5, .distance 1 3, .distance 1 2, .theta 1, .distance 0 1, .distance 1 4, .distance 1 6]
    constant := ![-3, 0, 0, -1, 3, -1, 0]
    coefficient := ![0, 0, 0, 0, 1, 0, 0]
    strict := ![false, true, true, false, false, false, true] }
  origin := ![.gapLower 1 3, .triangle 20 1, .triangle 15 1, .corridorLower 1 2, .corridorUpper 0 1, .triangle 2 0, .triangle 23 2]

-- Cycle fingerprint b06bb9431357fe133d320be6f1afcb3803c9155d5fdebfcc689aff58c24542a3.
def localCycle00296 : Cycle where
  length := 7
  data := {
    node := ![.distance 2 6, .theta 6, .theta 5, .theta 4, .distance 3 4, .distance 4 5, .distance 2 4, .distance 2 6]
    constant := ![-2, 0, 0, 3, -1, -1, 0]
    coefficient := ![-1, 0, 0, 1, 0, 0, 0]
    strict := ![true, true, true, false, false, false, true] }
  origin := ![.gapUpper 6 6, .thetaNext 5, .thetaNext 4, .corridorUpper 3 4, .triangle 31 0, .triangle 28 0, .triangle 29 2]

-- Cycle fingerprint b097eb62f69455073f6cfeef59d820d3599ee516486c024c501b0e4a25aa3b50.
def localCycle00297 : Cycle where
  length := 8
  data := {
    node := ![.distance 1 4, .distance 1 3, .distance 1 2, .theta 1, .distance 0 1, .distance 0 5, .distance 5 6, .distance 1 5, .distance 1 4]
    constant := ![-2, 0, -1, 3, 0, -1, -1, 0]
    coefficient := ![0, 0, 0, 1, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, false, false, false] }
  origin := ![.gapLower 1 2, .triangle 15 1, .corridorLower 1 2, .corridorUpper 0 1, .triangle 3 2, .triangle 14 0, .triangle 24 0, .gapLower 1 3]

-- Cycle fingerprint b0a94574ccdd042d9d21cf0c5b087c6903eddd1f754257bc3dede681ffaa002a.
def localCycle00298 : Cycle where
  length := 8
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 4, .distance 4 5, .distance 1 5, .distance 1 6, .distance 1 3, .distance 1 2, .theta 1]
    constant := ![4, 0, -1, 0, -2, 0, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, true, false, false] }
  origin := ![.gapLower 1 6, .triangle 2 2, .triangle 12 0, .triangle 22 2, .gapLower 1 4, .triangle 21 1, .gapLower 1 1, .corridorLower 1 2]

-- Cycle fingerprint b0d236bad4505eb4a5b03e1dc23d16af899cfb022b5c26a470178b5e3db0c1ef.
def localCycle00299 : Cycle where
  length := 7
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 4, .distance 4 5, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1]
    constant := ![2, 0, -1, -1, -2, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, true, false] }
  origin := ![.gapLower 1 6, .triangle 2 2, .triangle 12 0, .triangle 22 0, .gapLower 1 2, .triangle 15 1, .corridorLower 1 2]

-- Cycle fingerprint b2de7d27b2adcbd3e4243ee68b87e712a3491277cac85cd0ed627d453c55359f.
def localCycle00300 : Cycle where
  length := 5
  data := {
    node := ![.distance 1 6, .distance 1 5, .distance 1 4, .theta 1, .distance 0 1, .distance 1 6]
    constant := ![0, -2, -1, 2, -1]
    coefficient := ![0, 0, 0, 1, 0]
    strict := ![true, false, false, false, false] }
  origin := ![.triangle 24 1, .gapLower 1 3, .corridorLower 1 4, .gapLower 1 6, .triangle 4 0]

-- Cycle fingerprint b2fedb3f51fd9146736fb3ffb8b834da3a5c9a6758493cf23b1238cf6a09ba57.
def localCycle00301 : Cycle where
  length := 12
  data := {
    node := ![.distance 1 4, .distance 1 3, .distance 1 2, .theta 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 2 4, .distance 2 5, .distance 5 6, .distance 4 5, .distance 1 4]
    constant := ![0, 0, -2, 0, 0, 0, 3, 0, 0, -1, -1, -1]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, false, true, true, false, false, false] }
  origin := ![.gapLower 1 2, .triangle 15 1, .gapLower 1 0, .thetaNext 0, .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 28 2, .triangle 30 0, .triangle 34 0, .triangle 22 0]

-- Cycle fingerprint b48b630d2c4275f32dd166a29588824a614ccc2f16cb6c59e73436268b3d767f.
def localCycle00302 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 6, .distance 1 5, .distance 1 4, .theta 1, .theta 0, .zero, .theta 6, .distance 1 6]
    constant := ![-2, -2, -1, 0, 0, 0, 2]
    coefficient := ![0, 0, 0, 0, 0, 1, 0]
    strict := ![false, false, false, true, false, false, true] }
  origin := ![.gapLower 1 4, .gapLower 1 3, .corridorLower 1 4, .thetaNext 0, .thetaLower 0, .thetaUpper 6, .gapUpper 6 0]

-- Cycle fingerprint b494585c15fa3b0c9a6e18a300ae83fad2370415d325401b354b5ff4c793c017.
def localCycle00303 : Cycle where
  length := 4
  data := {
    node := ![.theta 1, .distance 0 1, .distance 1 5, .distance 1 6, .theta 1]
    constant := ![2, -1, -2, -1]
    coefficient := ![1, 0, 0, 0]
    strict := ![false, false, false, false] }
  origin := ![.gapLower 1 6, .triangle 3 0, .gapLower 1 4, .corridorLower 1 6]

-- Cycle fingerprint b4da83081d8ecd1fdd43c8427b2216d8cc42eaeebc4d01ce2fcce711b0a93382.
def localCycle00304 : Cycle where
  length := 11
  data := {
    node := ![.distance 2 5, .distance 5 6, .distance 4 5, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1, .zero, .theta 4, .distance 3 4, .distance 2 4, .distance 2 5]
    constant := ![-1, -1, -1, 0, -2, -1, 0, 0, 3, 0, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, true, false, false, false, false, false, true, true] }
  origin := ![.triangle 30 0, .triangle 34 0, .triangle 22 0, .triangle 19 1, .gapLower 1 1, .corridorLower 1 2, .thetaLower 1, .thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 28 2]

-- Cycle fingerprint b4dc968cca32218c51bcb52225d1631970e6d5a40ca79fa701405f4ede985f31.
def localCycle00305 : Cycle where
  length := 10
  data := {
    node := ![.theta 1, .zero, .theta 4, .distance 3 4, .distance 2 4, .distance 4 6, .distance 4 5, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1]
    constant := ![0, 0, 3, 0, -1, 0, -1, 0, -2, -2]
    coefficient := ![0, 1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true, false, true, false, false] }
  origin := ![.thetaLower 1, .thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 29 0, .triangle 34 1, .triangle 22 0, .triangle 19 1, .gapLower 1 1, .gapLower 1 0]

-- Cycle fingerprint b4f140d4e4ce700454cd8ac9c23afa1ff859c15d086b3cd39116fbee1557c80f.
def localCycle00306 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 4 6, .distance 4 5, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1, .distance 0 1]
    constant := ![0, -1, 0, -1, -2, -2, -1, 4]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![true, false, true, false, false, false, false, false] }
  origin := ![.triangle 2 2, .triangle 13 0, .triangle 34 1, .triangle 22 0, .gapLower 1 2, .gapLower 1 1, .corridorLower 1 2, .gapLower 1 6]

-- Cycle fingerprint b51aee9f00dab80fd0d2e438aaf2d38e019c6601795cccd47fac4c201fbce393.
def localCycle00307 : Cycle where
  length := 8
  data := {
    node := ![.distance 4 5, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1, .distance 0 1, .distance 0 4, .distance 4 6, .distance 4 5]
    constant := ![-1, 0, -2, -1, 2, 0, -1, 0]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, true] }
  origin := ![.triangle 22 0, .gapLower 1 2, .gapLower 1 1, .corridorLower 1 2, .gapLower 1 6, .triangle 2 2, .triangle 13 0, .triangle 34 1]

-- Cycle fingerprint b565de772bb138675852c53f0d89dae1e2caff38756695dfa2c4ac508c000767.
def localCycle00308 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 2 4, .distance 4 5, .distance 5 6, .distance 1 5, .distance 1 4, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, 0, -1, -1, -1, 0, 0, -3, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, true, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 28 0, .triangle 34 0, .triangle 24 0, .gapLower 1 3, .triangle 16 1, .gapLower 1 0, .thetaLower 1]

-- Cycle fingerprint b59ede5762bd0f63240528a4a41b7dd6e2a4ebe3d2ac0b50445aa93849281e6c.
def localCycle00309 : Cycle where
  length := 8
  data := {
    node := ![.theta 5, .theta 4, .theta 3, .theta 2, .theta 1, .distance 0 1, .distance 1 5, .distance 5 6, .theta 5]
    constant := ![0, 0, 0, 0, 1, -1, -1, -1]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![true, true, true, true, false, false, false, false] }
  origin := ![.thetaNext 4, .thetaNext 3, .thetaNext 2, .thetaNext 1, .gapLower 1 6, .triangle 3 0, .triangle 24 0, .corridorLower 5 6]

-- Cycle fingerprint b5b9346ec5fc1852a56da79ae2f2e7f157eb59763dabcc1d0361aa3c1a48705b.
def localCycle00310 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 4 5, .distance 2 4, .distance 4 6, .distance 0 4, .theta 0, .zero]
    constant := ![0, 3, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 31 0, .triangle 28 0, .triangle 29 0, .triangle 13 0, .corridorLower 0 4, .thetaLower 0]

-- Cycle fingerprint b840e3afd1ec4641c3075dd54e387eb942f041679564df85853d596c99f3be55.
def localCycle00311 : Cycle where
  length := 9
  data := {
    node := ![.distance 5 6, .distance 1 6, .distance 1 5, .distance 1 2, .theta 1, .zero, .theta 4, .distance 3 4, .distance 4 5, .distance 5 6]
    constant := ![0, -2, 0, -2, 0, 0, 3, -1, -1]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![false, false, true, false, false, false, false, false, false] }
  origin := ![.gapLower 6 1, .gapLower 1 4, .triangle 17 1, .gapLower 1 0, .thetaLower 1, .thetaUpper 4, .corridorUpper 3 4, .triangle 31 0, .triangle 34 0]

-- Cycle fingerprint b86996485835149922fe0b5996aca0ce77f2ca107ec646116d55466fdeb80722.
def localCycle00312 : Cycle where
  length := 11
  data := {
    node := ![.distance 3 4, .distance 2 4, .distance 2 5, .distance 5 6, .distance 4 5, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1, .zero, .theta 4, .distance 3 4]
    constant := ![0, 0, -1, -1, -1, 0, -3, -1, 0, 0, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1]
    strict := ![true, true, false, false, false, false, false, false, false, false, false] }
  origin := ![.triangle 25 2, .triangle 28 2, .triangle 30 0, .triangle 34 0, .triangle 22 0, .gapLower 1 2, .gapLower 1 1, .corridorLower 1 2, .thetaLower 1, .thetaUpper 4, .corridorUpper 3 4]

-- Cycle fingerprint badd4853d95c127d6ddfdc8c4c71bb573c61f0d9d8d6236f9d9c121a7cd9a45d.
def localCycle00313 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 5, .distance 1 4, .distance 1 2, .theta 1, .zero, .theta 6, .distance 1 6, .distance 1 5]
    constant := ![-2, 0, -2, 0, 0, 2, 0]
    coefficient := ![0, 0, 0, 0, 1, 0, 0]
    strict := ![false, true, false, false, false, true, true] }
  origin := ![.gapLower 1 3, .triangle 16 1, .gapLower 1 0, .thetaLower 1, .thetaUpper 6, .gapUpper 6 0, .triangle 24 1]

-- Cycle fingerprint bb0af6fbd5df5f5b02a1732b6a81c5134af279e512903f7a658cd00bf4778c22.
def localCycle00314 : Cycle where
  length := 6
  data := {
    node := ![.theta 1, .distance 0 1, .distance 1 4, .distance 1 6, .distance 1 5, .distance 1 3, .theta 1]
    constant := ![3, -1, 0, 0, -3, -1]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false] }
  origin := ![.corridorUpper 0 1, .triangle 2 0, .triangle 23 2, .triangle 24 1, .gapLower 1 2, .corridorLower 1 3]

-- Cycle fingerprint bb7e2db50253ea62ad460599b3082885691aa91a07b108c88302d494bf299901.
def localCycle00315 : Cycle where
  length := 7
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 4, .distance 2 3, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, -1, -1, -1, -2, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 0, .triangle 25 0, .triangle 15 0, .gapLower 1 0, .thetaLower 1]

-- Cycle fingerprint bbaeb01b46cd51678b7be6a13754d94df0bd3bad6e84810c941884879c25d89a.
def localCycle00316 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 2, .theta 1, .distance 0 1, .distance 0 4, .distance 4 6, .distance 1 6, .distance 1 5, .distance 1 4, .distance 1 3, .distance 1 2]
    constant := ![-1, 2, 0, -1, 0, 0, -2, 0, 0]
    coefficient := ![0, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, true, false, false, true] }
  origin := ![.corridorLower 1 2, .gapLower 1 6, .triangle 2 2, .triangle 13 0, .triangle 23 2, .triangle 24 1, .gapLower 1 3, .gapLower 1 2, .triangle 15 1]

-- Cycle fingerprint bbdc3f78d16d67241b9e4813674a8686286243f269babc08b4d3f5cd6fdd4562.
def localCycle00317 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 4, .distance 2 3, .distance 3 6, .distance 0 3, .theta 0, .zero]
    constant := ![0, 3, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 0, .triangle 25 0, .triangle 27 0, .triangle 11 0, .corridorLower 0 3, .thetaLower 0]

-- Cycle fingerprint bc1587ac4c5e5e45ec1fae000c52400227cc5bd45e05090f2aef1bda8b5aedec.
def localCycle00318 : Cycle where
  length := 6
  data := {
    node := ![.distance 1 2, .theta 1, .distance 0 1, .distance 1 5, .distance 1 4, .distance 1 3, .distance 1 2]
    constant := ![-2, 3, -1, 0, -2, 0]
    coefficient := ![0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true] }
  origin := ![.gapLower 1 0, .corridorUpper 0 1, .triangle 3 0, .triangle 22 1, .gapLower 1 2, .triangle 15 1]

-- Cycle fingerprint bc39f7065882215d12d48f0d0bcc5d12aaad7957cf6f45937f568ec85af3efd2.
def localCycle00319 : Cycle where
  length := 6
  data := {
    node := ![.distance 1 5, .distance 1 3, .theta 1, .distance 0 1, .distance 1 4, .distance 1 6, .distance 1 5]
    constant := ![-2, -1, 3, -1, -2, 0]
    coefficient := ![0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, true] }
  origin := ![.gapLower 1 2, .corridorLower 1 3, .corridorUpper 0 1, .triangle 2 0, .gapLower 1 4, .triangle 24 1]

-- Cycle fingerprint bc50c61b812b55bf43ded9222345b9d1beaa9b70ab5bcfef76b887bcf83dcbde.
def localCycle00320 : Cycle where
  length := 8
  data := {
    node := ![.distance 3 4, .distance 2 4, .distance 4 5, .distance 5 6, .distance 1 6, .distance 1 5, .distance 1 4, .theta 4, .distance 3 4]
    constant := ![0, -1, -1, 0, -2, 0, 0, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![true, false, false, true, false, true, false, false] }
  origin := ![.triangle 25 2, .triangle 28 0, .triangle 34 0, .triangle 24 2, .gapLower 1 4, .triangle 22 1, .gapLower 4 0, .corridorUpper 3 4]

-- Cycle fingerprint bc7d85d7793d9a7b89bbbac4a2145a8c505a7b39314c4c247581593ccb847df0.
def localCycle00321 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 0 4, .distance 4 6, .distance 1 4, .distance 4 5, .theta 4]
    constant := ![3, 0, 0, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 6 2, .triangle 13 0, .triangle 23 0, .triangle 22 0, .corridorLower 4 5]

-- Cycle fingerprint bc9112d560a4d94059b128af70e9227083184bb16cda02fe9c463aa4a51facc7.
def localCycle00322 : Cycle where
  length := 9
  data := {
    node := ![.distance 5 6, .distance 1 5, .distance 1 4, .distance 1 2, .theta 1, .zero, .theta 4, .distance 3 4, .distance 4 5, .distance 5 6]
    constant := ![-1, -2, 0, -2, 0, 0, 3, -1, -1]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![false, false, true, false, false, false, false, false, false] }
  origin := ![.triangle 24 0, .gapLower 1 3, .triangle 16 1, .gapLower 1 0, .thetaLower 1, .thetaUpper 4, .corridorUpper 3 4, .triangle 31 0, .triangle 34 0]

-- Cycle fingerprint bd2f2b019b4b6bbb9b409f27bfd46dd9f5ea1259166197bc33a2b069d513816b.
def localCycle00323 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 3 5, .distance 5 6, .distance 4 5, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, 0, -1, -1, -1, 0, 0, -3, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, true, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 31 2, .triangle 33 0, .triangle 34 0, .triangle 22 0, .gapLower 1 2, .triangle 15 1, .gapLower 1 0, .thetaLower 1]

-- Cycle fingerprint bdb1767d0cdf29b88499de5a3254f6e7d8661ca2eaa72d7c4f9c065b98e65c5d.
def localCycle00324 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 5, .distance 1 6, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1, .distance 0 1, .distance 0 4, .distance 4 5, .distance 1 5]
    constant := ![0, -2, 0, -2, -1, 4, 0, -1, 0]
    coefficient := ![0, 0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![true, false, true, false, false, false, true, false, true] }
  origin := ![.triangle 24 2, .gapLower 1 3, .triangle 19 1, .gapLower 1 1, .corridorLower 1 2, .gapLower 1 6, .triangle 2 2, .triangle 12 0, .triangle 22 2]

-- Cycle fingerprint bdfb70cac395f95f7b0357ca160fa93a0d97fd1c16d2b4d8696f354fac1db0a7.
def localCycle00325 : Cycle where
  length := 5
  data := {
    node := ![.distance 1 5, .theta 1, .distance 0 1, .distance 1 4, .distance 1 6, .distance 1 5]
    constant := ![-1, 3, -1, -2, -2]
    coefficient := ![0, 1, 0, 0, 0]
    strict := ![false, false, false, false, false] }
  origin := ![.corridorLower 1 5, .corridorUpper 0 1, .triangle 2 0, .gapLower 1 4, .gapLower 1 3]

-- Cycle fingerprint be593e6838d0cf25ecdb05512936b97d7249d1f6c39f9600522f41d6b42d6580.
def localCycle00326 : Cycle where
  length := 8
  data := {
    node := ![.distance 3 5, .distance 5 6, .distance 4 5, .distance 0 5, .distance 1 5, .distance 1 4, .theta 4, .distance 3 4, .distance 3 5]
    constant := ![-1, -1, 0, 0, -3, 0, 3, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 0]
    strict := ![false, false, false, true, false, false, false, true] }
  origin := ![.triangle 33 0, .triangle 34 0, .gapLower 5 2, .triangle 3 1, .gapLower 1 3, .gapLower 4 0, .corridorUpper 3 4, .triangle 31 2]

-- Cycle fingerprint bee34cf477a25964970492e0fe72a521502890624b942d752f4682f8d4cff816.
def localCycle00327 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 6, .distance 1 5, .distance 1 4, .theta 4, .distance 3 4, .distance 4 5, .distance 5 6, .distance 1 6]
    constant := ![-2, 0, 0, 3, -1, -1, 0]
    coefficient := ![0, 0, 0, 1, 0, 0, 0]
    strict := ![false, true, false, false, false, false, true] }
  origin := ![.gapLower 1 4, .triangle 22 1, .gapLower 4 0, .corridorUpper 3 4, .triangle 31 0, .triangle 34 0, .triangle 24 2]

-- Cycle fingerprint bf9ec8f5a6447a533a279f87e939b297d47f47bc08555fdabfcdd41753349725.
def localCycle00328 : Cycle where
  length := 5
  data := {
    node := ![.theta 1, .distance 0 1, .distance 1 4, .distance 1 6, .distance 1 5, .theta 1]
    constant := ![3, -1, 0, -3, -1]
    coefficient := ![1, 0, 0, 0, 0]
    strict := ![false, false, true, false, false] }
  origin := ![.corridorUpper 0 1, .triangle 2 0, .triangle 23 2, .gapLower 1 3, .corridorLower 1 5]

-- Cycle fingerprint c04520de512da7e52e5543aeaa5de93db5f646450e926ca4ebe1e89108f9d7fc.
def localCycle00329 : Cycle where
  length := 8
  data := {
    node := ![.distance 4 5, .theta 4, .theta 3, .theta 2, .theta 1, .distance 0 1, .distance 1 6, .distance 1 4, .distance 4 5]
    constant := ![-1, 0, 0, 0, 1, -1, 0, -1]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![false, true, true, true, false, false, true, false] }
  origin := ![.corridorLower 4 5, .thetaNext 3, .thetaNext 2, .thetaNext 1, .gapLower 1 6, .triangle 4 0, .triangle 23 1, .triangle 22 0]

-- Cycle fingerprint c114c5993b8d39e7dc4a23aab2dab86c971e61cd9702c9ba13362daaf8401b32.
def localCycle00330 : Cycle where
  length := 9
  data := {
    node := ![.distance 5 6, .distance 1 6, .distance 1 5, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1, .distance 0 1, .distance 0 5, .distance 5 6]
    constant := ![0, -2, 0, 0, 0, -2, 3, 0, -1]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 0, 0]
    strict := ![true, false, false, true, true, false, false, true, false] }
  origin := ![.triangle 24 2, .gapLower 1 4, .gapLower 1 3, .triangle 19 1, .triangle 15 1, .gapLower 1 0, .corridorUpper 0 1, .triangle 3 2, .triangle 14 0]

-- Cycle fingerprint c1237a96e5f6f0c266e9f338059433e0be8541ad2605a67ec79df653dcd7cb5f.
def localCycle00331 : Cycle where
  length := 10
  data := {
    node := ![.theta 1, .zero, .theta 4, .distance 3 4, .distance 3 5, .distance 5 6, .distance 4 5, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1]
    constant := ![0, 0, 3, 0, -1, -1, -1, 0, -3, -1]
    coefficient := ![0, 1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, false, false, false] }
  origin := ![.thetaLower 1, .thetaUpper 4, .corridorUpper 3 4, .triangle 31 2, .triangle 33 0, .triangle 34 0, .triangle 22 0, .gapLower 1 2, .gapLower 1 1, .corridorLower 1 2]

-- Cycle fingerprint c150b2bd16b179131cfc8e986979c2fada0851887601906fee6b029ddecce5b1.
def localCycle00332 : Cycle where
  length := 8
  data := {
    node := ![.theta 1, .zero, .theta 6, .distance 1 6, .distance 1 4, .distance 1 5, .distance 1 3, .distance 1 2, .theta 1]
    constant := ![0, 0, 2, 0, -2, 0, -2, -1]
    coefficient := ![0, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, true, false, false] }
  origin := ![.thetaLower 1, .thetaUpper 6, .gapUpper 6 0, .triangle 23 1, .gapLower 1 3, .triangle 20 1, .gapLower 1 1, .corridorLower 1 2]

-- Cycle fingerprint c19c4b338475fe63b243dd8d7a0c645754cf4317ac3c4be8f499dc9d3c9be794.
def localCycle00333 : Cycle where
  length := 8
  data := {
    node := ![.distance 4 5, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1, .distance 0 1, .distance 0 6, .distance 0 4, .distance 4 5]
    constant := ![-1, 0, -2, -1, 2, 0, 0, -1]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, false] }
  origin := ![.triangle 22 0, .gapLower 1 2, .gapLower 1 1, .corridorLower 1 2, .gapLower 1 6, .triangle 4 2, .triangle 13 1, .triangle 12 0]

-- Cycle fingerprint c20241d745d6d6e9f25e989396d1cca86b9d19345863bb21a3733c46c2e46e9f.
def localCycle00334 : Cycle where
  length := 6
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 4, .distance 4 6, .distance 1 6, .distance 1 5, .theta 1]
    constant := ![3, 0, -1, 0, -3, -1]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false] }
  origin := ![.corridorUpper 0 1, .triangle 2 2, .triangle 13 0, .triangle 23 2, .gapLower 1 4, .corridorLower 1 5]

-- Cycle fingerprint c3b0127ddbb4ee204db850540190af616dcb35f2d199a370bd6fd8839075be7a.
def localCycle00335 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 4, .distance 1 3, .theta 1, .zero, .theta 6, .distance 1 6, .distance 1 5, .distance 1 4]
    constant := ![-3, -1, 0, 0, 2, 0, 0]
    coefficient := ![0, 0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, false, true, true, true] }
  origin := ![.gapLower 1 2, .corridorLower 1 3, .thetaLower 1, .thetaUpper 6, .gapUpper 6 0, .triangle 24 1, .triangle 22 1]

-- Cycle fingerprint c3eb8d9c954f177e4e5a803f6c27321c67356d924bd62b6b42ef9fcb04e30e8f.
def localCycle00336 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 1 5, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1, .distance 0 1]
    constant := ![-1, 0, 0, 0, -3, 3]
    coefficient := ![0, 0, 0, 0, 0, 1]
    strict := ![false, true, true, true, false, false] }
  origin := ![.triangle 3 0, .triangle 22 1, .triangle 19 1, .triangle 15 1, .gapLower 1 0, .corridorUpper 0 1]

-- Cycle fingerprint c3fa3266719f43e263b7de315dc4f416a99ae669ceb0542dbd01c8d611377196.
def localCycle00337 : Cycle where
  length := 6
  data := {
    node := ![.distance 1 3, .theta 1, .distance 0 1, .distance 1 5, .distance 1 6, .distance 1 4, .distance 1 3]
    constant := ![-1, 3, -1, 0, -2, -2]
    coefficient := ![0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false] }
  origin := ![.corridorLower 1 3, .corridorUpper 0 1, .triangle 3 0, .triangle 24 2, .gapLower 1 3, .gapLower 1 2]

-- Cycle fingerprint c46a3a790b3732967188addc80083160d6de9cb8a7f2ddd8a3e9f8680b773e18.
def localCycle00338 : Cycle where
  length := 10
  data := {
    node := ![.theta 1, .zero, .theta 4, .distance 3 4, .distance 2 4, .distance 4 6, .distance 4 5, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1]
    constant := ![0, 0, 3, 0, -1, 0, -1, 0, -3, -1]
    coefficient := ![0, 1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true, false, true, false, false] }
  origin := ![.thetaLower 1, .thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 29 0, .triangle 34 1, .triangle 22 0, .triangle 19 1, .gapLower 1 1, .corridorLower 1 2]

-- Cycle fingerprint c4c341f440109ff68d80ebac2773c856d4fcfdd1e7a2b73e383bc96a5dbfed58.
def localCycle00339 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 3, .distance 1 2, .theta 1, .distance 0 1, .distance 0 4, .distance 4 5, .distance 1 4, .distance 1 3]
    constant := ![-3, -1, 3, 0, -1, -1, 0]
    coefficient := ![0, 0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false] }
  origin := ![.gapLower 1 1, .corridorLower 1 2, .corridorUpper 0 1, .triangle 2 2, .triangle 12 0, .triangle 22 0, .gapLower 1 2]

-- Cycle fingerprint c4f5619494b4db5cd4fc093f85e93af08cea8000b02cc217128610a841ed52f7.
def localCycle00340 : Cycle where
  length := 10
  data := {
    node := ![.theta 1, .zero, .theta 4, .distance 3 4, .distance 2 4, .distance 2 5, .distance 5 6, .distance 4 5, .distance 1 4, .distance 1 3, .theta 1]
    constant := ![0, 0, 3, 0, 0, -1, -1, -1, -3, -1]
    coefficient := ![0, 1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false, false, false, false, false] }
  origin := ![.thetaLower 1, .thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 28 2, .triangle 30 0, .triangle 34 0, .triangle 22 0, .gapLower 1 2, .corridorLower 1 3]

-- Cycle fingerprint c695e60f21dfe8d627f50d38f1f7070535733b2a7582904559ca23de8bf01001.
def localCycle00341 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 0 4, .distance 4 5, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, 0, -1, -1, -1, 0, 0, -3, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, true, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 13 0, .triangle 12 0, .triangle 22 0, .gapLower 1 2, .triangle 15 1, .gapLower 1 0, .thetaLower 1]

-- Cycle fingerprint c714e7774525f5ef8744fd43361d16db065ef9db239627a93dd8932982378e71.
def localCycle00342 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 4, .distance 1 3, .distance 1 2, .theta 1, .distance 0 1, .distance 0 4, .distance 4 5, .distance 5 6, .distance 1 5, .distance 1 4]
    constant := ![0, 0, -1, 3, 0, -1, -1, -1, 0]
    coefficient := ![0, 0, 0, 1, 0, 0, 0, 0, 0]
    strict := ![true, true, false, false, true, false, false, false, false] }
  origin := ![.triangle 19 1, .triangle 15 1, .corridorLower 1 2, .corridorUpper 0 1, .triangle 2 2, .triangle 12 0, .triangle 34 0, .triangle 24 0, .gapLower 1 3]

-- Cycle fingerprint c71aea3b8e1b612c95285a2cb740d65607d576039b4331719e725438c8edd690.
def localCycle00343 : Cycle where
  length := 8
  data := {
    node := ![.distance 5 6, .distance 1 5, .distance 1 3, .distance 1 2, .theta 1, .distance 0 1, .distance 0 4, .distance 0 5, .distance 5 6]
    constant := ![-1, 0, 0, -1, 1, 0, 0, -1]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![false, false, true, false, false, true, true, false] }
  origin := ![.triangle 24 0, .gapLower 1 2, .triangle 15 1, .corridorLower 1 2, .gapLower 1 6, .triangle 2 2, .triangle 12 2, .triangle 14 0]

-- Cycle fingerprint c755e41d8393c498f963e76c52ac40a2dcc3a343776f990b7b69b7f455729e3b.
def localCycle00344 : Cycle where
  length := 13
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 4, .distance 2 3, .distance 3 6, .distance 4 6, .distance 5 6, .distance 1 5, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, -1, -1, -1, 0, 0, -1, 0, 0, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, false, true, true, true, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 0, .triangle 25 0, .triangle 27 0, .triangle 32 1, .triangle 34 1, .triangle 24 0, .triangle 22 1, .triangle 19 1, .triangle 15 1, .corridorLower 1 2, .thetaLower 1]

-- Cycle fingerprint c76fab4beab994c4eeb57aed81202df5b2a834fc80188bbd95bc1a682ae4fddd.
def localCycle00345 : Cycle where
  length := 7
  data := {
    node := ![.theta 1, .distance 0 1, .distance 1 6, .distance 1 4, .distance 1 5, .distance 1 3, .distance 1 2, .theta 1]
    constant := ![2, -1, 0, 0, -2, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, true, false] }
  origin := ![.gapLower 1 6, .triangle 4 0, .triangle 23 1, .triangle 22 2, .gapLower 1 2, .triangle 15 1, .corridorLower 1 2]

-- Cycle fingerprint c82196962e58d7c4e8564dc9ba61bf0195644410e98433a770a1ec47fb670a77.
def localCycle00346 : Cycle where
  length := 6
  data := {
    node := ![.distance 1 6, .distance 1 5, .distance 1 3, .theta 1, .distance 0 1, .distance 1 4, .distance 1 6]
    constant := ![0, -2, -1, 3, -2, 0]
    coefficient := ![0, 0, 0, 1, 0, 0]
    strict := ![true, false, false, false, false, true] }
  origin := ![.triangle 24 1, .gapLower 1 2, .corridorLower 1 3, .corridorUpper 0 1, .gapLower 1 5, .triangle 23 2]

-- Cycle fingerprint c8af4d9cea94309ccda8fcf7933c9a7eb5ac0a1beea9d258d4b3116a76cee4b2.
def localCycle00347 : Cycle where
  length := 14
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 2 6, .distance 1 6, .distance 0 1, .distance 1 2, .distance 1 3, .distance 3 4, .distance 2 4, .distance 4 5, .theta 4, .zero]
    constant := ![0, 3, 0, 0, 0, 0, -1, -1, 0, -1, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, true, true, false, false, true, false, true, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 27 2, .triangle 18 2, .triangle 4 0, .triangle 0 0, .triangle 15 2, .triangle 19 0, .triangle 25 2, .triangle 28 0, .corridorLower 4 5, .thetaLower 4]

-- Cycle fingerprint c8ec2ff764ef1fdb37a538da529ae4a1fcf0f8b14b2f51ca45e45e62a330a0e5.
def localCycle00348 : Cycle where
  length := 7
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 4, .distance 4 5, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1]
    constant := ![2, 0, -1, -1, 0, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false] }
  origin := ![.gapLower 1 6, .triangle 2 2, .triangle 12 0, .triangle 22 0, .gapLower 1 2, .gapLower 1 1, .corridorLower 1 2]

-- Cycle fingerprint caa37550510869dcd0d4445461066bb21a9f23b0442cb2d9805da4d315f73a8b.
def localCycle00349 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 4, .distance 0 5, .distance 5 6, .distance 1 5, .distance 1 3, .distance 1 2, .theta 1, .distance 0 1, .distance 0 4]
    constant := ![0, -1, -1, 0, -3, -1, 3, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 0]
    strict := ![true, false, false, false, false, false, false, true] }
  origin := ![.triangle 12 2, .triangle 14 0, .triangle 24 0, .gapLower 1 2, .gapLower 1 1, .corridorLower 1 2, .corridorUpper 0 1, .triangle 2 2]

-- Cycle fingerprint cab523f35165a275fec7cea09b252a999877dda1c0f737024e76e9ced3d3c469.
def localCycle00350 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 4 5, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1, .distance 0 1]
    constant := ![0, -1, -1, 0, 0, -2, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![true, false, false, false, true, false, false] }
  origin := ![.triangle 2 2, .triangle 12 0, .triangle 22 0, .gapLower 1 2, .triangle 15 1, .gapLower 1 0, .corridorUpper 0 1]

-- Cycle fingerprint cbaadc2b4d8dacc7e51b0296b7616a4b91d133361a634b5a19d3c0f15b82813d.
def localCycle00351 : Cycle where
  length := 14
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 2 6, .distance 1 6, .distance 0 1, .distance 1 2, .distance 2 3, .distance 3 5, .distance 3 4, .theta 3, .theta 2, .zero]
    constant := ![0, 3, 0, 0, 0, 0, -1, -1, -1, -1, 0, -1, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, true, true, false, false, false, false, true, false, true, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 27 2, .triangle 18 2, .triangle 4 0, .triangle 0 0, .triangle 15 0, .triangle 26 0, .triangle 31 1, .corridorLower 3 4, .thetaNext 2, .thetaLower 2]

-- Cycle fingerprint cbf2a046a34307cee8a33973ff8529586d5b35bfe7d301df2a64527f486d1ef6.
def localCycle00352 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 2, .theta 1, .zero, .theta 6, .distance 5 6, .distance 3 5, .distance 2 3, .distance 1 2]
    constant := ![-3, 0, 0, 3, -1, -1, -1]
    coefficient := ![0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 1 0, .thetaLower 1, .thetaUpper 6, .corridorUpper 5 6, .triangle 33 0, .triangle 26 0, .triangle 15 0]

-- Cycle fingerprint cc4f95c8bab5c7b71170ca4bde463de6abcc200593f7e8a60a2673b7bc03894e.
def localCycle00353 : Cycle where
  length := 12
  data := {
    node := ![.distance 2 5, .distance 2 3, .distance 1 2, .theta 1, .distance 0 1, .distance 1 4, .distance 4 6, .distance 4 5, .theta 4, .distance 3 4, .distance 3 5, .distance 5 6, .distance 2 5]
    constant := ![0, -1, -2, 3, -2, -1, 0, -1, 3, 0, -1, -1]
    coefficient := ![0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, false, false, true, false, false] }
  origin := ![.gapLower 2 3, .triangle 15 0, .gapLower 1 0, .corridorUpper 0 1, .gapLower 1 5, .triangle 23 0, .triangle 34 1, .corridorLower 4 5, .corridorUpper 3 4, .triangle 31 2, .triangle 33 0, .triangle 30 0]

-- Cycle fingerprint cc99576c139647ffffeb4aee17b9a6a9cd6f5f57b988c31c0dbd3d6ea14a0fff.
def localCycle00354 : Cycle where
  length := 5
  data := {
    node := ![.distance 1 4, .distance 1 3, .theta 1, .distance 0 1, .distance 1 6, .distance 1 4]
    constant := ![-2, -1, 3, -2, 0]
    coefficient := ![0, 0, 1, 0, 0]
    strict := ![false, false, false, false, true] }
  origin := ![.gapLower 1 2, .corridorLower 1 3, .corridorUpper 0 1, .gapLower 1 5, .triangle 23 1]

-- Cycle fingerprint cd2556a937892e3e887a2766a6e06f88ae951ae080b2f57706e8c55ed0b46cd2.
def localCycle00355 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 2, .theta 1, .zero, .theta 4, .distance 3 4, .distance 3 5, .distance 5 6, .distance 4 5, .distance 1 4, .distance 1 3, .distance 1 2]
    constant := ![-2, 0, 0, 3, 0, -1, -1, -1, -2, 0]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, false, false, true] }
  origin := ![.gapLower 1 0, .thetaLower 1, .thetaUpper 4, .corridorUpper 3 4, .triangle 31 2, .triangle 33 0, .triangle 34 0, .triangle 22 0, .gapLower 1 2, .triangle 15 1]

-- Cycle fingerprint cd2d03da3a62f1a84535fbd8c2fdd03eb89c34ca4822221022e09160bc0b3dd2.
def localCycle00356 : Cycle where
  length := 8
  data := {
    node := ![.distance 2 4, .distance 2 5, .distance 5 6, .distance 4 5, .distance 1 5, .distance 1 4, .theta 4, .distance 3 4, .distance 2 4]
    constant := ![0, -1, -1, 0, -2, 0, 3, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 0]
    strict := ![true, false, false, true, false, false, false, true] }
  origin := ![.triangle 28 2, .triangle 30 0, .triangle 34 0, .triangle 22 2, .gapLower 1 3, .gapLower 4 0, .corridorUpper 3 4, .triangle 25 2]

-- Cycle fingerprint ce19faa6dc5a6132fd57f439170a6199768b2afea48048bc9a52b3c232028e4d.
def localCycle00357 : Cycle where
  length := 3
  data := {
    node := ![.distance 4 6, .distance 1 4, .distance 1 6, .distance 4 6]
    constant := ![2, -3, 0]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.gapUpper 4 2, .gapLower 1 4, .triangle 23 1]

-- Cycle fingerprint cfe59859940d7804a0c118fcc394d1e7b5cefc571e405e0111e59bc55164fbfc.
def localCycle00358 : Cycle where
  length := 8
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 5, .distance 5 6, .distance 1 6, .distance 1 5, .distance 1 4, .distance 1 3, .theta 1]
    constant := ![4, 0, -1, 0, -2, 0, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, true, false, false] }
  origin := ![.gapLower 1 6, .triangle 3 2, .triangle 14 0, .triangle 24 2, .gapLower 1 4, .triangle 22 1, .gapLower 1 2, .corridorLower 1 3]

-- Cycle fingerprint d08f73ecb8d30a84e1427352ff3b8b2f800cdd1fa4cf5f1bd164c0327c6667ea.
def localCycle00359 : Cycle where
  length := 8
  data := {
    node := ![.distance 1 5, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1, .distance 0 1, .distance 0 5, .distance 5 6, .distance 1 5]
    constant := ![0, 0, 0, -1, 2, 0, -1, -1]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![false, true, true, false, false, true, false, false] }
  origin := ![.gapLower 1 3, .triangle 19 1, .triangle 15 1, .corridorLower 1 2, .gapLower 1 6, .triangle 3 2, .triangle 14 0, .triangle 24 0]

-- Cycle fingerprint d0c02935cee65de9c965c1001c0a9bf527348f1810265316d7a9cea226ca00a5.
def localCycle00360 : Cycle where
  length := 5
  data := {
    node := ![.distance 1 4, .theta 1, .distance 0 1, .distance 1 5, .distance 1 6, .distance 1 4]
    constant := ![-1, 3, -1, -2, -2]
    coefficient := ![0, 1, 0, 0, 0]
    strict := ![false, false, false, false, false] }
  origin := ![.corridorLower 1 4, .corridorUpper 0 1, .triangle 3 0, .gapLower 1 4, .gapLower 1 3]

-- Cycle fingerprint d1237381d93bfb0ea53ba3ac5dc2c60af1aefa7db246a186eaf00ced2debca73.
def localCycle00361 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 6, .distance 1 6, .distance 1 5, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1, .zero]
    constant := ![0, 2, 0, 0, -2, 0, -2, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, true, false, false] }
  origin := ![.thetaUpper 6, .gapUpper 6 0, .triangle 24 1, .triangle 22 1, .gapLower 1 2, .triangle 15 1, .gapLower 1 0, .thetaLower 1]

-- Cycle fingerprint d14eb4a65bca3bb40a170776684ca07e4e56867ddcd54a98f236973a5f060808.
def localCycle00362 : Cycle where
  length := 6
  data := {
    node := ![.distance 1 5, .theta 1, .zero, .theta 6, .distance 1 6, .distance 1 4, .distance 1 5]
    constant := ![-1, 0, 0, 2, -2, -2]
    coefficient := ![0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, true, false, false] }
  origin := ![.corridorLower 1 5, .thetaLower 1, .thetaUpper 6, .gapUpper 6 0, .gapLower 1 4, .gapLower 1 3]

-- Cycle fingerprint d2050bbaf7fe21347bc44bfb3e5cc1e05f07b2c48308608f630243e20b0fc2f2.
def localCycle00363 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 6, .distance 1 6, .distance 1 4, .distance 1 5, .distance 1 3, .distance 1 2, .theta 1, .zero]
    constant := ![0, 2, 0, 0, -2, 0, -2, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, true, false, false] }
  origin := ![.thetaUpper 6, .gapUpper 6 0, .triangle 23 1, .triangle 22 2, .gapLower 1 2, .triangle 15 1, .gapLower 1 0, .thetaLower 1]

-- Cycle fingerprint d25c87b06675fe8a4779678b5de85f08c0919e649ee06ebac4726f87ca6d4761.
def localCycle00364 : Cycle where
  length := 7
  data := {
    node := ![.theta 1, .distance 0 1, .distance 1 5, .distance 1 6, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1]
    constant := ![2, -1, 0, -2, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, true, false] }
  origin := ![.gapLower 1 6, .triangle 3 0, .triangle 24 2, .gapLower 1 3, .triangle 19 1, .triangle 15 1, .corridorLower 1 2]

-- Cycle fingerprint d39ca1e7702955e9ab74f688994661dfa8bbfd950c5c34d4aa1df41e522e0dd5.
def localCycle00365 : Cycle where
  length := 9
  data := {
    node := ![.distance 4 5, .distance 1 4, .distance 1 3, .theta 1, .zero, .theta 6, .distance 5 6, .distance 4 6, .distance 0 4, .distance 4 5]
    constant := ![-1, -3, -1, 0, 0, 3, 0, -1, -1]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, false, false] }
  origin := ![.triangle 22 0, .gapLower 1 2, .corridorLower 1 3, .thetaLower 1, .thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 13 0, .triangle 12 0]

-- Cycle fingerprint d3b7f51d1748a8f6552577bdcf694e536f03720e7b7c6ab161568fd03e441538.
def localCycle00366 : Cycle where
  length := 8
  data := {
    node := ![.distance 1 4, .distance 1 3, .distance 1 2, .theta 1, .distance 0 1, .distance 0 4, .distance 4 6, .distance 4 5, .distance 1 4]
    constant := ![0, -2, -1, 3, 0, -1, 0, -1]
    coefficient := ![0, 0, 0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, true, false] }
  origin := ![.gapLower 1 2, .gapLower 1 1, .corridorLower 1 2, .corridorUpper 0 1, .triangle 2 2, .triangle 13 0, .triangle 34 1, .triangle 22 0]

-- Cycle fingerprint d3ed5ca063015f3f461ab505b7e961982f77530138ace7d36b668b20e0dd97c8.
def localCycle00367 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 4, .distance 2 3, .distance 3 6, .distance 4 6, .distance 0 4, .theta 0, .zero]
    constant := ![0, 3, -1, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 0, .triangle 25 0, .triangle 27 0, .triangle 32 1, .triangle 13 0, .corridorLower 0 4, .thetaLower 0]

-- Cycle fingerprint d60965ad460a3c6a272f082486d4af19e3784e40961b65a61cfd18808a0203ee.
def localCycle00368 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 5, .distance 1 6, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1, .distance 0 1, .distance 0 4, .distance 4 5, .distance 1 5]
    constant := ![0, -2, 0, 0, -2, 3, 0, -1, 0]
    coefficient := ![0, 0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![true, false, false, true, false, false, true, false, true] }
  origin := ![.triangle 24 2, .gapLower 1 3, .gapLower 1 2, .triangle 15 1, .gapLower 1 0, .corridorUpper 0 1, .triangle 2 2, .triangle 12 0, .triangle 22 2]

-- Cycle fingerprint d6af48eba54d5d3bc06a631a20e8c5b476e16b85eea2ca337b38974ff1cf6604.
def localCycle00369 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 0 5, .distance 5 6, .distance 1 6, .distance 1 5, .distance 1 3, .theta 1, .distance 0 1]
    constant := ![0, 0, -1, 0, -2, -2, -1, 4]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![true, true, false, true, false, false, false, false] }
  origin := ![.triangle 2 2, .triangle 12 2, .triangle 14 0, .triangle 24 2, .gapLower 1 3, .gapLower 1 2, .corridorLower 1 3, .gapLower 1 6]

-- Cycle fingerprint d6bee97f5c1b9ba9c1f8c8aa73dcd1d22a46f3d346d2843e8fc9ade15573df01.
def localCycle00370 : Cycle where
  length := 10
  data := {
    node := ![.distance 3 4, .distance 2 4, .distance 4 5, .distance 5 6, .distance 1 5, .distance 1 4, .distance 1 3, .theta 1, .zero, .theta 4, .distance 3 4]
    constant := ![0, -1, -1, -1, 0, -2, -1, 0, 0, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 1, 1]
    strict := ![true, false, false, false, false, false, false, false, false, false] }
  origin := ![.triangle 25 2, .triangle 28 0, .triangle 34 0, .triangle 24 0, .gapLower 1 3, .gapLower 1 2, .corridorLower 1 3, .thetaLower 1, .thetaUpper 4, .corridorUpper 3 4]

-- Cycle fingerprint d81ba11e68980cf2edbba6cc3ade350dd9ac8487d8fa1afaec7df8d0e0d3d70c.
def localCycle00371 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 4, .distance 4 5, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1, .zero, .theta 6, .distance 5 6, .distance 4 6, .distance 0 4]
    constant := ![-1, -1, 0, 0, -2, 0, 0, 3, 0, -1]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, true, false, false, false, false, true, false] }
  origin := ![.triangle 12 0, .triangle 22 0, .gapLower 1 2, .triangle 15 1, .gapLower 1 0, .thetaLower 1, .thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 13 0]

-- Cycle fingerprint d83c7a90fa3b1341e81b05bd142467b8cfe71812bbee765e8831bd78f6af4c08.
def localCycle00372 : Cycle where
  length := 5
  data := {
    node := ![.theta 1, .distance 0 1, .distance 1 5, .distance 1 4, .distance 1 3, .theta 1]
    constant := ![3, -1, 0, -3, -1]
    coefficient := ![1, 0, 0, 0, 0]
    strict := ![false, false, true, false, false] }
  origin := ![.corridorUpper 0 1, .triangle 3 0, .triangle 22 1, .gapLower 1 2, .corridorLower 1 3]

-- Cycle fingerprint d8e91365e12e4799c73408eafe363aa1575232abcef10a44c14b89ac60a92fa5.
def localCycle00373 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 5, .distance 5 6, .distance 1 5, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1, .distance 0 1, .distance 0 5]
    constant := ![-1, -1, 0, 0, -3, -1, 4, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 0]
    strict := ![false, false, false, true, false, false, false, true] }
  origin := ![.triangle 14 0, .triangle 24 0, .gapLower 1 3, .triangle 19 1, .gapLower 1 1, .corridorLower 1 2, .gapLower 1 6, .triangle 3 2]

-- Cycle fingerprint d8f28fe6f6e4b9f739a593cc9bbbea8ac1cbddb9beddaa32b84fe4d27aab4d3d.
def localCycle00374 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 2 4, .distance 4 5, .distance 5 6, .distance 1 5, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, 0, -1, -1, -1, -2, 0, -2, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, true, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 28 0, .triangle 34 0, .triangle 24 0, .gapLower 1 3, .triangle 19 1, .gapLower 1 1, .corridorLower 1 2, .thetaLower 1]

-- Cycle fingerprint dbd544b4eed28e3795f64e026e5dc32ae783ec6805f7124b02a379cfda623c4d.
def localCycle00375 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 2 5, .distance 5 6, .distance 4 6, .distance 1 4, .distance 4 5, .theta 4]
    constant := ![3, 0, 0, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 28 2, .triangle 30 0, .triangle 34 2, .triangle 23 0, .triangle 22 0, .corridorLower 4 5]

-- Cycle fingerprint dbdf77c43e00f16d3fc5fd1265e9b351bfaed8aa850913cc35266ed6d8f0a88a.
def localCycle00376 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 4, .distance 2 3, .distance 3 6, .distance 4 6, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, -1, -1, -1, 0, -1, 0, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, true, true, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 0, .triangle 25 0, .triangle 27 0, .triangle 32 1, .triangle 23 0, .triangle 19 1, .triangle 15 1, .corridorLower 1 2, .thetaLower 1]

-- Cycle fingerprint ddab2fcef08b96a19f71e8feb7b8f752d0907dedaf22772658d02143d0b6d3ea.
def localCycle00377 : Cycle where
  length := 9
  data := {
    node := ![.distance 2 3, .distance 1 2, .theta 1, .zero, .theta 4, .distance 3 4, .distance 3 5, .distance 5 6, .distance 2 5, .distance 2 3]
    constant := ![-1, -3, 0, 0, 3, 0, -1, -1, 0]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, false, false] }
  origin := ![.triangle 15 0, .gapLower 1 0, .thetaLower 1, .thetaUpper 4, .corridorUpper 3 4, .triangle 31 2, .triangle 33 0, .triangle 30 0, .gapLower 2 3]

-- Cycle fingerprint deb9972017391cabdca6ba59684bdd498fc960243f5b9f6b4c7dbab11cefd22b.
def localCycle00378 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 4, .distance 1 3, .distance 1 2, .theta 1, .distance 0 1, .distance 0 4, .distance 0 5, .distance 5 6, .distance 4 5, .distance 1 4]
    constant := ![0, 0, -1, 3, 0, 0, -1, -1, -1]
    coefficient := ![0, 0, 0, 1, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, true, false, false, false] }
  origin := ![.gapLower 1 2, .triangle 15 1, .corridorLower 1 2, .corridorUpper 0 1, .triangle 2 2, .triangle 12 2, .triangle 14 0, .triangle 34 0, .triangle 22 0]

-- Cycle fingerprint dee4fed0b40c9ec077d1a8eb9e966a3653379d7ec1f4cf531ff2e9b2e26fd759.
def localCycle00379 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 5 6, .distance 3 6, .distance 0 3, .distance 3 5, .distance 2 3, .distance 3 4, .theta 3, .zero]
    constant := ![0, 3, -1, 0, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 34 0, .triangle 33 2, .triangle 11 0, .triangle 10 0, .triangle 26 0, .triangle 25 0, .corridorLower 3 4, .thetaLower 3]

-- Cycle fingerprint df1542b705d15781950c484f3c154717f34ab8ad0a9d5aeb5a49d65f63ece05e.
def localCycle00380 : Cycle where
  length := 8
  data := {
    node := ![.distance 5 6, .distance 1 5, .distance 1 3, .distance 1 2, .theta 1, .distance 0 1, .distance 0 4, .distance 0 5, .distance 5 6]
    constant := ![-1, -2, 0, -1, 2, 0, 0, -1]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![false, false, true, false, false, true, true, false] }
  origin := ![.triangle 24 0, .gapLower 1 2, .triangle 15 1, .corridorLower 1 2, .gapLower 1 6, .triangle 2 2, .triangle 12 2, .triangle 14 0]

-- Cycle fingerprint df4255978739587a2819c77cab343c8b302313163418eac6f47519428bfdcf03.
def localCycle00381 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 4, .distance 1 3, .distance 1 2, .theta 1, .distance 0 1, .distance 0 4, .distance 4 5, .distance 1 4]
    constant := ![-2, -2, -1, 4, 0, -1, -1]
    coefficient := ![0, 0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false] }
  origin := ![.gapLower 1 2, .gapLower 1 1, .corridorLower 1 2, .gapLower 1 6, .triangle 2 2, .triangle 12 0, .triangle 22 0]

-- Cycle fingerprint df8b2ffd79df15b1e6a74fa9ee0aa3411525ad365226c884c4a3b4783ae60c82.
def localCycle00382 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 4, .distance 4 5, .distance 2 4, .distance 2 3, .distance 1 2, .theta 1, .theta 0, .zero]
    constant := ![0, 3, 0, -1, -1, -1, 0, -1, -1, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, true, false, false, true, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 0, .triangle 31 0, .triangle 28 0, .triangle 25 1, .triangle 15 0, .corridorLower 1 2, .thetaNext 0, .thetaLower 0]

-- Cycle fingerprint e00a473c2ef422b6e2a32b2100c8005c4b860b1703e1e0041ceb865f3bf7a6ad.
def localCycle00383 : Cycle where
  length := 7
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 6, .distance 0 4, .distance 4 5, .distance 1 4, .distance 1 3, .theta 1]
    constant := ![2, 0, 0, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, true, false] }
  origin := ![.gapLower 1 6, .triangle 4 2, .triangle 13 1, .triangle 12 0, .triangle 22 0, .triangle 19 1, .corridorLower 1 3]

-- Cycle fingerprint e04208f35c26a3f0ceb51bcd8623cfe051531bcad2b997cf8363d546415f178f.
def localCycle00384 : Cycle where
  length := 9
  data := {
    node := ![.distance 5 6, .distance 1 6, .distance 1 5, .distance 1 3, .distance 1 2, .theta 1, .distance 0 1, .distance 0 4, .distance 0 5, .distance 5 6]
    constant := ![0, -2, 0, 0, -2, 3, 0, 0, -1]
    coefficient := ![0, 0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![true, false, false, true, false, false, true, true, false] }
  origin := ![.triangle 24 2, .gapLower 1 3, .gapLower 1 2, .triangle 15 1, .gapLower 1 0, .corridorUpper 0 1, .triangle 2 2, .triangle 12 2, .triangle 14 0]

-- Cycle fingerprint e0f79476b5b18e7adf646cb0d984e52d9f07a7d5349603c567dc273c95863781.
def localCycle00385 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 0 4, .distance 0 5, .distance 5 6, .distance 4 6, .distance 1 4, .distance 4 5, .theta 4]
    constant := ![3, 0, 0, 0, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, true, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 6 2, .triangle 12 2, .triangle 14 0, .triangle 34 2, .triangle 23 0, .triangle 22 0, .corridorLower 4 5]

-- Cycle fingerprint e10f1a0a9681f21d28aa61300bf4ce7f7172e710512d152baf2f5def1c81a1e3.
def localCycle00386 : Cycle where
  length := 7
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 6, .distance 0 4, .distance 4 5, .distance 1 5, .distance 1 4, .theta 1]
    constant := ![2, 0, 0, -1, 0, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, false] }
  origin := ![.gapLower 1 6, .triangle 4 2, .triangle 13 1, .triangle 12 0, .triangle 22 2, .gapLower 1 3, .corridorLower 1 4]

-- Cycle fingerprint e1e49daf45d0ddccc22269a3b5e6072afa9945b958097fd226ed860e1aaaeadf.
def localCycle00387 : Cycle where
  length := 7
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 5, .distance 5 6, .distance 1 5, .distance 1 4, .distance 1 2, .theta 1]
    constant := ![2, 0, -1, -1, 0, 0, -2]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, true, false] }
  origin := ![.gapLower 1 6, .triangle 3 2, .triangle 14 0, .triangle 24 0, .gapLower 1 3, .triangle 16 1, .gapLower 1 0]

-- Cycle fingerprint e2730657fa48e41f5353eb275b47126006f51cff4ad0be4fe621905888f6f033.
def localCycle00388 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 4, .distance 0 5, .distance 5 6, .distance 1 5, .distance 1 3, .distance 1 2, .theta 1, .distance 0 1, .distance 0 4]
    constant := ![0, -1, -1, 0, -2, -2, 3, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 0]
    strict := ![true, false, false, false, false, false, false, true] }
  origin := ![.triangle 12 2, .triangle 14 0, .triangle 24 0, .gapLower 1 2, .gapLower 1 1, .gapLower 1 0, .corridorUpper 0 1, .triangle 2 2]

-- Cycle fingerprint e2b66063a93cbc068573e823cc51ba036775f31582bed56cdbe31049ed87d019.
def localCycle00389 : Cycle where
  length := 8
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 5, .distance 5 6, .distance 1 5, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1]
    constant := ![4, 0, -1, -1, -2, 0, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, true, false, false] }
  origin := ![.gapLower 1 6, .triangle 3 2, .triangle 14 0, .triangle 24 0, .gapLower 1 3, .triangle 19 1, .gapLower 1 1, .corridorLower 1 2]

-- Cycle fingerprint e381557c709bc79049e8e7cfd35f74b1c1636c065baf1010698f655cfaa65c87.
def localCycle00390 : Cycle where
  length := 8
  data := {
    node := ![.theta 5, .distance 4 5, .distance 5 6, .distance 1 6, .distance 0 1, .distance 1 2, .distance 2 3, .distance 3 5, .theta 5]
    constant := ![3, -1, 0, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false] }
  origin := ![.corridorUpper 4 5, .triangle 34 0, .triangle 24 2, .triangle 4 0, .triangle 0 0, .triangle 15 0, .triangle 26 0, .gapLower 5 0]

-- Cycle fingerprint e3ace8397b166097bc74160ab13f3ebf203049c9b3025084dae8a7fae5a2f4a2.
def localCycle00391 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 3 4, .distance 3 5, .distance 5 6, .distance 4 6, .distance 1 4, .distance 4 5, .theta 4]
    constant := ![3, 0, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 31 2, .triangle 33 0, .triangle 34 2, .triangle 23 0, .triangle 22 0, .corridorLower 4 5]

-- Cycle fingerprint e3b10ecda5e6beff830c49960087739b57d3bca488b2c14ef47d434daa5e0c21.
def localCycle00392 : Cycle where
  length := 10
  data := {
    node := ![.theta 3, .distance 3 6, .distance 2 6, .distance 1 6, .distance 0 1, .distance 1 2, .distance 2 3, .distance 2 4, .distance 4 5, .distance 3 4, .theta 3]
    constant := ![4, 0, 0, -1, -1, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, false, true, false, false, false] }
  origin := ![.gapLower 3 6, .triangle 27 2, .triangle 18 2, .triangle 4 0, .triangle 0 0, .triangle 15 0, .triangle 25 2, .triangle 28 0, .triangle 31 0, .corridorLower 3 4]

-- Cycle fingerprint e521cb46d008e552f6ba5c11320277377a4c5eb784540103e8db572fd1953612.
def localCycle00393 : Cycle where
  length := 10
  data := {
    node := ![.distance 3 4, .distance 4 5, .distance 5 6, .distance 1 5, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1, .zero, .theta 4, .distance 3 4]
    constant := ![-1, -1, -1, 0, 0, -2, -1, 0, 0, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 1, 1]
    strict := ![false, false, false, false, true, false, false, false, false, false] }
  origin := ![.triangle 31 0, .triangle 34 0, .triangle 24 0, .gapLower 1 3, .triangle 19 1, .gapLower 1 1, .corridorLower 1 2, .thetaLower 1, .thetaUpper 4, .corridorUpper 3 4]

-- Cycle fingerprint e6e55a423c0f796aacf16580c4a2dd9c16dcfd5cf50ed3d37cf25f03566a8075.
def localCycle00394 : Cycle where
  length := 7
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 4, .distance 4 6, .distance 4 5, .distance 1 4, .distance 1 3, .theta 1]
    constant := ![2, 0, -1, 0, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, false] }
  origin := ![.gapLower 1 6, .triangle 2 2, .triangle 13 0, .triangle 34 1, .triangle 22 0, .gapLower 1 2, .corridorLower 1 3]

-- Cycle fingerprint e7452657dcec7ca0af7f642bf043bedcef8caad11b5ca78ac4c7d740a97516ad.
def localCycle00395 : Cycle where
  length := 5
  data := {
    node := ![.distance 1 3, .distance 1 2, .theta 1, .distance 0 1, .distance 1 6, .distance 1 3]
    constant := ![-2, -1, 3, -2, 0]
    coefficient := ![0, 0, 1, 0, 0]
    strict := ![false, false, false, false, true] }
  origin := ![.gapLower 1 1, .corridorLower 1 2, .corridorUpper 0 1, .gapLower 1 5, .triangle 21 1]

-- Cycle fingerprint e74574ed06bca2174616b7c74d3b94e3e839b71449d1c9dbe46d9550e9108afc.
def localCycle00396 : Cycle where
  length := 6
  data := {
    node := ![.theta 4, .distance 3 4, .distance 4 5, .distance 5 6, .distance 1 5, .distance 1 4, .theta 4]
    constant := ![3, -1, -1, -1, -3, 0]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 31 0, .triangle 34 0, .triangle 24 0, .gapLower 1 3, .gapLower 4 0]

-- Cycle fingerprint e75cdff1aebef091a7cbbe35db1d5ff1dbab69bebf5fe416113bb393e8927869.
def localCycle00397 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 5, .distance 1 6, .distance 1 4, .theta 1, .distance 0 1, .distance 0 4, .distance 4 5, .distance 1 5]
    constant := ![-2, -2, -1, 3, 0, -1, 0]
    coefficient := ![0, 0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, false, true, false, true] }
  origin := ![.gapLower 1 4, .gapLower 1 3, .corridorLower 1 4, .corridorUpper 0 1, .triangle 2 2, .triangle 12 0, .triangle 22 2]

-- Cycle fingerprint e7ca81d31fdb9b7449effe18fe1f9338a09e97947b15e4b9f8e440898af5cb21.
def localCycle00398 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 6, .distance 1 5, .distance 1 4, .theta 1, .distance 0 1, .distance 0 5, .distance 5 6, .distance 1 6]
    constant := ![-2, -2, -1, 4, 0, -1, 0]
    coefficient := ![0, 0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, false, true, false, true] }
  origin := ![.gapLower 1 4, .gapLower 1 3, .corridorLower 1 4, .gapLower 1 6, .triangle 3 2, .triangle 14 0, .triangle 24 2]

-- Cycle fingerprint e976111cc1ef26412e363940a6f4fcd9225405f3dd45e3734cbddd06c8af6217.
def localCycle00399 : Cycle where
  length := 10
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 5 6, .distance 2 5, .distance 2 4, .distance 1 2, .theta 1, .theta 0, .zero, .theta 5]
    constant := ![3, 0, -1, -1, 0, -1, -2, 0, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, false, false, false, false, false, true, false, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 33 0, .triangle 30 0, .gapLower 2 4, .triangle 16 0, .gapLower 1 0, .thetaNext 0, .thetaLower 0, .thetaUpper 5]

-- Cycle fingerprint ea1dfed53b527d72ba517bc98042d438c40781a09989b5e1cdb508e0b43027d5.
def localCycle00400 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 4 5, .distance 5 6, .distance 1 5, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, -1, -1, -1, 0, 0, 0, -3, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, true, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 31 0, .triangle 34 0, .triangle 24 0, .gapLower 1 3, .triangle 19 1, .triangle 15 1, .gapLower 1 0, .thetaLower 1]

-- Cycle fingerprint ea8912dadd869c4373ad995621f62b2ddcabeee57443293062ca4d623a6a7606.
def localCycle00401 : Cycle where
  length := 12
  data := {
    node := ![.distance 2 4, .distance 2 5, .distance 5 6, .distance 4 5, .distance 1 5, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1, .zero, .theta 4, .distance 3 4, .distance 2 4]
    constant := ![0, -1, -1, 0, -2, 0, 0, -2, 0, 0, 3, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![true, false, false, false, false, false, true, false, false, false, false, true] }
  origin := ![.triangle 28 2, .triangle 30 0, .triangle 34 0, .gapLower 5 1, .gapLower 1 3, .gapLower 1 2, .triangle 15 1, .gapLower 1 0, .thetaLower 1, .thetaUpper 4, .corridorUpper 3 4, .triangle 25 2]

-- Cycle fingerprint eacfb7eff6df630f86dbb110224d97e0573a7ea656fcf2241a2c3d5570ec1d82.
def localCycle00402 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 6, .distance 1 5, .distance 1 4, .theta 4, .distance 3 4, .distance 4 5, .distance 5 6, .distance 1 6]
    constant := ![-2, -2, 0, 3, -1, -1, 0]
    coefficient := ![0, 0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true] }
  origin := ![.gapLower 1 4, .gapLower 1 3, .gapLower 4 0, .corridorUpper 3 4, .triangle 31 0, .triangle 34 0, .triangle 24 2]

-- Cycle fingerprint eae3112076efe4a863a75e1134c93b6086519815f6cf334bd8e12fdc33659375.
def localCycle00403 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 2, .theta 1, .distance 0 1, .distance 1 5, .distance 5 6, .theta 5, .distance 4 5, .distance 3 4, .distance 2 3, .distance 1 2]
    constant := ![-1, 1, -1, -1, -1, 3, -1, -1, -1]
    coefficient := ![0, 1, 0, 0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false, false] }
  origin := ![.corridorLower 1 2, .gapLower 1 6, .triangle 3 0, .triangle 24 0, .corridorLower 5 6, .corridorUpper 4 5, .triangle 31 0, .triangle 25 0, .triangle 15 0]

-- Cycle fingerprint eb33b60130245e9d137dcfb28e6715c74f87d97a063e80155b6a9720d12520ad.
def localCycle00404 : Cycle where
  length := 6
  data := {
    node := ![.distance 1 5, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1, .distance 0 1, .distance 1 5]
    constant := ![0, -2, 0, -1, 2, -1]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![true, false, true, false, false, false] }
  origin := ![.triangle 22 1, .gapLower 1 2, .triangle 15 1, .corridorLower 1 2, .gapLower 1 6, .triangle 3 0]

-- Cycle fingerprint ed51f1478def11fa1101a2187c343ec091ad56e5ccdae95d0f7152fb5f0ef5e1.
def localCycle00405 : Cycle where
  length := 10
  data := {
    node := ![.theta 1, .zero, .theta 4, .distance 3 4, .distance 3 5, .distance 5 6, .distance 4 5, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1]
    constant := ![0, 0, 3, 0, -1, -1, -1, 0, -2, -2]
    coefficient := ![0, 1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, false, false, false] }
  origin := ![.thetaLower 1, .thetaUpper 4, .corridorUpper 3 4, .triangle 31 2, .triangle 33 0, .triangle 34 0, .triangle 22 0, .gapLower 1 2, .gapLower 1 1, .gapLower 1 0]

-- Cycle fingerprint ed73a28f0f60d1f6db2490373e87d0dae18ad24c091f7e71277c055a728f5bec.
def localCycle00406 : Cycle where
  length := 11
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 4 5, .distance 5 6, .distance 1 5, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1, .zero, .theta 4]
    constant := ![3, 0, -1, -1, -1, 0, -2, -2, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, false, false, false, true, false, false, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 28 0, .triangle 34 0, .triangle 24 0, .triangle 22 1, .gapLower 1 2, .gapLower 1 1, .corridorLower 1 2, .thetaLower 1, .thetaUpper 4]

-- Cycle fingerprint edbe60cda2c32c7d190e2aa724b0d1506ffcc849021dd67f9f011f043261a916.
def localCycle00407 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 3 5, .distance 5 6, .distance 4 6, .distance 2 4, .distance 0 4, .distance 4 5, .theta 4]
    constant := ![3, 0, -1, 0, -1, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, true, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 31 2, .triangle 33 0, .triangle 34 2, .triangle 29 0, .triangle 6 2, .triangle 12 0, .corridorLower 4 5]

-- Cycle fingerprint edfa5d234723d52b9cdd983552054b960a6d27ac963e7a21af49a76b516c811d.
def localCycle00408 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 6, .distance 1 5, .distance 1 2, .theta 1, .distance 0 1, .distance 0 4, .distance 4 6, .distance 1 6]
    constant := ![-2, 0, -2, 3, 0, -1, 0]
    coefficient := ![0, 0, 0, 1, 0, 0, 0]
    strict := ![false, true, false, false, true, false, true] }
  origin := ![.gapLower 1 4, .triangle 17 1, .gapLower 1 0, .corridorUpper 0 1, .triangle 2 2, .triangle 13 0, .triangle 23 2]

-- Cycle fingerprint ee95785255b16eef7a4d51f0463e31264c6551abaac1d5c69eea3c87a4e0b4f3.
def localCycle00409 : Cycle where
  length := 6
  data := {
    node := ![.theta 4, .distance 3 4, .distance 0 3, .distance 3 6, .distance 5 6, .distance 4 5, .theta 4]
    constant := ![3, -1, -1, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 9 0, .triangle 11 0, .triangle 33 1, .triangle 34 0, .corridorLower 4 5]

-- Cycle fingerprint efc02ac09687ee8c46d773ae6a79217994445b8ad5087eb3d980a51abea5db34.
def localCycle00410 : Cycle where
  length := 12
  data := {
    node := ![.distance 2 4, .distance 2 5, .distance 5 6, .distance 4 5, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 2 4]
    constant := ![0, -1, -1, -1, -2, 0, -2, 0, 0, 0, 3, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![true, false, false, false, false, true, false, true, false, false, false, true] }
  origin := ![.triangle 28 2, .triangle 30 0, .triangle 34 0, .triangle 22 0, .gapLower 1 2, .triangle 15 1, .gapLower 1 0, .thetaNext 0, .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 25 2]

-- Cycle fingerprint f1309f3b5e43f537d3d64dff0430d186baca95743b88a4de1aa087ace16d7431.
def localCycle00411 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 3, .distance 1 2, .theta 1, .distance 0 1, .distance 1 5, .distance 1 6, .distance 1 4, .distance 1 3]
    constant := ![-2, -1, 3, -1, 0, -2, 0]
    coefficient := ![0, 0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, true] }
  origin := ![.gapLower 1 1, .corridorLower 1 2, .corridorUpper 0 1, .triangle 3 0, .triangle 24 2, .gapLower 1 3, .triangle 19 1]

-- Cycle fingerprint f1b1e88221ad00ca778f6a8a660cfab10d5ddbb0fd5541643c72717fac8ca18d.
def localCycle00412 : Cycle where
  length := 11
  data := {
    node := ![.distance 1 2, .theta 1, .zero, .theta 4, .distance 3 4, .distance 2 4, .distance 4 6, .distance 0 4, .distance 4 5, .distance 1 4, .distance 1 3, .distance 1 2]
    constant := ![-1, 0, 0, 3, 0, -1, -1, -1, -1, 0, 0]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, false, false, true, true] }
  origin := ![.corridorLower 1 2, .thetaLower 1, .thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 29 0, .triangle 13 0, .triangle 12 0, .triangle 22 0, .triangle 19 1, .triangle 15 1]

-- Cycle fingerprint f34fd7af36d02f599b969821f2e7288927dc344f25f7b7546d1325ffe1fa70e9.
def localCycle00413 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 5, .distance 5 6, .distance 1 5, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1, .distance 0 1]
    constant := ![0, -1, -1, 0, -3, 0, -1, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![true, false, false, false, false, true, false, false] }
  origin := ![.triangle 3 2, .triangle 14 0, .triangle 24 0, .gapLower 1 3, .gapLower 1 2, .triangle 15 1, .corridorLower 1 2, .corridorUpper 0 1]

-- Cycle fingerprint f40068904cadff5c258d8da65c3a432502c4880f56ee53bb220c044ba0a14b53.
def localCycle00414 : Cycle where
  length := 5
  data := {
    node := ![.theta 1, .zero, .theta 6, .distance 1 6, .distance 1 4, .theta 1]
    constant := ![0, 0, 2, -3, -1]
    coefficient := ![0, 1, 0, 0, 0]
    strict := ![false, false, true, false, false] }
  origin := ![.thetaLower 1, .thetaUpper 6, .gapUpper 6 0, .gapLower 1 4, .corridorLower 1 4]

-- Cycle fingerprint f4ebcdb9bdcc44c823204f769b2325adacdf14fd9d6c2d9a5c99641abebcf9fc.
def localCycle00415 : Cycle where
  length := 5
  data := {
    node := ![.distance 1 6, .distance 1 4, .distance 1 5, .theta 1, .distance 0 1, .distance 1 6]
    constant := ![0, -2, -1, 2, -1]
    coefficient := ![0, 0, 0, 1, 0]
    strict := ![true, false, false, false, false] }
  origin := ![.triangle 23 1, .gapLower 1 3, .corridorLower 1 5, .gapLower 1 6, .triangle 4 0]

-- Cycle fingerprint f55dde6233a9bbe4b063e56852ea082281522e9be247f616c047dcbb510d1e3c.
def localCycle00416 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 6, .distance 1 5, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1, .distance 0 1]
    constant := ![-3, 0, 0, 0, 0, -1, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, true, true, true, false, false] }
  origin := ![.gapLower 1 5, .triangle 24 1, .triangle 22 1, .triangle 19 1, .triangle 15 1, .corridorLower 1 2, .corridorUpper 0 1]

-- Cycle fingerprint f5dc9aae82d692b65add6b0b2a9b239dd01732d0257ad2cf37e457900f542aba.
def localCycle00417 : Cycle where
  length := 8
  data := {
    node := ![.distance 4 5, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1, .distance 0 1, .distance 0 4, .distance 4 6, .distance 4 5]
    constant := ![-1, 0, 0, -1, 1, 0, -1, 0]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![false, false, true, false, false, true, false, true] }
  origin := ![.triangle 22 0, .gapLower 1 2, .triangle 15 1, .corridorLower 1 2, .gapLower 1 6, .triangle 2 2, .triangle 13 0, .triangle 34 1]

-- Cycle fingerprint f7156ef25103868bc05ec455c00ae0400d9743fcf7c7fd97aa695f8a534fe783.
def localCycle00418 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 4 5, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1, .distance 0 1]
    constant := ![0, -1, -1, -2, 0, -1, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![true, false, false, false, true, false, false] }
  origin := ![.triangle 2 2, .triangle 12 0, .triangle 22 0, .gapLower 1 2, .triangle 15 1, .corridorLower 1 2, .corridorUpper 0 1]

-- Cycle fingerprint f7197ba773ae20e6bf645aec9aaf86303b10bfc18c7b9bc4efc82ee16f6744a9.
def localCycle00419 : Cycle where
  length := 7
  data := {
    node := ![.theta 1, .distance 0 1, .distance 1 6, .distance 1 5, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1]
    constant := ![1, -1, 0, 0, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, true, true, false] }
  origin := ![.gapLower 1 6, .triangle 4 0, .triangle 24 1, .triangle 22 1, .triangle 19 1, .triangle 15 1, .corridorLower 1 2]

-- Cycle fingerprint f771b9b5b0f7d262254ad10f74e986bd49ad5165861322bf2ad3039ab915c80e.
def localCycle00420 : Cycle where
  length := 7
  data := {
    node := ![.theta 1, .distance 0 1, .distance 1 6, .distance 1 5, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1]
    constant := ![2, -1, 0, 0, 0, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, true, false, false] }
  origin := ![.gapLower 1 6, .triangle 4 0, .triangle 24 1, .triangle 22 1, .triangle 19 1, .gapLower 1 1, .corridorLower 1 2]

-- Cycle fingerprint f96b040b940b3c5beedf6622f585ce9173135637ab9356c28251a9a92e32208c.
def localCycle00421 : Cycle where
  length := 7
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 4 5, .distance 5 6, .distance 2 6, .theta 2, .zero]
    constant := ![0, 3, -1, -1, 0, -2, 0]
    coefficient := ![1, 1, 0, 0, 0, -1, 0]
    strict := ![false, false, false, false, true, true, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 31 0, .triangle 34 0, .triangle 30 2, .gapUpper 2 6, .thetaLower 2]

-- Cycle fingerprint f9fab4e7f1853365d452641aed8f4a6fb8695597b27e64242723ba98e995b807.
def localCycle00422 : Cycle where
  length := 11
  data := {
    node := ![.distance 2 5, .distance 5 6, .distance 1 5, .distance 1 4, .distance 1 2, .theta 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 4 5, .distance 2 5]
    constant := ![-1, -1, 0, 0, -2, 0, 0, 0, 3, -1, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, true, false, true, false, false, false, false, true] }
  origin := ![.triangle 30 0, .triangle 24 0, .gapLower 1 3, .triangle 16 1, .gapLower 1 0, .thetaNext 0, .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 31 0, .triangle 28 2]

-- Cycle fingerprint fafcb3afd6cd831ada34d93306e15742ce90cc595e9de48d0ab7750d8c173db2.
def localCycle00423 : Cycle where
  length := 6
  data := {
    node := ![.distance 1 2, .theta 1, .distance 0 1, .distance 1 4, .distance 1 6, .distance 1 5, .distance 1 2]
    constant := ![-2, 3, -1, 0, -2, 0]
    coefficient := ![0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true] }
  origin := ![.gapLower 1 0, .corridorUpper 0 1, .triangle 2 0, .triangle 23 2, .gapLower 1 3, .triangle 17 1]

-- Cycle fingerprint fbc30232be87b68f5783a7bf90a56c8afe68da1a8822b9e54dc501f19b42de24.
def localCycle00424 : Cycle where
  length := 7
  data := {
    node := ![.theta 1, .distance 0 1, .distance 1 6, .distance 1 5, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1]
    constant := ![2, -2, 0, 0, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, true, true, false] }
  origin := ![.gapLower 1 6, .gapLower 1 5, .triangle 24 1, .triangle 22 1, .triangle 19 1, .triangle 15 1, .corridorLower 1 2]

-- Cycle fingerprint fc433a5e3ae79154cbbf5ce8cd836bdbd15ce9eaa1e5b40c9c2d8ec30503658a.
def localCycle00425 : Cycle where
  length := 6
  data := {
    node := ![.distance 1 5, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1, .distance 0 1, .distance 1 5]
    constant := ![0, 0, 0, -2, 2, -1]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![true, true, true, false, false, false] }
  origin := ![.triangle 22 1, .triangle 19 1, .triangle 15 1, .gapLower 1 0, .gapLower 1 6, .triangle 3 0]

-- Cycle fingerprint fcb03297969ed00a9c1b821dcebd7e8a239558c2a6d907eb9b701f811f7bcc57.
def localCycle00426 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 5, .distance 1 4, .distance 1 3, .theta 1, .zero, .theta 6, .distance 1 6, .distance 1 5]
    constant := ![-2, -2, -1, 0, 0, 2, 0]
    coefficient := ![0, 0, 0, 0, 1, 0, 0]
    strict := ![false, false, false, false, false, true, true] }
  origin := ![.gapLower 1 3, .gapLower 1 2, .corridorLower 1 3, .thetaLower 1, .thetaUpper 6, .gapUpper 6 0, .triangle 24 1]

-- Cycle fingerprint fd3ba523112913f3a2c25a755f61b80b1e557224fc91d84f7ee00a3dec6ce484.
def localCycle00427 : Cycle where
  length := 4
  data := {
    node := ![.distance 0 1, .distance 1 5, .distance 1 6, .theta 1, .distance 0 1]
    constant := ![-2, -2, -1, 3]
    coefficient := ![0, 0, 0, 1]
    strict := ![false, false, false, false] }
  origin := ![.gapLower 1 5, .gapLower 1 4, .corridorLower 1 6, .corridorUpper 0 1]

-- Cycle fingerprint fd690ff113784bd2eaef5e070e6cf51108e7a52c2766778e69e4bfc3f0f9b00c.
def localCycle00428 : Cycle where
  length := 12
  data := {
    node := ![.theta 4, .distance 3 4, .distance 4 5, .distance 2 4, .distance 4 6, .distance 5 6, .distance 1 5, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1, .zero, .theta 4]
    constant := ![3, -1, -1, -1, 0, -1, 0, 0, 0, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![false, false, false, false, true, false, false, true, true, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 31 0, .triangle 28 0, .triangle 29 0, .triangle 34 1, .triangle 24 0, .gapLower 1 3, .triangle 19 1, .triangle 15 1, .corridorLower 1 2, .thetaLower 1, .thetaUpper 4]

-- Cycle fingerprint fdfa570387f4dd585746d67c21bb59aa6a09a03b6f13fd3cb9d004fc1f94abda.
def localCycle00429 : Cycle where
  length := 11
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 2 5, .distance 5 6, .distance 4 5, .distance 1 4, .distance 1 3, .theta 1, .theta 0, .zero, .theta 4]
    constant := ![3, 0, 0, -1, -1, -1, -3, -1, 0, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, true, false, false, false, false, false, true, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 28 2, .triangle 30 0, .triangle 34 0, .triangle 22 0, .gapLower 1 2, .corridorLower 1 3, .thetaNext 0, .thetaLower 0, .thetaUpper 4]

-- Cycle fingerprint fe0d7fec3a87b5cfdb1af6ea8f832cfe8da51bec70a2786e7f47c817480b732b.
def localCycle00430 : Cycle where
  length := 8
  data := {
    node := ![.theta 0, .zero, .theta 6, .distance 1 6, .distance 1 5, .distance 1 4, .distance 1 3, .theta 1, .theta 0]
    constant := ![0, 0, 2, 0, -2, -2, -1, 0]
    coefficient := ![0, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, true] }
  origin := ![.thetaLower 0, .thetaUpper 6, .gapUpper 6 0, .triangle 24 1, .gapLower 1 3, .gapLower 1 2, .corridorLower 1 3, .thetaNext 0]

-- Cycle fingerprint fe168f48d48af381052638b248b8be63bcf7b607be1b265a7edafc808bfd6f1b.
def localCycle00431 : Cycle where
  length := 5
  data := {
    node := ![.distance 1 5, .distance 1 3, .theta 1, .distance 0 1, .distance 1 6, .distance 1 5]
    constant := ![-2, -1, 3, -2, 0]
    coefficient := ![0, 0, 1, 0, 0]
    strict := ![false, false, false, false, true] }
  origin := ![.gapLower 1 2, .corridorLower 1 3, .corridorUpper 0 1, .gapLower 1 5, .triangle 24 1]

-- Cycle fingerprint feea04c486af2863b58b98ba7ffdf34a005a97b470d586b355d3c8331e84e320.
def localCycle00432 : Cycle where
  length := 7
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 4, .distance 4 6, .distance 4 5, .distance 1 4, .distance 1 3, .theta 1]
    constant := ![2, 0, -1, 0, -1, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, false] }
  origin := ![.gapLower 1 6, .triangle 2 2, .triangle 13 0, .triangle 34 1, .triangle 22 0, .gapLower 1 2, .corridorLower 1 3]

-- Cycle fingerprint ffb5eb88193491be15947ecfdb88ea54140cf1b6065059f292a54727fac30406.
def localCycle00433 : Cycle where
  length := 11
  data := {
    node := ![.distance 2 5, .distance 5 6, .distance 4 5, .distance 1 4, .distance 1 3, .theta 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 2 4, .distance 2 5]
    constant := ![-1, -1, -1, -2, -1, 0, 0, 0, 3, 0, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, false, false, true, false, false, false, true, true] }
  origin := ![.triangle 30 0, .triangle 34 0, .triangle 22 0, .gapLower 1 2, .corridorLower 1 3, .thetaNext 0, .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 28 2]

def library : Library := fun id => if id < 217 then (if id < 108 then (if id < 54 then (if id < 27 then (if id < 13 then (if id < 6 then (if id < 3 then (if id < 1 then (if id = 0 then some localCycle00000 else none) else (if id < 2 then (if id = 1 then some localCycle00001 else none) else (if id = 2 then some localCycle00002 else none))) else (if id < 4 then (if id = 3 then some localCycle00003 else none) else (if id < 5 then (if id = 4 then some localCycle00004 else none) else (if id = 5 then some localCycle00005 else none)))) else (if id < 9 then (if id < 7 then (if id = 6 then some localCycle00006 else none) else (if id < 8 then (if id = 7 then some localCycle00007 else none) else (if id = 8 then some localCycle00008 else none))) else (if id < 11 then (if id < 10 then (if id = 9 then some localCycle00009 else none) else (if id = 10 then some localCycle00010 else none)) else (if id < 12 then (if id = 11 then some localCycle00011 else none) else (if id = 12 then some localCycle00012 else none))))) else (if id < 20 then (if id < 16 then (if id < 14 then (if id = 13 then some localCycle00013 else none) else (if id < 15 then (if id = 14 then some localCycle00014 else none) else (if id = 15 then some localCycle00015 else none))) else (if id < 18 then (if id < 17 then (if id = 16 then some localCycle00016 else none) else (if id = 17 then some localCycle00017 else none)) else (if id < 19 then (if id = 18 then some localCycle00018 else none) else (if id = 19 then some localCycle00019 else none)))) else (if id < 23 then (if id < 21 then (if id = 20 then some localCycle00020 else none) else (if id < 22 then (if id = 21 then some localCycle00021 else none) else (if id = 22 then some localCycle00022 else none))) else (if id < 25 then (if id < 24 then (if id = 23 then some localCycle00023 else none) else (if id = 24 then some localCycle00024 else none)) else (if id < 26 then (if id = 25 then some localCycle00025 else none) else (if id = 26 then some localCycle00026 else none)))))) else (if id < 40 then (if id < 33 then (if id < 30 then (if id < 28 then (if id = 27 then some localCycle00027 else none) else (if id < 29 then (if id = 28 then some localCycle00028 else none) else (if id = 29 then some localCycle00029 else none))) else (if id < 31 then (if id = 30 then some localCycle00030 else none) else (if id < 32 then (if id = 31 then some localCycle00031 else none) else (if id = 32 then some localCycle00032 else none)))) else (if id < 36 then (if id < 34 then (if id = 33 then some localCycle00033 else none) else (if id < 35 then (if id = 34 then some localCycle00034 else none) else (if id = 35 then some localCycle00035 else none))) else (if id < 38 then (if id < 37 then (if id = 36 then some localCycle00036 else none) else (if id = 37 then some localCycle00037 else none)) else (if id < 39 then (if id = 38 then some localCycle00038 else none) else (if id = 39 then some localCycle00039 else none))))) else (if id < 47 then (if id < 43 then (if id < 41 then (if id = 40 then some localCycle00040 else none) else (if id < 42 then (if id = 41 then some localCycle00041 else none) else (if id = 42 then some localCycle00042 else none))) else (if id < 45 then (if id < 44 then (if id = 43 then some localCycle00043 else none) else (if id = 44 then some localCycle00044 else none)) else (if id < 46 then (if id = 45 then some localCycle00045 else none) else (if id = 46 then some localCycle00046 else none)))) else (if id < 50 then (if id < 48 then (if id = 47 then some localCycle00047 else none) else (if id < 49 then (if id = 48 then some localCycle00048 else none) else (if id = 49 then some localCycle00049 else none))) else (if id < 52 then (if id < 51 then (if id = 50 then some localCycle00050 else none) else (if id = 51 then some localCycle00051 else none)) else (if id < 53 then (if id = 52 then some localCycle00052 else none) else (if id = 53 then some localCycle00053 else none))))))) else (if id < 81 then (if id < 67 then (if id < 60 then (if id < 57 then (if id < 55 then (if id = 54 then some localCycle00054 else none) else (if id < 56 then (if id = 55 then some localCycle00055 else none) else (if id = 56 then some localCycle00056 else none))) else (if id < 58 then (if id = 57 then some localCycle00057 else none) else (if id < 59 then (if id = 58 then some localCycle00058 else none) else (if id = 59 then some localCycle00059 else none)))) else (if id < 63 then (if id < 61 then (if id = 60 then some localCycle00060 else none) else (if id < 62 then (if id = 61 then some localCycle00061 else none) else (if id = 62 then some localCycle00062 else none))) else (if id < 65 then (if id < 64 then (if id = 63 then some localCycle00063 else none) else (if id = 64 then some localCycle00064 else none)) else (if id < 66 then (if id = 65 then some localCycle00065 else none) else (if id = 66 then some localCycle00066 else none))))) else (if id < 74 then (if id < 70 then (if id < 68 then (if id = 67 then some localCycle00067 else none) else (if id < 69 then (if id = 68 then some localCycle00068 else none) else (if id = 69 then some localCycle00069 else none))) else (if id < 72 then (if id < 71 then (if id = 70 then some localCycle00070 else none) else (if id = 71 then some localCycle00071 else none)) else (if id < 73 then (if id = 72 then some localCycle00072 else none) else (if id = 73 then some localCycle00073 else none)))) else (if id < 77 then (if id < 75 then (if id = 74 then some localCycle00074 else none) else (if id < 76 then (if id = 75 then some localCycle00075 else none) else (if id = 76 then some localCycle00076 else none))) else (if id < 79 then (if id < 78 then (if id = 77 then some localCycle00077 else none) else (if id = 78 then some localCycle00078 else none)) else (if id < 80 then (if id = 79 then some localCycle00079 else none) else (if id = 80 then some localCycle00080 else none)))))) else (if id < 94 then (if id < 87 then (if id < 84 then (if id < 82 then (if id = 81 then some localCycle00081 else none) else (if id < 83 then (if id = 82 then some localCycle00082 else none) else (if id = 83 then some localCycle00083 else none))) else (if id < 85 then (if id = 84 then some localCycle00084 else none) else (if id < 86 then (if id = 85 then some localCycle00085 else none) else (if id = 86 then some localCycle00086 else none)))) else (if id < 90 then (if id < 88 then (if id = 87 then some localCycle00087 else none) else (if id < 89 then (if id = 88 then some localCycle00088 else none) else (if id = 89 then some localCycle00089 else none))) else (if id < 92 then (if id < 91 then (if id = 90 then some localCycle00090 else none) else (if id = 91 then some localCycle00091 else none)) else (if id < 93 then (if id = 92 then some localCycle00092 else none) else (if id = 93 then some localCycle00093 else none))))) else (if id < 101 then (if id < 97 then (if id < 95 then (if id = 94 then some localCycle00094 else none) else (if id < 96 then (if id = 95 then some localCycle00095 else none) else (if id = 96 then some localCycle00096 else none))) else (if id < 99 then (if id < 98 then (if id = 97 then some localCycle00097 else none) else (if id = 98 then some localCycle00098 else none)) else (if id < 100 then (if id = 99 then some localCycle00099 else none) else (if id = 100 then some localCycle00100 else none)))) else (if id < 104 then (if id < 102 then (if id = 101 then some localCycle00101 else none) else (if id < 103 then (if id = 102 then some localCycle00102 else none) else (if id = 103 then some localCycle00103 else none))) else (if id < 106 then (if id < 105 then (if id = 104 then some localCycle00104 else none) else (if id = 105 then some localCycle00105 else none)) else (if id < 107 then (if id = 106 then some localCycle00106 else none) else (if id = 107 then some localCycle00107 else none)))))))) else (if id < 162 then (if id < 135 then (if id < 121 then (if id < 114 then (if id < 111 then (if id < 109 then (if id = 108 then some localCycle00108 else none) else (if id < 110 then (if id = 109 then some localCycle00109 else none) else (if id = 110 then some localCycle00110 else none))) else (if id < 112 then (if id = 111 then some localCycle00111 else none) else (if id < 113 then (if id = 112 then some localCycle00112 else none) else (if id = 113 then some localCycle00113 else none)))) else (if id < 117 then (if id < 115 then (if id = 114 then some localCycle00114 else none) else (if id < 116 then (if id = 115 then some localCycle00115 else none) else (if id = 116 then some localCycle00116 else none))) else (if id < 119 then (if id < 118 then (if id = 117 then some localCycle00117 else none) else (if id = 118 then some localCycle00118 else none)) else (if id < 120 then (if id = 119 then some localCycle00119 else none) else (if id = 120 then some localCycle00120 else none))))) else (if id < 128 then (if id < 124 then (if id < 122 then (if id = 121 then some localCycle00121 else none) else (if id < 123 then (if id = 122 then some localCycle00122 else none) else (if id = 123 then some localCycle00123 else none))) else (if id < 126 then (if id < 125 then (if id = 124 then some localCycle00124 else none) else (if id = 125 then some localCycle00125 else none)) else (if id < 127 then (if id = 126 then some localCycle00126 else none) else (if id = 127 then some localCycle00127 else none)))) else (if id < 131 then (if id < 129 then (if id = 128 then some localCycle00128 else none) else (if id < 130 then (if id = 129 then some localCycle00129 else none) else (if id = 130 then some localCycle00130 else none))) else (if id < 133 then (if id < 132 then (if id = 131 then some localCycle00131 else none) else (if id = 132 then some localCycle00132 else none)) else (if id < 134 then (if id = 133 then some localCycle00133 else none) else (if id = 134 then some localCycle00134 else none)))))) else (if id < 148 then (if id < 141 then (if id < 138 then (if id < 136 then (if id = 135 then some localCycle00135 else none) else (if id < 137 then (if id = 136 then some localCycle00136 else none) else (if id = 137 then some localCycle00137 else none))) else (if id < 139 then (if id = 138 then some localCycle00138 else none) else (if id < 140 then (if id = 139 then some localCycle00139 else none) else (if id = 140 then some localCycle00140 else none)))) else (if id < 144 then (if id < 142 then (if id = 141 then some localCycle00141 else none) else (if id < 143 then (if id = 142 then some localCycle00142 else none) else (if id = 143 then some localCycle00143 else none))) else (if id < 146 then (if id < 145 then (if id = 144 then some localCycle00144 else none) else (if id = 145 then some localCycle00145 else none)) else (if id < 147 then (if id = 146 then some localCycle00146 else none) else (if id = 147 then some localCycle00147 else none))))) else (if id < 155 then (if id < 151 then (if id < 149 then (if id = 148 then some localCycle00148 else none) else (if id < 150 then (if id = 149 then some localCycle00149 else none) else (if id = 150 then some localCycle00150 else none))) else (if id < 153 then (if id < 152 then (if id = 151 then some localCycle00151 else none) else (if id = 152 then some localCycle00152 else none)) else (if id < 154 then (if id = 153 then some localCycle00153 else none) else (if id = 154 then some localCycle00154 else none)))) else (if id < 158 then (if id < 156 then (if id = 155 then some localCycle00155 else none) else (if id < 157 then (if id = 156 then some localCycle00156 else none) else (if id = 157 then some localCycle00157 else none))) else (if id < 160 then (if id < 159 then (if id = 158 then some localCycle00158 else none) else (if id = 159 then some localCycle00159 else none)) else (if id < 161 then (if id = 160 then some localCycle00160 else none) else (if id = 161 then some localCycle00161 else none))))))) else (if id < 189 then (if id < 175 then (if id < 168 then (if id < 165 then (if id < 163 then (if id = 162 then some localCycle00162 else none) else (if id < 164 then (if id = 163 then some localCycle00163 else none) else (if id = 164 then some localCycle00164 else none))) else (if id < 166 then (if id = 165 then some localCycle00165 else none) else (if id < 167 then (if id = 166 then some localCycle00166 else none) else (if id = 167 then some localCycle00167 else none)))) else (if id < 171 then (if id < 169 then (if id = 168 then some localCycle00168 else none) else (if id < 170 then (if id = 169 then some localCycle00169 else none) else (if id = 170 then some localCycle00170 else none))) else (if id < 173 then (if id < 172 then (if id = 171 then some localCycle00171 else none) else (if id = 172 then some localCycle00172 else none)) else (if id < 174 then (if id = 173 then some localCycle00173 else none) else (if id = 174 then some localCycle00174 else none))))) else (if id < 182 then (if id < 178 then (if id < 176 then (if id = 175 then some localCycle00175 else none) else (if id < 177 then (if id = 176 then some localCycle00176 else none) else (if id = 177 then some localCycle00177 else none))) else (if id < 180 then (if id < 179 then (if id = 178 then some localCycle00178 else none) else (if id = 179 then some localCycle00179 else none)) else (if id < 181 then (if id = 180 then some localCycle00180 else none) else (if id = 181 then some localCycle00181 else none)))) else (if id < 185 then (if id < 183 then (if id = 182 then some localCycle00182 else none) else (if id < 184 then (if id = 183 then some localCycle00183 else none) else (if id = 184 then some localCycle00184 else none))) else (if id < 187 then (if id < 186 then (if id = 185 then some localCycle00185 else none) else (if id = 186 then some localCycle00186 else none)) else (if id < 188 then (if id = 187 then some localCycle00187 else none) else (if id = 188 then some localCycle00188 else none)))))) else (if id < 203 then (if id < 196 then (if id < 192 then (if id < 190 then (if id = 189 then some localCycle00189 else none) else (if id < 191 then (if id = 190 then some localCycle00190 else none) else (if id = 191 then some localCycle00191 else none))) else (if id < 194 then (if id < 193 then (if id = 192 then some localCycle00192 else none) else (if id = 193 then some localCycle00193 else none)) else (if id < 195 then (if id = 194 then some localCycle00194 else none) else (if id = 195 then some localCycle00195 else none)))) else (if id < 199 then (if id < 197 then (if id = 196 then some localCycle00196 else none) else (if id < 198 then (if id = 197 then some localCycle00197 else none) else (if id = 198 then some localCycle00198 else none))) else (if id < 201 then (if id < 200 then (if id = 199 then some localCycle00199 else none) else (if id = 200 then some localCycle00200 else none)) else (if id < 202 then (if id = 201 then some localCycle00201 else none) else (if id = 202 then some localCycle00202 else none))))) else (if id < 210 then (if id < 206 then (if id < 204 then (if id = 203 then some localCycle00203 else none) else (if id < 205 then (if id = 204 then some localCycle00204 else none) else (if id = 205 then some localCycle00205 else none))) else (if id < 208 then (if id < 207 then (if id = 206 then some localCycle00206 else none) else (if id = 207 then some localCycle00207 else none)) else (if id < 209 then (if id = 208 then some localCycle00208 else none) else (if id = 209 then some localCycle00209 else none)))) else (if id < 213 then (if id < 211 then (if id = 210 then some localCycle00210 else none) else (if id < 212 then (if id = 211 then some localCycle00211 else none) else (if id = 212 then some localCycle00212 else none))) else (if id < 215 then (if id < 214 then (if id = 213 then some localCycle00213 else none) else (if id = 214 then some localCycle00214 else none)) else (if id < 216 then (if id = 215 then some localCycle00215 else none) else (if id = 216 then some localCycle00216 else none))))))))) else (if id < 325 then (if id < 271 then (if id < 244 then (if id < 230 then (if id < 223 then (if id < 220 then (if id < 218 then (if id = 217 then some localCycle00217 else none) else (if id < 219 then (if id = 218 then some localCycle00218 else none) else (if id = 219 then some localCycle00219 else none))) else (if id < 221 then (if id = 220 then some localCycle00220 else none) else (if id < 222 then (if id = 221 then some localCycle00221 else none) else (if id = 222 then some localCycle00222 else none)))) else (if id < 226 then (if id < 224 then (if id = 223 then some localCycle00223 else none) else (if id < 225 then (if id = 224 then some localCycle00224 else none) else (if id = 225 then some localCycle00225 else none))) else (if id < 228 then (if id < 227 then (if id = 226 then some localCycle00226 else none) else (if id = 227 then some localCycle00227 else none)) else (if id < 229 then (if id = 228 then some localCycle00228 else none) else (if id = 229 then some localCycle00229 else none))))) else (if id < 237 then (if id < 233 then (if id < 231 then (if id = 230 then some localCycle00230 else none) else (if id < 232 then (if id = 231 then some localCycle00231 else none) else (if id = 232 then some localCycle00232 else none))) else (if id < 235 then (if id < 234 then (if id = 233 then some localCycle00233 else none) else (if id = 234 then some localCycle00234 else none)) else (if id < 236 then (if id = 235 then some localCycle00235 else none) else (if id = 236 then some localCycle00236 else none)))) else (if id < 240 then (if id < 238 then (if id = 237 then some localCycle00237 else none) else (if id < 239 then (if id = 238 then some localCycle00238 else none) else (if id = 239 then some localCycle00239 else none))) else (if id < 242 then (if id < 241 then (if id = 240 then some localCycle00240 else none) else (if id = 241 then some localCycle00241 else none)) else (if id < 243 then (if id = 242 then some localCycle00242 else none) else (if id = 243 then some localCycle00243 else none)))))) else (if id < 257 then (if id < 250 then (if id < 247 then (if id < 245 then (if id = 244 then some localCycle00244 else none) else (if id < 246 then (if id = 245 then some localCycle00245 else none) else (if id = 246 then some localCycle00246 else none))) else (if id < 248 then (if id = 247 then some localCycle00247 else none) else (if id < 249 then (if id = 248 then some localCycle00248 else none) else (if id = 249 then some localCycle00249 else none)))) else (if id < 253 then (if id < 251 then (if id = 250 then some localCycle00250 else none) else (if id < 252 then (if id = 251 then some localCycle00251 else none) else (if id = 252 then some localCycle00252 else none))) else (if id < 255 then (if id < 254 then (if id = 253 then some localCycle00253 else none) else (if id = 254 then some localCycle00254 else none)) else (if id < 256 then (if id = 255 then some localCycle00255 else none) else (if id = 256 then some localCycle00256 else none))))) else (if id < 264 then (if id < 260 then (if id < 258 then (if id = 257 then some localCycle00257 else none) else (if id < 259 then (if id = 258 then some localCycle00258 else none) else (if id = 259 then some localCycle00259 else none))) else (if id < 262 then (if id < 261 then (if id = 260 then some localCycle00260 else none) else (if id = 261 then some localCycle00261 else none)) else (if id < 263 then (if id = 262 then some localCycle00262 else none) else (if id = 263 then some localCycle00263 else none)))) else (if id < 267 then (if id < 265 then (if id = 264 then some localCycle00264 else none) else (if id < 266 then (if id = 265 then some localCycle00265 else none) else (if id = 266 then some localCycle00266 else none))) else (if id < 269 then (if id < 268 then (if id = 267 then some localCycle00267 else none) else (if id = 268 then some localCycle00268 else none)) else (if id < 270 then (if id = 269 then some localCycle00269 else none) else (if id = 270 then some localCycle00270 else none))))))) else (if id < 298 then (if id < 284 then (if id < 277 then (if id < 274 then (if id < 272 then (if id = 271 then some localCycle00271 else none) else (if id < 273 then (if id = 272 then some localCycle00272 else none) else (if id = 273 then some localCycle00273 else none))) else (if id < 275 then (if id = 274 then some localCycle00274 else none) else (if id < 276 then (if id = 275 then some localCycle00275 else none) else (if id = 276 then some localCycle00276 else none)))) else (if id < 280 then (if id < 278 then (if id = 277 then some localCycle00277 else none) else (if id < 279 then (if id = 278 then some localCycle00278 else none) else (if id = 279 then some localCycle00279 else none))) else (if id < 282 then (if id < 281 then (if id = 280 then some localCycle00280 else none) else (if id = 281 then some localCycle00281 else none)) else (if id < 283 then (if id = 282 then some localCycle00282 else none) else (if id = 283 then some localCycle00283 else none))))) else (if id < 291 then (if id < 287 then (if id < 285 then (if id = 284 then some localCycle00284 else none) else (if id < 286 then (if id = 285 then some localCycle00285 else none) else (if id = 286 then some localCycle00286 else none))) else (if id < 289 then (if id < 288 then (if id = 287 then some localCycle00287 else none) else (if id = 288 then some localCycle00288 else none)) else (if id < 290 then (if id = 289 then some localCycle00289 else none) else (if id = 290 then some localCycle00290 else none)))) else (if id < 294 then (if id < 292 then (if id = 291 then some localCycle00291 else none) else (if id < 293 then (if id = 292 then some localCycle00292 else none) else (if id = 293 then some localCycle00293 else none))) else (if id < 296 then (if id < 295 then (if id = 294 then some localCycle00294 else none) else (if id = 295 then some localCycle00295 else none)) else (if id < 297 then (if id = 296 then some localCycle00296 else none) else (if id = 297 then some localCycle00297 else none)))))) else (if id < 311 then (if id < 304 then (if id < 301 then (if id < 299 then (if id = 298 then some localCycle00298 else none) else (if id < 300 then (if id = 299 then some localCycle00299 else none) else (if id = 300 then some localCycle00300 else none))) else (if id < 302 then (if id = 301 then some localCycle00301 else none) else (if id < 303 then (if id = 302 then some localCycle00302 else none) else (if id = 303 then some localCycle00303 else none)))) else (if id < 307 then (if id < 305 then (if id = 304 then some localCycle00304 else none) else (if id < 306 then (if id = 305 then some localCycle00305 else none) else (if id = 306 then some localCycle00306 else none))) else (if id < 309 then (if id < 308 then (if id = 307 then some localCycle00307 else none) else (if id = 308 then some localCycle00308 else none)) else (if id < 310 then (if id = 309 then some localCycle00309 else none) else (if id = 310 then some localCycle00310 else none))))) else (if id < 318 then (if id < 314 then (if id < 312 then (if id = 311 then some localCycle00311 else none) else (if id < 313 then (if id = 312 then some localCycle00312 else none) else (if id = 313 then some localCycle00313 else none))) else (if id < 316 then (if id < 315 then (if id = 314 then some localCycle00314 else none) else (if id = 315 then some localCycle00315 else none)) else (if id < 317 then (if id = 316 then some localCycle00316 else none) else (if id = 317 then some localCycle00317 else none)))) else (if id < 321 then (if id < 319 then (if id = 318 then some localCycle00318 else none) else (if id < 320 then (if id = 319 then some localCycle00319 else none) else (if id = 320 then some localCycle00320 else none))) else (if id < 323 then (if id < 322 then (if id = 321 then some localCycle00321 else none) else (if id = 322 then some localCycle00322 else none)) else (if id < 324 then (if id = 323 then some localCycle00323 else none) else (if id = 324 then some localCycle00324 else none)))))))) else (if id < 379 then (if id < 352 then (if id < 338 then (if id < 331 then (if id < 328 then (if id < 326 then (if id = 325 then some localCycle00325 else none) else (if id < 327 then (if id = 326 then some localCycle00326 else none) else (if id = 327 then some localCycle00327 else none))) else (if id < 329 then (if id = 328 then some localCycle00328 else none) else (if id < 330 then (if id = 329 then some localCycle00329 else none) else (if id = 330 then some localCycle00330 else none)))) else (if id < 334 then (if id < 332 then (if id = 331 then some localCycle00331 else none) else (if id < 333 then (if id = 332 then some localCycle00332 else none) else (if id = 333 then some localCycle00333 else none))) else (if id < 336 then (if id < 335 then (if id = 334 then some localCycle00334 else none) else (if id = 335 then some localCycle00335 else none)) else (if id < 337 then (if id = 336 then some localCycle00336 else none) else (if id = 337 then some localCycle00337 else none))))) else (if id < 345 then (if id < 341 then (if id < 339 then (if id = 338 then some localCycle00338 else none) else (if id < 340 then (if id = 339 then some localCycle00339 else none) else (if id = 340 then some localCycle00340 else none))) else (if id < 343 then (if id < 342 then (if id = 341 then some localCycle00341 else none) else (if id = 342 then some localCycle00342 else none)) else (if id < 344 then (if id = 343 then some localCycle00343 else none) else (if id = 344 then some localCycle00344 else none)))) else (if id < 348 then (if id < 346 then (if id = 345 then some localCycle00345 else none) else (if id < 347 then (if id = 346 then some localCycle00346 else none) else (if id = 347 then some localCycle00347 else none))) else (if id < 350 then (if id < 349 then (if id = 348 then some localCycle00348 else none) else (if id = 349 then some localCycle00349 else none)) else (if id < 351 then (if id = 350 then some localCycle00350 else none) else (if id = 351 then some localCycle00351 else none)))))) else (if id < 365 then (if id < 358 then (if id < 355 then (if id < 353 then (if id = 352 then some localCycle00352 else none) else (if id < 354 then (if id = 353 then some localCycle00353 else none) else (if id = 354 then some localCycle00354 else none))) else (if id < 356 then (if id = 355 then some localCycle00355 else none) else (if id < 357 then (if id = 356 then some localCycle00356 else none) else (if id = 357 then some localCycle00357 else none)))) else (if id < 361 then (if id < 359 then (if id = 358 then some localCycle00358 else none) else (if id < 360 then (if id = 359 then some localCycle00359 else none) else (if id = 360 then some localCycle00360 else none))) else (if id < 363 then (if id < 362 then (if id = 361 then some localCycle00361 else none) else (if id = 362 then some localCycle00362 else none)) else (if id < 364 then (if id = 363 then some localCycle00363 else none) else (if id = 364 then some localCycle00364 else none))))) else (if id < 372 then (if id < 368 then (if id < 366 then (if id = 365 then some localCycle00365 else none) else (if id < 367 then (if id = 366 then some localCycle00366 else none) else (if id = 367 then some localCycle00367 else none))) else (if id < 370 then (if id < 369 then (if id = 368 then some localCycle00368 else none) else (if id = 369 then some localCycle00369 else none)) else (if id < 371 then (if id = 370 then some localCycle00370 else none) else (if id = 371 then some localCycle00371 else none)))) else (if id < 375 then (if id < 373 then (if id = 372 then some localCycle00372 else none) else (if id < 374 then (if id = 373 then some localCycle00373 else none) else (if id = 374 then some localCycle00374 else none))) else (if id < 377 then (if id < 376 then (if id = 375 then some localCycle00375 else none) else (if id = 376 then some localCycle00376 else none)) else (if id < 378 then (if id = 377 then some localCycle00377 else none) else (if id = 378 then some localCycle00378 else none))))))) else (if id < 406 then (if id < 392 then (if id < 385 then (if id < 382 then (if id < 380 then (if id = 379 then some localCycle00379 else none) else (if id < 381 then (if id = 380 then some localCycle00380 else none) else (if id = 381 then some localCycle00381 else none))) else (if id < 383 then (if id = 382 then some localCycle00382 else none) else (if id < 384 then (if id = 383 then some localCycle00383 else none) else (if id = 384 then some localCycle00384 else none)))) else (if id < 388 then (if id < 386 then (if id = 385 then some localCycle00385 else none) else (if id < 387 then (if id = 386 then some localCycle00386 else none) else (if id = 387 then some localCycle00387 else none))) else (if id < 390 then (if id < 389 then (if id = 388 then some localCycle00388 else none) else (if id = 389 then some localCycle00389 else none)) else (if id < 391 then (if id = 390 then some localCycle00390 else none) else (if id = 391 then some localCycle00391 else none))))) else (if id < 399 then (if id < 395 then (if id < 393 then (if id = 392 then some localCycle00392 else none) else (if id < 394 then (if id = 393 then some localCycle00393 else none) else (if id = 394 then some localCycle00394 else none))) else (if id < 397 then (if id < 396 then (if id = 395 then some localCycle00395 else none) else (if id = 396 then some localCycle00396 else none)) else (if id < 398 then (if id = 397 then some localCycle00397 else none) else (if id = 398 then some localCycle00398 else none)))) else (if id < 402 then (if id < 400 then (if id = 399 then some localCycle00399 else none) else (if id < 401 then (if id = 400 then some localCycle00400 else none) else (if id = 401 then some localCycle00401 else none))) else (if id < 404 then (if id < 403 then (if id = 402 then some localCycle00402 else none) else (if id = 403 then some localCycle00403 else none)) else (if id < 405 then (if id = 404 then some localCycle00404 else none) else (if id = 405 then some localCycle00405 else none)))))) else (if id < 420 then (if id < 413 then (if id < 409 then (if id < 407 then (if id = 406 then some localCycle00406 else none) else (if id < 408 then (if id = 407 then some localCycle00407 else none) else (if id = 408 then some localCycle00408 else none))) else (if id < 411 then (if id < 410 then (if id = 409 then some localCycle00409 else none) else (if id = 410 then some localCycle00410 else none)) else (if id < 412 then (if id = 411 then some localCycle00411 else none) else (if id = 412 then some localCycle00412 else none)))) else (if id < 416 then (if id < 414 then (if id = 413 then some localCycle00413 else none) else (if id < 415 then (if id = 414 then some localCycle00414 else none) else (if id = 415 then some localCycle00415 else none))) else (if id < 418 then (if id < 417 then (if id = 416 then some localCycle00416 else none) else (if id = 417 then some localCycle00417 else none)) else (if id < 419 then (if id = 418 then some localCycle00418 else none) else (if id = 419 then some localCycle00419 else none))))) else (if id < 427 then (if id < 423 then (if id < 421 then (if id = 420 then some localCycle00420 else none) else (if id < 422 then (if id = 421 then some localCycle00421 else none) else (if id = 422 then some localCycle00422 else none))) else (if id < 425 then (if id < 424 then (if id = 423 then some localCycle00423 else none) else (if id = 424 then some localCycle00424 else none)) else (if id < 426 then (if id = 425 then some localCycle00425 else none) else (if id = 426 then some localCycle00426 else none)))) else (if id < 430 then (if id < 428 then (if id = 427 then some localCycle00427 else none) else (if id < 429 then (if id = 428 then some localCycle00428 else none) else (if id = 429 then some localCycle00429 else none))) else (if id < 432 then (if id < 431 then (if id = 430 then some localCycle00430 else none) else (if id = 431 then some localCycle00431 else none)) else (if id < 433 then (if id = 432 then some localCycle00432 else none) else (if id = 433 then some localCycle00433 else none)))))))))

def namedLeaf000 : LeafData := { rows := ![![5, 4, 3, 2, 1, 6], ![5, 4, 3, 2, 0, 6], ![3, 5, 4, 1, 0, 6], ![2, 5, 4, 1, 0, 6], ![5, 2, 3, 1, 0, 6], ![4, 2, 3, 1, 0, 6], ![0, 1, 2, 3, 4, 5]], proof := .tail 347 }

theorem namedLeaf000_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 17792)) namedLeaf000 = true :=
  by decide +kernel

def namedLeaf001 : LeafData := { rows := ![![5, 4, 3, 2, 1, 6], ![5, 4, 3, 2, 0, 6], ![5, 3, 4, 1, 0, 6], ![5, 2, 4, 1, 0, 6], ![5, 2, 3, 1, 0, 6], ![4, 3, 2, 1, 0, 6], ![0, 1, 2, 3, 4, 5]], proof := .tail 134 }

theorem namedLeaf001_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 17793)) namedLeaf001 = true :=
  by decide +kernel

def namedLeaf002 : LeafData := { rows := ![![4, 3, 5, 2, 1, 6], ![4, 3, 5, 2, 0, 6], ![4, 3, 5, 1, 0, 6], ![4, 2, 1, 0, 5, 6], ![3, 2, 1, 0, 5, 6], ![2, 1, 0, 3, 4, 6], ![0, 1, 2, 3, 4, 5]], proof := .tail 56 }

theorem namedLeaf002_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 17794)) namedLeaf002 = true :=
  by decide +kernel

def namedLeaf003 : LeafData := { rows := ![![4, 3, 5, 2, 1, 6], ![4, 3, 5, 2, 0, 6], ![4, 3, 5, 1, 0, 6], ![4, 2, 1, 0, 5, 6], ![3, 2, 1, 0, 6, 5], ![2, 1, 0, 3, 6, 4], ![0, 1, 2, 3, 5, 4]], proof := .tail 26 }

theorem namedLeaf003_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 17795)) namedLeaf003 = true :=
  by decide +kernel

def namedLeaf004 : LeafData := { rows := ![![4, 3, 5, 2, 1, 6], ![4, 3, 5, 2, 0, 6], ![4, 3, 5, 1, 0, 6], ![4, 2, 1, 0, 6, 5], ![3, 2, 1, 0, 6, 5], ![2, 1, 0, 6, 3, 4], ![0, 1, 2, 5, 3, 4]], proof := .tail 113 }

theorem namedLeaf004_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 17796)) namedLeaf004 = true :=
  by decide +kernel

def namedLeaf005 : LeafData := { rows := ![![4, 5, 3, 2, 1, 6], ![4, 3, 5, 2, 0, 6], ![4, 3, 5, 1, 0, 6], ![4, 2, 1, 5, 0, 6], ![3, 2, 1, 0, 5, 6], ![2, 1, 3, 0, 4, 6], ![0, 1, 2, 3, 4, 5]], proof := .tail 160 }

theorem namedLeaf005_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 17797)) namedLeaf005 = true :=
  by decide +kernel

def namedLeaf006 : LeafData := { rows := ![![4, 5, 3, 2, 1, 6], ![4, 3, 5, 2, 0, 6], ![4, 3, 5, 1, 0, 6], ![4, 2, 1, 5, 0, 6], ![3, 2, 1, 0, 6, 5], ![2, 1, 3, 0, 6, 4], ![0, 1, 2, 3, 5, 4]], proof := .tail 379 }

theorem namedLeaf006_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 17798)) namedLeaf006 = true :=
  by decide +kernel

def namedLeaf007 : LeafData := { rows := ![![5, 4, 3, 2, 1, 6], ![4, 3, 5, 2, 0, 6], ![4, 3, 5, 1, 0, 6], ![4, 2, 1, 5, 0, 6], ![3, 2, 1, 5, 0, 6], ![2, 1, 3, 4, 0, 6], ![0, 1, 2, 3, 4, 5]], proof := .tail 72 }

theorem namedLeaf007_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 17799)) namedLeaf007 = true :=
  by decide +kernel

def namedLeaf008 : LeafData := { rows := ![![4, 5, 3, 2, 1, 6], ![4, 5, 3, 2, 0, 6], ![4, 3, 5, 1, 0, 6], ![4, 2, 5, 1, 0, 6], ![3, 2, 1, 0, 5, 6], ![2, 3, 1, 0, 4, 6], ![0, 1, 2, 3, 4, 5]], proof := .tail 212 }

theorem namedLeaf008_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 17800)) namedLeaf008 = true :=
  by decide +kernel

def namedLeaf009 : LeafData := { rows := ![![4, 5, 3, 2, 1, 6], ![4, 5, 3, 2, 0, 6], ![4, 3, 5, 1, 0, 6], ![4, 2, 5, 1, 0, 6], ![3, 2, 1, 0, 6, 5], ![2, 3, 1, 0, 6, 4], ![0, 1, 2, 3, 5, 4]], proof := .tail 104 }

theorem namedLeaf009_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 17801)) namedLeaf009 = true :=
  by decide +kernel

def namedLeaf010 : LeafData := { rows := ![![5, 4, 3, 2, 1, 6], ![4, 5, 3, 2, 0, 6], ![4, 3, 5, 1, 0, 6], ![4, 2, 5, 1, 0, 6], ![3, 2, 1, 5, 0, 6], ![2, 3, 1, 4, 0, 6], ![0, 1, 2, 3, 4, 5]], proof := .tail 212 }

theorem namedLeaf010_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 17802)) namedLeaf010 = true :=
  by decide +kernel

def namedLeaf011 : LeafData := { rows := ![![5, 4, 3, 2, 1, 6], ![5, 4, 3, 2, 0, 6], ![4, 3, 5, 1, 0, 6], ![4, 2, 5, 1, 0, 6], ![3, 2, 5, 1, 0, 6], ![2, 3, 4, 1, 0, 6], ![0, 1, 2, 3, 4, 5]], proof := .tail 208 }

theorem namedLeaf011_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 17803)) namedLeaf011 = true :=
  by decide +kernel

def namedLeaf012 : LeafData := { rows := ![![4, 5, 3, 2, 1, 6], ![4, 5, 3, 2, 0, 6], ![4, 5, 3, 1, 0, 6], ![4, 5, 2, 1, 0, 6], ![3, 2, 1, 0, 5, 6], ![3, 2, 1, 0, 4, 6], ![0, 1, 2, 3, 4, 5]], proof := .tail 351 }

theorem namedLeaf012_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 17804)) namedLeaf012 = true :=
  by decide +kernel

def namedLeaf013 : LeafData := { rows := ![![4, 5, 3, 2, 1, 6], ![4, 5, 3, 2, 0, 6], ![4, 5, 3, 1, 0, 6], ![4, 5, 2, 1, 0, 6], ![3, 2, 1, 0, 6, 5], ![3, 2, 1, 0, 6, 4], ![0, 1, 2, 3, 5, 4]], proof := .tail 390 }

theorem namedLeaf013_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 17805)) namedLeaf013 = true :=
  by decide +kernel

def namedLeaf014 : LeafData := { rows := ![![5, 4, 3, 2, 1, 6], ![4, 5, 3, 2, 0, 6], ![4, 5, 3, 1, 0, 6], ![4, 5, 2, 1, 0, 6], ![3, 2, 1, 5, 0, 6], ![3, 2, 1, 4, 0, 6], ![0, 1, 2, 3, 4, 5]], proof := .tail 351 }

theorem namedLeaf014_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 17806)) namedLeaf014 = true :=
  by decide +kernel

def namedLeaf015 : LeafData := { rows := ![![5, 4, 3, 2, 1, 6], ![5, 4, 3, 2, 0, 6], ![4, 5, 3, 1, 0, 6], ![4, 5, 2, 1, 0, 6], ![3, 2, 5, 1, 0, 6], ![3, 2, 4, 1, 0, 6], ![0, 1, 2, 3, 4, 5]], proof := .tail 76 }

theorem namedLeaf015_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 17807)) namedLeaf015 = true :=
  by decide +kernel

def namedLeaf016 : LeafData := { rows := ![![5, 4, 3, 2, 1, 6], ![5, 4, 3, 2, 0, 6], ![5, 4, 3, 1, 0, 6], ![4, 5, 2, 1, 0, 6], ![3, 5, 2, 1, 0, 6], ![3, 4, 2, 1, 0, 6], ![0, 1, 2, 3, 4, 5]], proof := .tail 392 }

theorem namedLeaf016_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 17808)) namedLeaf016 = true :=
  by decide +kernel

def namedLeaf017 : LeafData := { rows := ![![5, 4, 3, 2, 1, 6], ![5, 4, 3, 2, 0, 6], ![5, 4, 3, 1, 0, 6], ![5, 4, 2, 1, 0, 6], ![5, 3, 2, 1, 0, 6], ![4, 3, 2, 1, 0, 6], ![0, 1, 2, 3, 4, 5]], proof := .tail 198 }

theorem namedLeaf017_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 17809)) namedLeaf017 = true :=
  by decide +kernel

def namedLeaf018 : LeafData := { rows := ![![2, 3, 4, 5, 6, 1], ![2, 3, 4, 5, 6, 0], ![1, 0, 3, 4, 5, 6], ![1, 0, 2, 4, 5, 6], ![1, 0, 2, 3, 5, 6], ![1, 0, 2, 3, 4, 6], ![1, 0, 2, 3, 4, 5]], proof := .tail 248 }

theorem namedLeaf018_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 17810)) namedLeaf018 = true :=
  by decide +kernel

def namedLeaf019 : LeafData := { rows := ![![2, 3, 4, 5, 6, 1], ![2, 3, 4, 5, 6, 0], ![1, 0, 3, 4, 5, 6], ![1, 0, 2, 4, 5, 6], ![1, 0, 2, 3, 6, 5], ![1, 0, 2, 3, 6, 4], ![1, 0, 2, 3, 5, 4]], proof := .tail 246 }

theorem namedLeaf019_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 17811)) namedLeaf019 = true :=
  by decide +kernel

def namedLeaf020 : LeafData := { rows := ![![2, 3, 4, 5, 6, 1], ![2, 3, 4, 5, 6, 0], ![1, 0, 3, 4, 5, 6], ![1, 0, 2, 4, 6, 5], ![1, 0, 2, 3, 6, 5], ![1, 0, 2, 6, 3, 4], ![1, 0, 2, 5, 3, 4]], proof := .low (![258, 202, 335, 270, 211, 416, 419, 290, 361, 313, 188, 399, 118, 236, 55, 144, 395, 420, 426, 2, 354, 24, 279, 149, 300, 43, 232, 237]) }

theorem namedLeaf020_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 17812)) namedLeaf020 = true :=
  by decide +kernel

def namedLeaf021 : LeafData := { rows := ![![2, 3, 4, 5, 6, 1], ![2, 3, 4, 5, 6, 0], ![1, 0, 3, 4, 6, 5], ![1, 0, 2, 4, 6, 5], ![1, 0, 2, 3, 6, 5], ![1, 0, 6, 2, 3, 4], ![1, 0, 5, 2, 3, 4]], proof := .low (![46, 202, 335, 270, 211, 416, 419, 290, 361, 313, 188, 315, 118, 236, 55, 144, 395, 420, 426, 2, 354, 24, 279, 149, 300, 43, 232, 424]) }

theorem namedLeaf021_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 17813)) namedLeaf021 = true :=
  by decide +kernel

def namedLeaf022 : LeafData := { rows := ![![2, 3, 4, 6, 5, 1], ![2, 3, 4, 5, 6, 0], ![1, 0, 3, 4, 6, 5], ![1, 0, 2, 4, 6, 5], ![1, 0, 2, 3, 6, 5], ![1, 6, 0, 2, 3, 4], ![1, 5, 0, 2, 3, 4]], proof := .low (![272, 373, 413, 249, 130, 416, 81, 59, 52, 287, 330, 315, 387, 223, 389, 170, 275, 247, 266, 358, 297, 166, 398, 66, 172, 43, 23, 359]) }

theorem namedLeaf022_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 17814)) namedLeaf022 = true :=
  by decide +kernel

def namedLeaf023 : LeafData := { rows := ![![2, 3, 4, 6, 5, 1], ![2, 3, 4, 6, 5, 0], ![1, 0, 3, 4, 6, 5], ![1, 0, 2, 4, 6, 5], ![1, 0, 2, 3, 6, 5], ![6, 1, 0, 2, 3, 4], ![5, 1, 0, 2, 3, 4]], proof := .low (![46, 281, 57, 155, 175, 61, 403, 40, 318, 230, 89, 213, 129, 239, 411, 195, 228, 93, 337, 140, 136, 404, 360, 16, 364, 427, 303, 109]) }

theorem namedLeaf023_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 17815)) namedLeaf023 = true :=
  by decide +kernel

def namedLeaf024 : LeafData := { rows := ![![2, 3, 4, 5, 6, 1], ![2, 3, 4, 5, 6, 0], ![1, 0, 3, 4, 5, 6], ![1, 0, 2, 6, 4, 5], ![1, 0, 2, 6, 3, 5], ![1, 0, 2, 6, 3, 4], ![1, 0, 2, 5, 4, 3]], proof := .tail 278 }

theorem namedLeaf024_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 17816)) namedLeaf024 = true :=
  by decide +kernel

def namedLeaf025 : LeafData := { rows := ![![2, 3, 4, 5, 6, 1], ![2, 3, 4, 5, 6, 0], ![1, 0, 3, 4, 6, 5], ![1, 0, 2, 6, 4, 5], ![1, 0, 2, 6, 3, 5], ![1, 0, 6, 2, 3, 4], ![1, 0, 5, 2, 4, 3]], proof := .tail 250 }

theorem namedLeaf025_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 17817)) namedLeaf025 = true :=
  by decide +kernel

def namedLeaf026 : LeafData := { rows := ![![2, 3, 4, 6, 5, 1], ![2, 3, 4, 5, 6, 0], ![1, 0, 3, 4, 6, 5], ![1, 0, 2, 6, 4, 5], ![1, 0, 2, 6, 3, 5], ![1, 6, 0, 2, 3, 4], ![1, 5, 0, 2, 4, 3]], proof := .tail 250 }

theorem namedLeaf026_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 17818)) namedLeaf026 = true :=
  by decide +kernel

def namedLeaf027 : LeafData := { rows := ![![2, 3, 4, 6, 5, 1], ![2, 3, 4, 6, 5, 0], ![1, 0, 3, 4, 6, 5], ![1, 0, 2, 6, 4, 5], ![1, 0, 2, 6, 3, 5], ![6, 1, 0, 2, 3, 4], ![5, 1, 0, 2, 4, 3]], proof := .tail 250 }

theorem namedLeaf027_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 17819)) namedLeaf027 = true :=
  by decide +kernel

def namedLeaf028 : LeafData := { rows := ![![2, 3, 4, 5, 6, 1], ![2, 3, 4, 5, 6, 0], ![1, 0, 3, 6, 4, 5], ![1, 0, 2, 6, 4, 5], ![1, 0, 6, 2, 3, 5], ![1, 0, 6, 2, 3, 4], ![1, 0, 5, 4, 2, 3]], proof := .tail 225 }

theorem namedLeaf028_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 17820)) namedLeaf028 = true :=
  by decide +kernel

def namedLeaf029 : LeafData := { rows := ![![2, 3, 4, 6, 5, 1], ![2, 3, 4, 5, 6, 0], ![1, 0, 3, 6, 4, 5], ![1, 0, 2, 6, 4, 5], ![1, 0, 6, 2, 3, 5], ![1, 6, 0, 2, 3, 4], ![1, 5, 0, 4, 2, 3]], proof := .tail 225 }

theorem namedLeaf029_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 17821)) namedLeaf029 = true :=
  by decide +kernel

def namedLeaf030 : LeafData := { rows := ![![2, 3, 4, 6, 5, 1], ![2, 3, 4, 6, 5, 0], ![1, 0, 3, 6, 4, 5], ![1, 0, 2, 6, 4, 5], ![1, 0, 6, 2, 3, 5], ![6, 1, 0, 2, 3, 4], ![5, 1, 0, 4, 2, 3]], proof := .tail 225 }

theorem namedLeaf030_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 17822)) namedLeaf030 = true :=
  by decide +kernel

def namedLeaf031 : LeafData := { rows := ![![2, 3, 6, 4, 5, 1], ![2, 3, 4, 5, 6, 0], ![1, 0, 3, 6, 4, 5], ![1, 0, 2, 6, 4, 5], ![1, 6, 0, 2, 3, 5], ![1, 6, 0, 2, 3, 4], ![1, 5, 4, 0, 2, 3]], proof := .tail 225 }

theorem namedLeaf031_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 17823)) namedLeaf031 = true :=
  by decide +kernel

def namedLeaf032 : LeafData := { rows := ![![2, 3, 6, 4, 5, 1], ![2, 3, 4, 6, 5, 0], ![1, 0, 3, 6, 4, 5], ![1, 0, 2, 6, 4, 5], ![1, 6, 0, 2, 3, 5], ![6, 1, 0, 2, 3, 4], ![5, 1, 4, 0, 2, 3]], proof := .tail 225 }

theorem namedLeaf032_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 17824)) namedLeaf032 = true :=
  by decide +kernel

def namedLeaf033 : LeafData := { rows := ![![2, 3, 6, 4, 5, 1], ![2, 3, 6, 4, 5, 0], ![1, 0, 3, 6, 4, 5], ![1, 0, 2, 6, 4, 5], ![6, 1, 0, 2, 3, 5], ![6, 1, 0, 2, 3, 4], ![5, 4, 1, 0, 2, 3]], proof := .tail 225 }

theorem namedLeaf033_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 17825)) namedLeaf033 = true :=
  by decide +kernel

def namedLeaf034 : LeafData := { rows := ![![2, 3, 4, 5, 6, 1], ![2, 3, 4, 5, 6, 0], ![1, 0, 3, 4, 5, 6], ![1, 0, 2, 5, 4, 6], ![1, 0, 2, 5, 3, 6], ![1, 0, 2, 4, 3, 6], ![1, 0, 2, 3, 4, 5]], proof := .tail 382 }

theorem namedLeaf034_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 17826)) namedLeaf034 = true :=
  by decide +kernel

def namedLeaf035 : LeafData := { rows := ![![2, 3, 4, 5, 6, 1], ![2, 3, 4, 5, 6, 0], ![1, 0, 3, 4, 5, 6], ![1, 0, 2, 5, 6, 4], ![1, 0, 2, 5, 6, 3], ![1, 0, 2, 4, 3, 6], ![1, 0, 2, 4, 3, 5]], proof := .low (![165, 202, 335, 294, 84, 416, 419, 290, 361, 120, 75, 289, 118, 236, 193, 95, 395, 420, 430, 127, 354, 24, 302, 149, 17, 43, 153, 237]) }

theorem namedLeaf035_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 17827)) namedLeaf035 = true :=
  by decide +kernel

def namedLeaf036 : LeafData := { rows := ![![2, 3, 4, 5, 6, 1], ![2, 3, 4, 5, 6, 0], ![1, 0, 3, 4, 5, 6], ![1, 0, 2, 6, 5, 4], ![1, 0, 2, 5, 6, 3], ![1, 0, 2, 4, 6, 3], ![1, 0, 2, 4, 5, 3]], proof := .tail 30 }

theorem namedLeaf036_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 17828)) namedLeaf036 = true :=
  by decide +kernel

def namedLeaf037 : LeafData := { rows := ![![2, 3, 4, 5, 6, 1], ![2, 3, 4, 5, 6, 0], ![1, 0, 3, 4, 5, 6], ![1, 0, 2, 6, 5, 4], ![1, 0, 2, 6, 5, 3], ![1, 0, 2, 6, 4, 3], ![1, 0, 2, 5, 4, 3]], proof := .tail 421 }

theorem namedLeaf037_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 17829)) namedLeaf037 = true :=
  by decide +kernel

def namedLeaf038 : LeafData := { rows := ![![2, 3, 4, 5, 6, 1], ![2, 3, 4, 5, 6, 0], ![1, 0, 3, 4, 6, 5], ![1, 0, 2, 6, 5, 4], ![1, 0, 2, 6, 5, 3], ![1, 0, 6, 2, 4, 3], ![1, 0, 5, 2, 4, 3]], proof := .low (![400, 285, 180, 396, 53, 416, 419, 265, 253, 322, 188, 422, 118, 159, 0, 144, 393, 420, 205, 2, 204, 39, 279, 216, 222, 43, 232, 237]) }

theorem namedLeaf038_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 17830)) namedLeaf038 = true :=
  by decide +kernel

def namedLeaf039 : LeafData := { rows := ![![2, 3, 4, 6, 5, 1], ![2, 3, 4, 5, 6, 0], ![1, 0, 3, 4, 6, 5], ![1, 0, 2, 6, 5, 4], ![1, 0, 2, 6, 5, 3], ![1, 6, 0, 2, 4, 3], ![1, 5, 0, 2, 4, 3]], proof := .low (![176, 285, 180, 396, 130, 416, 187, 265, 253, 322, 311, 1, 387, 261, 222, 327, 393, 247, 222, 327, 204, 238, 402, 222, 234, 43, 90, 11]) }

theorem namedLeaf039_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 17831)) namedLeaf039 = true :=
  by decide +kernel

def namedLeaf040 : LeafData := { rows := ![![2, 3, 4, 6, 5, 1], ![2, 3, 4, 6, 5, 0], ![1, 0, 3, 4, 6, 5], ![1, 0, 2, 6, 5, 4], ![1, 0, 2, 6, 5, 3], ![6, 1, 0, 2, 4, 3], ![5, 1, 0, 2, 4, 3]], proof := .low (![196, 281, 372, 155, 175, 63, 203, 40, 318, 230, 89, 126, 131, 239, 411, 195, 228, 93, 337, 140, 136, 183, 360, 16, 364, 427, 303, 171]) }

theorem namedLeaf040_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 17832)) namedLeaf040 = true :=
  by decide +kernel

def namedLeaf041 : LeafData := { rows := ![![2, 3, 4, 5, 6, 1], ![2, 3, 4, 5, 6, 0], ![1, 0, 3, 6, 4, 5], ![1, 0, 2, 6, 5, 4], ![1, 0, 6, 2, 5, 3], ![1, 0, 6, 2, 4, 3], ![1, 0, 5, 4, 2, 3]], proof := .tail 191 }

theorem namedLeaf041_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 17833)) namedLeaf041 = true :=
  by decide +kernel

def namedLeaf042 : LeafData := { rows := ![![2, 3, 4, 6, 5, 1], ![2, 3, 4, 5, 6, 0], ![1, 0, 3, 6, 4, 5], ![1, 0, 2, 6, 5, 4], ![1, 0, 6, 2, 5, 3], ![1, 6, 0, 2, 4, 3], ![1, 5, 0, 4, 2, 3]], proof := .tail 428 }

theorem namedLeaf042_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 17834)) namedLeaf042 = true :=
  by decide +kernel

def namedLeaf043 : LeafData := { rows := ![![2, 3, 4, 6, 5, 1], ![2, 3, 4, 6, 5, 0], ![1, 0, 3, 6, 4, 5], ![1, 0, 2, 6, 5, 4], ![1, 0, 6, 2, 5, 3], ![6, 1, 0, 2, 4, 3], ![5, 1, 0, 4, 2, 3]], proof := .tail 310 }

theorem namedLeaf043_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 17835)) namedLeaf043 = true :=
  by decide +kernel

def namedLeaf044 : LeafData := { rows := ![![2, 3, 6, 4, 5, 1], ![2, 3, 4, 5, 6, 0], ![1, 0, 3, 6, 4, 5], ![1, 0, 2, 6, 5, 4], ![1, 6, 0, 2, 5, 3], ![1, 6, 0, 2, 4, 3], ![1, 5, 4, 0, 2, 3]], proof := .tail 146 }

theorem namedLeaf044_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 17836)) namedLeaf044 = true :=
  by decide +kernel

def namedLeaf045 : LeafData := { rows := ![![2, 3, 6, 4, 5, 1], ![2, 3, 4, 6, 5, 0], ![1, 0, 3, 6, 4, 5], ![1, 0, 2, 6, 5, 4], ![1, 6, 0, 2, 5, 3], ![6, 1, 0, 2, 4, 3], ![5, 1, 4, 0, 2, 3]], proof := .tail 146 }

theorem namedLeaf045_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 17837)) namedLeaf045 = true :=
  by decide +kernel

def namedLeaf046 : LeafData := { rows := ![![2, 3, 6, 4, 5, 1], ![2, 3, 6, 4, 5, 0], ![1, 0, 3, 6, 4, 5], ![1, 0, 2, 6, 5, 4], ![6, 1, 0, 2, 5, 3], ![6, 1, 0, 2, 4, 3], ![5, 4, 1, 0, 2, 3]], proof := .tail 78 }

theorem namedLeaf046_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 17838)) namedLeaf046 = true :=
  by decide +kernel

def namedLeaf047 : LeafData := { rows := ![![2, 3, 4, 5, 6, 1], ![2, 3, 4, 5, 6, 0], ![1, 0, 3, 5, 4, 6], ![1, 0, 2, 5, 4, 6], ![1, 0, 5, 2, 3, 6], ![1, 0, 4, 2, 3, 6], ![1, 0, 2, 3, 4, 5]], proof := .low (![7, 202, 335, 294, 84, 416, 419, 290, 361, 120, 75, 185, 118, 236, 193, 95, 395, 420, 430, 127, 209, 24, 302, 149, 17, 43, 153, 237]) }

theorem namedLeaf047_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 17839)) namedLeaf047 = true :=
  by decide +kernel

def namedLeaf048 : LeafData := { rows := ![![2, 3, 4, 5, 6, 1], ![2, 3, 4, 5, 6, 0], ![1, 0, 3, 5, 4, 6], ![1, 0, 2, 5, 6, 4], ![1, 0, 5, 2, 6, 3], ![1, 0, 4, 2, 3, 6], ![1, 0, 2, 4, 3, 5]], proof := .tail 199 }

theorem namedLeaf048_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 17840)) namedLeaf048 = true :=
  by decide +kernel

def namedLeaf049 : LeafData := { rows := ![![2, 3, 4, 5, 6, 1], ![2, 3, 4, 5, 6, 0], ![1, 0, 3, 5, 4, 6], ![1, 0, 2, 6, 5, 4], ![1, 0, 5, 2, 6, 3], ![1, 0, 4, 2, 6, 3], ![1, 0, 2, 4, 5, 3]], proof := .tail 79 }

theorem namedLeaf049_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 17841)) namedLeaf049 = true :=
  by decide +kernel

def namedLeaf050 : LeafData := { rows := ![![2, 3, 4, 5, 6, 1], ![2, 3, 4, 5, 6, 0], ![1, 0, 3, 5, 6, 4], ![1, 0, 2, 5, 6, 4], ![1, 0, 5, 6, 2, 3], ![1, 0, 4, 2, 3, 6], ![1, 0, 4, 2, 3, 5]], proof := .low (![352, 338, 69, 270, 211, 416, 419, 305, 44, 313, 188, 184, 118, 236, 55, 144, 395, 420, 426, 2, 354, 24, 279, 149, 300, 43, 232, 424]) }

theorem namedLeaf050_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 17842)) namedLeaf050 = true :=
  by decide +kernel

def namedLeaf051 : LeafData := { rows := ![![2, 3, 4, 5, 6, 1], ![2, 3, 4, 5, 6, 0], ![1, 0, 3, 5, 6, 4], ![1, 0, 2, 6, 5, 4], ![1, 0, 5, 6, 2, 3], ![1, 0, 4, 2, 6, 3], ![1, 0, 4, 2, 5, 3]], proof := .low (![323, 331, 154, 326, 211, 416, 419, 405, 355, 227, 188, 116, 118, 277, 55, 144, 65, 163, 426, 2, 28, 181, 279, 149, 300, 43, 232, 237]) }

theorem namedLeaf051_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 17843)) namedLeaf051 = true :=
  by decide +kernel

def namedLeaf052 : LeafData := { rows := ![![2, 3, 4, 5, 6, 1], ![2, 3, 4, 5, 6, 0], ![1, 0, 3, 6, 5, 4], ![1, 0, 2, 6, 5, 4], ![1, 0, 5, 6, 2, 3], ![1, 0, 4, 6, 2, 3], ![1, 0, 4, 5, 2, 3]], proof := .low (![119, 312, 429, 36, 211, 35, 419, 100, 410, 274, 188, 301, 288, 147, 55, 144, 34, 304, 426, 2, 433, 133, 279, 149, 300, 43, 232, 237]) }

theorem namedLeaf052_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 17844)) namedLeaf052 = true :=
  by decide +kernel

def namedLeaf053 : LeafData := { rows := ![![2, 3, 4, 5, 6, 1], ![2, 3, 4, 5, 6, 0], ![1, 0, 3, 6, 5, 4], ![1, 0, 2, 6, 5, 4], ![1, 0, 6, 5, 2, 3], ![1, 0, 6, 4, 2, 3], ![1, 0, 5, 4, 2, 3]], proof := .low (![308, 97, 3, 164, 151, 416, 419, 215, 218, 98, 111, 269, 118, 406, 374, 144, 233, 420, 19, 2, 370, 221, 279, 21, 125, 43, 232, 237]) }

theorem namedLeaf053_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 17845)) namedLeaf053 = true :=
  by decide +kernel

def namedLeaf054 : LeafData := { rows := ![![2, 3, 4, 6, 5, 1], ![2, 3, 4, 5, 6, 0], ![1, 0, 3, 6, 5, 4], ![1, 0, 2, 6, 5, 4], ![1, 0, 6, 5, 2, 3], ![1, 6, 0, 4, 2, 3], ![1, 5, 0, 4, 2, 3]], proof := .low (![308, 97, 3, 70, 130, 35, 187, 215, 218, 98, 286, 49, 387, 259, 374, 320, 233, 247, 257, 320, 370, 238, 99, 125, 234, 43, 90, 11]) }

theorem namedLeaf054_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 17846)) namedLeaf054 = true :=
  by decide +kernel

def namedLeaf055 : LeafData := { rows := ![![2, 3, 4, 6, 5, 1], ![2, 3, 4, 6, 5, 0], ![1, 0, 3, 6, 5, 4], ![1, 0, 2, 6, 5, 4], ![1, 0, 6, 5, 2, 3], ![6, 1, 0, 4, 2, 3], ![5, 1, 0, 4, 2, 3]], proof := .low (![336, 281, 372, 77, 175, 80, 309, 40, 318, 190, 89, 62, 425, 239, 411, 195, 228, 93, 337, 140, 136, 183, 360, 16, 88, 427, 303, 122]) }

theorem namedLeaf055_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 17847)) namedLeaf055 = true :=
  by decide +kernel

def namedLeaf056 : LeafData := { rows := ![![2, 3, 6, 4, 5, 1], ![2, 3, 4, 5, 6, 0], ![1, 0, 3, 6, 5, 4], ![1, 0, 2, 6, 5, 4], ![1, 6, 0, 5, 2, 3], ![1, 6, 0, 4, 2, 3], ![1, 5, 4, 0, 2, 3]], proof := .tail 82 }

theorem namedLeaf056_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 17848)) namedLeaf056 = true :=
  by decide +kernel

def namedLeaf057 : LeafData := { rows := ![![2, 3, 6, 4, 5, 1], ![2, 3, 4, 6, 5, 0], ![1, 0, 3, 6, 5, 4], ![1, 0, 2, 6, 5, 4], ![1, 6, 0, 5, 2, 3], ![6, 1, 0, 4, 2, 3], ![5, 1, 4, 0, 2, 3]], proof := .tail 82 }

theorem namedLeaf057_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 17849)) namedLeaf057 = true :=
  by decide +kernel

def namedLeaf058 : LeafData := { rows := ![![2, 3, 6, 4, 5, 1], ![2, 3, 6, 4, 5, 0], ![1, 0, 3, 6, 5, 4], ![1, 0, 2, 6, 5, 4], ![6, 1, 0, 5, 2, 3], ![6, 1, 0, 4, 2, 3], ![5, 4, 1, 0, 2, 3]], proof := .tail 54 }

theorem namedLeaf058_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 17850)) namedLeaf058 = true :=
  by decide +kernel

def namedLeaf059 : LeafData := { rows := ![![2, 3, 5, 4, 6, 1], ![2, 3, 4, 5, 6, 0], ![1, 0, 3, 5, 4, 6], ![1, 0, 2, 5, 4, 6], ![1, 5, 0, 2, 3, 6], ![1, 4, 0, 2, 3, 6], ![1, 0, 2, 3, 4, 5]], proof := .low (![341, 255, 365, 20, 84, 416, 45, 107, 197, 229, 371, 371, 29, 241, 224, 144, 41, 333, 206, 2, 106, 105, 302, 149, 386, 43, 15, 383]) }

theorem namedLeaf059_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 17851)) namedLeaf059 = true :=
  by decide +kernel

def namedLeaf060 : LeafData := { rows := ![![2, 3, 5, 4, 6, 1], ![2, 3, 4, 5, 6, 0], ![1, 0, 3, 5, 4, 6], ![1, 0, 2, 5, 6, 4], ![1, 5, 0, 2, 6, 3], ![1, 4, 0, 2, 3, 6], ![1, 0, 2, 4, 3, 5]], proof := .tail 292 }

theorem namedLeaf060_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 17852)) namedLeaf060 = true :=
  by decide +kernel

def namedLeaf061 : LeafData := { rows := ![![2, 3, 5, 4, 6, 1], ![2, 3, 4, 5, 6, 0], ![1, 0, 3, 5, 4, 6], ![1, 0, 2, 6, 5, 4], ![1, 5, 0, 2, 6, 3], ![1, 4, 0, 2, 6, 3], ![1, 0, 2, 4, 5, 3]], proof := .tail 201 }

theorem namedLeaf061_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 17853)) namedLeaf061 = true :=
  by decide +kernel

def namedLeaf062 : LeafData := { rows := ![![2, 3, 5, 4, 6, 1], ![2, 3, 4, 5, 6, 0], ![1, 0, 3, 5, 6, 4], ![1, 0, 2, 5, 6, 4], ![1, 5, 0, 6, 2, 3], ![1, 4, 0, 2, 3, 6], ![1, 0, 4, 2, 3, 5]], proof := .tail 412 }

theorem namedLeaf062_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 17854)) namedLeaf062 = true :=
  by decide +kernel

def namedLeaf063 : LeafData := { rows := ![![2, 3, 5, 4, 6, 1], ![2, 3, 4, 5, 6, 0], ![1, 0, 3, 5, 6, 4], ![1, 0, 2, 6, 5, 4], ![1, 5, 0, 6, 2, 3], ![1, 4, 0, 2, 6, 3], ![1, 0, 4, 2, 5, 3]], proof := .tail 128 }

theorem namedLeaf063_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 17855)) namedLeaf063 = true :=
  by decide +kernel

def namedLeaf064 : LeafData := { rows := ![![2, 3, 5, 4, 6, 1], ![2, 3, 4, 5, 6, 0], ![1, 0, 3, 6, 5, 4], ![1, 0, 2, 6, 5, 4], ![1, 5, 0, 6, 2, 3], ![1, 4, 0, 6, 2, 3], ![1, 0, 4, 5, 2, 3]], proof := .tail 114 }

theorem namedLeaf064_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 17856)) namedLeaf064 = true :=
  by decide +kernel

def namedLeaf065 : LeafData := { rows := ![![2, 3, 5, 6, 4, 1], ![2, 3, 4, 5, 6, 0], ![1, 0, 3, 5, 6, 4], ![1, 0, 2, 5, 6, 4], ![1, 5, 6, 0, 2, 3], ![1, 4, 0, 2, 3, 6], ![1, 4, 0, 2, 3, 5]], proof := .low (![276, 8, 280, 20, 179, 416, 417, 242, 58, 148, 103, 184, 110, 306, 252, 94, 366, 307, 33, 291, 262, 67, 9, 149, 316, 43, 243, 243]) }

theorem namedLeaf065_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 17857)) namedLeaf065 = true :=
  by decide +kernel

def namedLeaf066 : LeafData := { rows := ![![2, 3, 5, 6, 4, 1], ![2, 3, 4, 5, 6, 0], ![1, 0, 3, 5, 6, 4], ![1, 0, 2, 6, 5, 4], ![1, 5, 6, 0, 2, 3], ![1, 4, 0, 2, 6, 3], ![1, 4, 0, 2, 5, 3]], proof := .low (![323, 331, 60, 20, 334, 416, 138, 405, 355, 282, 408, 168, 110, 277, 263, 94, 65, 307, 263, 291, 181, 432, 251, 149, 316, 43, 260, 394]) }

theorem namedLeaf066_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 17858)) namedLeaf066 = true :=
  by decide +kernel

def namedLeaf067 : LeafData := { rows := ![![2, 3, 5, 6, 4, 1], ![2, 3, 4, 5, 6, 0], ![1, 0, 3, 6, 5, 4], ![1, 0, 2, 6, 5, 4], ![1, 5, 6, 0, 2, 3], ![1, 4, 0, 6, 2, 3], ![1, 4, 0, 5, 2, 3]], proof := .low (![119, 312, 340, 20, 179, 35, 138, 100, 200, 401, 71, 301, 110, 147, 356, 94, 34, 307, 356, 291, 133, 432, 251, 149, 316, 43, 243, 186]) }

theorem namedLeaf067_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 17859)) namedLeaf067 = true :=
  by decide +kernel

def namedLeaf068 : LeafData := { rows := ![![2, 3, 6, 5, 4, 1], ![2, 3, 4, 5, 6, 0], ![1, 0, 3, 6, 5, 4], ![1, 0, 2, 6, 5, 4], ![1, 5, 6, 0, 2, 3], ![1, 4, 6, 0, 2, 3], ![1, 4, 5, 0, 2, 3]], proof := .tail 378 }

theorem namedLeaf068_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 17860)) namedLeaf068 = true :=
  by decide +kernel

def namedLeaf069 : LeafData := { rows := ![![2, 3, 6, 5, 4, 1], ![2, 3, 4, 5, 6, 0], ![1, 0, 3, 6, 5, 4], ![1, 0, 2, 6, 5, 4], ![1, 6, 5, 0, 2, 3], ![1, 6, 4, 0, 2, 3], ![1, 5, 4, 0, 2, 3]], proof := .tail 342 }

theorem namedLeaf069_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 17861)) namedLeaf069 = true :=
  by decide +kernel

def namedLeaf070 : LeafData := { rows := ![![2, 3, 6, 5, 4, 1], ![2, 3, 4, 6, 5, 0], ![1, 0, 3, 6, 5, 4], ![1, 0, 2, 6, 5, 4], ![1, 6, 5, 0, 2, 3], ![6, 1, 4, 0, 2, 3], ![5, 1, 4, 0, 2, 3]], proof := .low (![141, 339, 50, 32, 175, 210, 12, 85, 207, 368, 4, 350, 132, 381, 324, 298, 267, 348, 217, 182, 418, 299, 397, 16, 143, 427, 117, 122]) }

theorem namedLeaf070_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 17862)) namedLeaf070 = true :=
  by decide +kernel

def namedLeaf071 : LeafData := { rows := ![![2, 3, 6, 5, 4, 1], ![2, 3, 6, 4, 5, 0], ![1, 0, 3, 6, 5, 4], ![1, 0, 2, 6, 5, 4], ![6, 1, 5, 0, 2, 3], ![6, 1, 4, 0, 2, 3], ![5, 4, 1, 0, 2, 3]], proof := .tail 152 }

theorem namedLeaf071_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 17863)) namedLeaf071 = true :=
  by decide +kernel

def namedLeaf072 : LeafData := { rows := ![![2, 3, 5, 4, 6, 1], ![2, 3, 5, 4, 6, 0], ![1, 0, 3, 5, 4, 6], ![1, 0, 2, 5, 4, 6], ![5, 1, 0, 2, 3, 6], ![4, 1, 0, 2, 3, 6], ![1, 0, 2, 3, 4, 5]], proof := .low (![7, 256, 37, 96, 414, 13, 329, 10, 363, 102, 27, 185, 220, 231, 332, 112, 395, 47, 74, 244, 431, 345, 362, 48, 415, 18, 219, 273]) }

theorem namedLeaf072_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 17864)) namedLeaf072 = true :=
  by decide +kernel

def namedLeaf073 : LeafData := { rows := ![![2, 3, 5, 4, 6, 1], ![2, 3, 5, 4, 6, 0], ![1, 0, 3, 5, 4, 6], ![1, 0, 2, 5, 6, 4], ![5, 1, 0, 2, 6, 3], ![4, 1, 0, 2, 3, 6], ![1, 0, 2, 4, 3, 5]], proof := .tail 14 }

theorem namedLeaf073_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 17865)) namedLeaf073 = true :=
  by decide +kernel

def namedLeaf074 : LeafData := { rows := ![![2, 3, 5, 4, 6, 1], ![2, 3, 5, 4, 6, 0], ![1, 0, 3, 5, 4, 6], ![1, 0, 2, 6, 5, 4], ![5, 1, 0, 2, 6, 3], ![4, 1, 0, 2, 6, 3], ![1, 0, 2, 4, 5, 3]], proof := .tail 407 }

theorem namedLeaf074_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 17866)) namedLeaf074 = true :=
  by decide +kernel

def namedLeaf075 : LeafData := { rows := ![![2, 3, 5, 4, 6, 1], ![2, 3, 5, 4, 6, 0], ![1, 0, 3, 5, 6, 4], ![1, 0, 2, 5, 6, 4], ![5, 1, 0, 6, 2, 3], ![4, 1, 0, 2, 3, 6], ![1, 0, 4, 2, 3, 5]], proof := .tail 73 }

theorem namedLeaf075_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 17867)) namedLeaf075 = true :=
  by decide +kernel

def namedLeaf076 : LeafData := { rows := ![![2, 3, 5, 4, 6, 1], ![2, 3, 5, 4, 6, 0], ![1, 0, 3, 5, 6, 4], ![1, 0, 2, 6, 5, 4], ![5, 1, 0, 6, 2, 3], ![4, 1, 0, 2, 6, 3], ![1, 0, 4, 2, 5, 3]], proof := .tail 108 }

theorem namedLeaf076_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 17868)) namedLeaf076 = true :=
  by decide +kernel

def namedLeaf077 : LeafData := { rows := ![![2, 3, 5, 4, 6, 1], ![2, 3, 5, 4, 6, 0], ![1, 0, 3, 6, 5, 4], ![1, 0, 2, 6, 5, 4], ![5, 1, 0, 6, 2, 3], ![4, 1, 0, 6, 2, 3], ![1, 0, 4, 5, 2, 3]], proof := .tail 177 }

theorem namedLeaf077_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 17869)) namedLeaf077 = true :=
  by decide +kernel

def namedLeaf078 : LeafData := { rows := ![![2, 3, 5, 6, 4, 1], ![2, 3, 5, 4, 6, 0], ![1, 0, 3, 5, 6, 4], ![1, 0, 2, 5, 6, 4], ![5, 1, 6, 0, 2, 3], ![4, 1, 0, 2, 3, 6], ![1, 4, 0, 2, 3, 5]], proof := .tail 321 }

theorem namedLeaf078_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 17870)) namedLeaf078 = true :=
  by decide +kernel

def namedLeaf079 : LeafData := { rows := ![![2, 3, 5, 6, 4, 1], ![2, 3, 5, 4, 6, 0], ![1, 0, 3, 5, 6, 4], ![1, 0, 2, 6, 5, 4], ![5, 1, 6, 0, 2, 3], ![4, 1, 0, 2, 6, 3], ![1, 4, 0, 2, 5, 3]], proof := .tail 391 }

theorem namedLeaf079_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 17871)) namedLeaf079 = true :=
  by decide +kernel

def namedLeaf080 : LeafData := { rows := ![![2, 3, 5, 6, 4, 1], ![2, 3, 5, 4, 6, 0], ![1, 0, 3, 6, 5, 4], ![1, 0, 2, 6, 5, 4], ![5, 1, 6, 0, 2, 3], ![4, 1, 0, 6, 2, 3], ![1, 4, 0, 5, 2, 3]], proof := .tail 375 }

theorem namedLeaf080_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 17872)) namedLeaf080 = true :=
  by decide +kernel

def namedLeaf081 : LeafData := { rows := ![![2, 3, 6, 5, 4, 1], ![2, 3, 5, 4, 6, 0], ![1, 0, 3, 6, 5, 4], ![1, 0, 2, 6, 5, 4], ![5, 1, 6, 0, 2, 3], ![4, 1, 6, 0, 2, 3], ![1, 4, 5, 0, 2, 3]], proof := .tail 385 }

theorem namedLeaf081_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 17873)) namedLeaf081 = true :=
  by decide +kernel

def namedLeaf082 : LeafData := { rows := ![![2, 3, 5, 6, 4, 1], ![2, 3, 5, 6, 4, 0], ![1, 0, 3, 5, 6, 4], ![1, 0, 2, 5, 6, 4], ![5, 6, 1, 0, 2, 3], ![4, 1, 0, 2, 3, 6], ![4, 1, 0, 2, 3, 5]], proof := .low (![352, 137, 235, 295, 357, 214, 283, 174, 86, 271, 6, 184, 135, 31, 169, 91, 38, 189, 124, 319, 346, 284, 325, 42, 150, 142, 5, 192]) }

theorem namedLeaf082_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 17874)) namedLeaf082 = true :=
  by decide +kernel

def namedLeaf083 : LeafData := { rows := ![![2, 3, 5, 6, 4, 1], ![2, 3, 5, 6, 4, 0], ![1, 0, 3, 5, 6, 4], ![1, 0, 2, 6, 5, 4], ![5, 6, 1, 0, 2, 3], ![4, 1, 0, 2, 6, 3], ![4, 1, 0, 2, 5, 3]], proof := .low (![377, 137, 314, 295, 357, 214, 283, 174, 86, 271, 6, 353, 268, 31, 169, 91, 38, 189, 124, 319, 346, 161, 325, 42, 150, 142, 5, 192]) }

theorem namedLeaf083_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 17875)) namedLeaf083 = true :=
  by decide +kernel

def namedLeaf084 : LeafData := { rows := ![![2, 3, 5, 6, 4, 1], ![2, 3, 5, 6, 4, 0], ![1, 0, 3, 6, 5, 4], ![1, 0, 2, 6, 5, 4], ![5, 6, 1, 0, 2, 3], ![4, 1, 0, 6, 2, 3], ![4, 1, 0, 5, 2, 3]], proof := .low (![115, 137, 314, 328, 357, 214, 283, 174, 86, 423, 6, 167, 135, 31, 169, 91, 38, 189, 124, 319, 346, 161, 325, 42, 254, 142, 5, 192]) }

theorem namedLeaf084_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 17876)) namedLeaf084 = true :=
  by decide +kernel

def namedLeaf085 : LeafData := { rows := ![![2, 3, 6, 5, 4, 1], ![2, 3, 5, 6, 4, 0], ![1, 0, 3, 6, 5, 4], ![1, 0, 2, 6, 5, 4], ![5, 6, 1, 0, 2, 3], ![4, 1, 6, 0, 2, 3], ![4, 1, 5, 0, 2, 3]], proof := .low (![22, 349, 101, 158, 357, 214, 343, 388, 139, 384, 6, 87, 293, 51, 173, 91, 264, 156, 369, 319, 157, 380, 325, 42, 68, 142, 5, 192]) }

theorem namedLeaf085_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 17877)) namedLeaf085 = true :=
  by decide +kernel

def namedLeaf086 : LeafData := { rows := ![![2, 3, 6, 5, 4, 1], ![2, 3, 6, 5, 4, 0], ![1, 0, 3, 6, 5, 4], ![1, 0, 2, 6, 5, 4], ![5, 6, 1, 0, 2, 3], ![4, 6, 1, 0, 2, 3], ![4, 5, 1, 0, 2, 3]], proof := .tail 194 }

theorem namedLeaf086_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 17878)) namedLeaf086 = true :=
  by decide +kernel

def namedLeaf087 : LeafData := { rows := ![![2, 3, 6, 5, 4, 1], ![2, 3, 6, 5, 4, 0], ![1, 0, 3, 6, 5, 4], ![1, 0, 2, 6, 5, 4], ![6, 5, 1, 0, 2, 3], ![6, 4, 1, 0, 2, 3], ![5, 4, 1, 0, 2, 3]], proof := .tail 245 }

theorem namedLeaf087_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 17879)) namedLeaf087 = true :=
  by decide +kernel

def namedLeaf088 : LeafData := { rows := ![![2, 3, 4, 5, 6, 1], ![2, 3, 4, 5, 6, 0], ![1, 0, 6, 3, 4, 5], ![1, 0, 6, 2, 4, 5], ![1, 0, 6, 2, 3, 5], ![1, 0, 6, 2, 3, 4], ![1, 0, 5, 4, 3, 2]], proof := .tail 83 }

theorem namedLeaf088_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 17880)) namedLeaf088 = true :=
  by decide +kernel

def namedLeaf089 : LeafData := { rows := ![![2, 3, 4, 5, 6, 1], ![2, 3, 4, 5, 6, 0], ![1, 0, 6, 3, 4, 5], ![1, 0, 6, 2, 5, 4], ![1, 0, 6, 2, 5, 3], ![1, 0, 6, 2, 4, 3], ![1, 0, 5, 4, 3, 2]], proof := .tail 191 }

theorem namedLeaf089_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 17881)) namedLeaf089 = true :=
  by decide +kernel

def namedLeaf090 : LeafData := { rows := ![![2, 3, 4, 5, 6, 1], ![2, 3, 4, 5, 6, 0], ![1, 0, 6, 3, 5, 4], ![1, 0, 6, 2, 5, 4], ![1, 0, 5, 6, 2, 3], ![1, 0, 4, 6, 2, 3], ![1, 0, 4, 5, 3, 2]], proof := .tail 123 }

theorem namedLeaf090_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 17882)) namedLeaf090 = true :=
  by decide +kernel

def namedLeaf091 : LeafData := { rows := ![![2, 3, 4, 5, 6, 1], ![2, 3, 4, 5, 6, 0], ![1, 0, 6, 3, 5, 4], ![1, 0, 6, 2, 5, 4], ![1, 0, 6, 5, 2, 3], ![1, 0, 6, 4, 2, 3], ![1, 0, 5, 4, 3, 2]], proof := .tail 178 }

theorem namedLeaf091_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 17883)) namedLeaf091 = true :=
  by decide +kernel

def namedLeaf092 : LeafData := { rows := ![![2, 3, 5, 4, 6, 1], ![2, 3, 4, 5, 6, 0], ![1, 0, 6, 3, 5, 4], ![1, 0, 6, 2, 5, 4], ![1, 5, 0, 6, 2, 3], ![1, 4, 0, 6, 2, 3], ![1, 0, 4, 5, 3, 2]], proof := .tail 121 }

theorem namedLeaf092_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 17884)) namedLeaf092 = true :=
  by decide +kernel

def namedLeaf093 : LeafData := { rows := ![![2, 3, 5, 4, 6, 1], ![2, 3, 5, 4, 6, 0], ![1, 0, 6, 3, 5, 4], ![1, 0, 6, 2, 5, 4], ![5, 1, 0, 6, 2, 3], ![4, 1, 0, 6, 2, 3], ![1, 0, 4, 5, 3, 2]], proof := .tail 240 }

theorem namedLeaf093_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 17885)) namedLeaf093 = true :=
  by decide +kernel

def namedLeaf094 : LeafData := { rows := ![![2, 3, 4, 6, 5, 1], ![2, 3, 4, 5, 6, 0], ![1, 0, 6, 3, 4, 5], ![1, 0, 6, 2, 4, 5], ![1, 0, 6, 2, 3, 5], ![1, 6, 0, 2, 3, 4], ![1, 5, 0, 4, 3, 2]], proof := .tail 162 }

theorem namedLeaf094_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 17886)) namedLeaf094 = true :=
  by decide +kernel

def namedLeaf095 : LeafData := { rows := ![![2, 3, 4, 6, 5, 1], ![2, 3, 4, 5, 6, 0], ![1, 0, 6, 3, 4, 5], ![1, 0, 6, 2, 5, 4], ![1, 0, 6, 2, 5, 3], ![1, 6, 0, 2, 4, 3], ![1, 5, 0, 4, 3, 2]], proof := .tail 296 }

theorem namedLeaf095_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 17887)) namedLeaf095 = true :=
  by decide +kernel

def namedLeaf096 : LeafData := { rows := ![![2, 3, 4, 6, 5, 1], ![2, 3, 4, 5, 6, 0], ![1, 0, 6, 3, 5, 4], ![1, 0, 6, 2, 5, 4], ![1, 0, 6, 5, 2, 3], ![1, 6, 0, 4, 2, 3], ![1, 5, 0, 4, 3, 2]], proof := .tail 178 }

theorem namedLeaf096_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 17888)) namedLeaf096 = true :=
  by decide +kernel

def namedLeaf097 : LeafData := { rows := ![![2, 3, 4, 6, 5, 1], ![2, 3, 4, 6, 5, 0], ![1, 0, 6, 3, 4, 5], ![1, 0, 6, 2, 4, 5], ![1, 0, 6, 2, 3, 5], ![6, 1, 0, 2, 3, 4], ![5, 1, 0, 4, 3, 2]], proof := .tail 367 }

theorem namedLeaf097_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 17889)) namedLeaf097 = true :=
  by decide +kernel

def namedLeaf098 : LeafData := { rows := ![![2, 3, 4, 6, 5, 1], ![2, 3, 4, 6, 5, 0], ![1, 0, 6, 3, 4, 5], ![1, 0, 6, 2, 5, 4], ![1, 0, 6, 2, 5, 3], ![6, 1, 0, 2, 4, 3], ![5, 1, 0, 4, 3, 2]], proof := .tail 310 }

theorem namedLeaf098_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 17890)) namedLeaf098 = true :=
  by decide +kernel

def namedLeaf099 : LeafData := { rows := ![![2, 3, 4, 6, 5, 1], ![2, 3, 4, 6, 5, 0], ![1, 0, 6, 3, 5, 4], ![1, 0, 6, 2, 5, 4], ![1, 0, 6, 5, 2, 3], ![6, 1, 0, 4, 2, 3], ![5, 1, 0, 4, 3, 2]], proof := .tail 178 }

theorem namedLeaf099_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 17891)) namedLeaf099 = true :=
  by decide +kernel

def namedLeaf100 : LeafData := { rows := ![![2, 3, 5, 6, 4, 1], ![2, 3, 4, 5, 6, 0], ![1, 0, 6, 3, 5, 4], ![1, 0, 6, 2, 5, 4], ![1, 5, 6, 0, 2, 3], ![1, 4, 0, 6, 2, 3], ![1, 4, 0, 5, 3, 2]], proof := .tail 123 }

theorem namedLeaf100_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 17892)) namedLeaf100 = true :=
  by decide +kernel

def namedLeaf101 : LeafData := { rows := ![![2, 3, 5, 6, 4, 1], ![2, 3, 5, 4, 6, 0], ![1, 0, 6, 3, 5, 4], ![1, 0, 6, 2, 5, 4], ![5, 1, 6, 0, 2, 3], ![4, 1, 0, 6, 2, 3], ![1, 4, 0, 5, 3, 2]], proof := .tail 240 }

theorem namedLeaf101_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 17893)) namedLeaf101 = true :=
  by decide +kernel

def namedLeaf102 : LeafData := { rows := ![![2, 3, 5, 6, 4, 1], ![2, 3, 5, 6, 4, 0], ![1, 0, 6, 3, 5, 4], ![1, 0, 6, 2, 5, 4], ![5, 6, 1, 0, 2, 3], ![4, 1, 0, 6, 2, 3], ![4, 1, 0, 5, 3, 2]], proof := .tail 123 }

theorem namedLeaf102_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 17894)) namedLeaf102 = true :=
  by decide +kernel

def namedLeaf103 : LeafData := { rows := ![![2, 3, 6, 4, 5, 1], ![2, 3, 4, 5, 6, 0], ![1, 0, 6, 3, 4, 5], ![1, 0, 6, 2, 4, 5], ![1, 6, 0, 2, 3, 5], ![1, 6, 0, 2, 3, 4], ![1, 5, 4, 0, 3, 2]], proof := .tail 344 }

theorem namedLeaf103_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 17895)) namedLeaf103 = true :=
  by decide +kernel

def namedLeaf104 : LeafData := { rows := ![![2, 3, 6, 4, 5, 1], ![2, 3, 4, 5, 6, 0], ![1, 0, 6, 3, 4, 5], ![1, 0, 6, 2, 5, 4], ![1, 6, 0, 2, 5, 3], ![1, 6, 0, 2, 4, 3], ![1, 5, 4, 0, 3, 2]], proof := .tail 146 }

theorem namedLeaf104_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 17896)) namedLeaf104 = true :=
  by decide +kernel

def namedLeaf105 : LeafData := { rows := ![![2, 3, 6, 4, 5, 1], ![2, 3, 4, 5, 6, 0], ![1, 0, 6, 3, 5, 4], ![1, 0, 6, 2, 5, 4], ![1, 6, 0, 5, 2, 3], ![1, 6, 0, 4, 2, 3], ![1, 5, 4, 0, 3, 2]], proof := .tail 82 }

theorem namedLeaf105_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 17897)) namedLeaf105 = true :=
  by decide +kernel

def namedLeaf106 : LeafData := { rows := ![![2, 3, 6, 5, 4, 1], ![2, 3, 4, 5, 6, 0], ![1, 0, 6, 3, 5, 4], ![1, 0, 6, 2, 5, 4], ![1, 5, 6, 0, 2, 3], ![1, 4, 6, 0, 2, 3], ![1, 4, 5, 0, 3, 2]], proof := .tail 145 }

theorem namedLeaf106_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 17898)) namedLeaf106 = true :=
  by decide +kernel

def namedLeaf107 : LeafData := { rows := ![![2, 3, 6, 5, 4, 1], ![2, 3, 4, 5, 6, 0], ![1, 0, 6, 3, 5, 4], ![1, 0, 6, 2, 5, 4], ![1, 6, 5, 0, 2, 3], ![1, 6, 4, 0, 2, 3], ![1, 5, 4, 0, 3, 2]], proof := .tail 64 }

theorem namedLeaf107_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 17899)) namedLeaf107 = true :=
  by decide +kernel

def namedLeaf108 : LeafData := { rows := ![![2, 3, 6, 5, 4, 1], ![2, 3, 5, 4, 6, 0], ![1, 0, 6, 3, 5, 4], ![1, 0, 6, 2, 5, 4], ![5, 1, 6, 0, 2, 3], ![4, 1, 6, 0, 2, 3], ![1, 4, 5, 0, 3, 2]], proof := .tail 240 }

theorem namedLeaf108_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 17900)) namedLeaf108 = true :=
  by decide +kernel

def namedLeaf109 : LeafData := { rows := ![![2, 3, 6, 4, 5, 1], ![2, 3, 4, 6, 5, 0], ![1, 0, 6, 3, 4, 5], ![1, 0, 6, 2, 4, 5], ![1, 6, 0, 2, 3, 5], ![6, 1, 0, 2, 3, 4], ![5, 1, 4, 0, 3, 2]], proof := .tail 376 }

theorem namedLeaf109_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 17901)) namedLeaf109 = true :=
  by decide +kernel

def namedLeaf110 : LeafData := { rows := ![![2, 3, 6, 4, 5, 1], ![2, 3, 4, 6, 5, 0], ![1, 0, 6, 3, 4, 5], ![1, 0, 6, 2, 5, 4], ![1, 6, 0, 2, 5, 3], ![6, 1, 0, 2, 4, 3], ![5, 1, 4, 0, 3, 2]], proof := .tail 146 }

theorem namedLeaf110_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 17902)) namedLeaf110 = true :=
  by decide +kernel

def namedLeaf111 : LeafData := { rows := ![![2, 3, 6, 4, 5, 1], ![2, 3, 4, 6, 5, 0], ![1, 0, 6, 3, 5, 4], ![1, 0, 6, 2, 5, 4], ![1, 6, 0, 5, 2, 3], ![6, 1, 0, 4, 2, 3], ![5, 1, 4, 0, 3, 2]], proof := .tail 82 }

theorem namedLeaf111_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 17903)) namedLeaf111 = true :=
  by decide +kernel

def namedLeaf112 : LeafData := { rows := ![![2, 3, 6, 5, 4, 1], ![2, 3, 4, 6, 5, 0], ![1, 0, 6, 3, 5, 4], ![1, 0, 6, 2, 5, 4], ![1, 6, 5, 0, 2, 3], ![6, 1, 4, 0, 2, 3], ![5, 1, 4, 0, 3, 2]], proof := .tail 178 }

theorem namedLeaf112_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 17904)) namedLeaf112 = true :=
  by decide +kernel

def namedLeaf113 : LeafData := { rows := ![![2, 3, 6, 5, 4, 1], ![2, 3, 5, 6, 4, 0], ![1, 0, 6, 3, 5, 4], ![1, 0, 6, 2, 5, 4], ![5, 6, 1, 0, 2, 3], ![4, 1, 6, 0, 2, 3], ![4, 1, 5, 0, 3, 2]], proof := .tail 123 }

theorem namedLeaf113_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 17905)) namedLeaf113 = true :=
  by decide +kernel

def namedLeaf114 : LeafData := { rows := ![![2, 3, 6, 4, 5, 1], ![2, 3, 6, 4, 5, 0], ![1, 0, 6, 3, 4, 5], ![1, 0, 6, 2, 4, 5], ![6, 1, 0, 2, 3, 5], ![6, 1, 0, 2, 3, 4], ![5, 4, 1, 0, 3, 2]], proof := .tail 317 }

theorem namedLeaf114_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 17906)) namedLeaf114 = true :=
  by decide +kernel

def namedLeaf115 : LeafData := { rows := ![![2, 3, 6, 4, 5, 1], ![2, 3, 6, 4, 5, 0], ![1, 0, 6, 3, 4, 5], ![1, 0, 6, 2, 5, 4], ![6, 1, 0, 2, 5, 3], ![6, 1, 0, 2, 4, 3], ![5, 4, 1, 0, 3, 2]], proof := .tail 226 }

theorem namedLeaf115_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 17907)) namedLeaf115 = true :=
  by decide +kernel

def namedLeaf116 : LeafData := { rows := ![![2, 3, 6, 4, 5, 1], ![2, 3, 6, 4, 5, 0], ![1, 0, 6, 3, 5, 4], ![1, 0, 6, 2, 5, 4], ![6, 1, 0, 5, 2, 3], ![6, 1, 0, 4, 2, 3], ![5, 4, 1, 0, 3, 2]], proof := .tail 54 }

theorem namedLeaf116_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 17908)) namedLeaf116 = true :=
  by decide +kernel

def namedLeaf117 : LeafData := { rows := ![![2, 3, 6, 5, 4, 1], ![2, 3, 6, 4, 5, 0], ![1, 0, 6, 3, 5, 4], ![1, 0, 6, 2, 5, 4], ![6, 1, 5, 0, 2, 3], ![6, 1, 4, 0, 2, 3], ![5, 4, 1, 0, 3, 2]], proof := .tail 152 }

theorem namedLeaf117_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 17909)) namedLeaf117 = true :=
  by decide +kernel

def namedLeaf118 : LeafData := { rows := ![![2, 3, 6, 5, 4, 1], ![2, 3, 6, 5, 4, 0], ![1, 0, 6, 3, 5, 4], ![1, 0, 6, 2, 5, 4], ![5, 6, 1, 0, 2, 3], ![4, 6, 1, 0, 2, 3], ![4, 5, 1, 0, 3, 2]], proof := .tail 123 }

theorem namedLeaf118_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 17910)) namedLeaf118 = true :=
  by decide +kernel

def namedLeaf119 : LeafData := { rows := ![![2, 3, 6, 5, 4, 1], ![2, 3, 6, 5, 4, 0], ![1, 0, 6, 3, 5, 4], ![1, 0, 6, 2, 5, 4], ![6, 5, 1, 0, 2, 3], ![6, 4, 1, 0, 2, 3], ![5, 4, 1, 0, 3, 2]], proof := .tail 25 }

theorem namedLeaf119_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 17911)) namedLeaf119 = true :=
  by decide +kernel

def namedLeaf120 : LeafData := { rows := ![![2, 6, 3, 4, 5, 1], ![2, 3, 4, 5, 6, 0], ![1, 0, 6, 3, 4, 5], ![1, 6, 0, 2, 4, 5], ![1, 6, 0, 2, 3, 5], ![1, 6, 0, 2, 3, 4], ![1, 5, 4, 3, 0, 2]], proof := .tail 162 }

theorem namedLeaf120_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 17912)) namedLeaf120 = true :=
  by decide +kernel

def namedLeaf121 : LeafData := { rows := ![![2, 6, 3, 4, 5, 1], ![2, 3, 4, 5, 6, 0], ![1, 0, 6, 3, 4, 5], ![1, 6, 0, 2, 5, 4], ![1, 6, 0, 2, 5, 3], ![1, 6, 0, 2, 4, 3], ![1, 5, 4, 3, 0, 2]], proof := .tail 146 }

theorem namedLeaf121_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 17913)) namedLeaf121 = true :=
  by decide +kernel

def namedLeaf122 : LeafData := { rows := ![![2, 6, 3, 4, 5, 1], ![2, 3, 4, 5, 6, 0], ![1, 0, 6, 3, 5, 4], ![1, 6, 0, 2, 5, 4], ![1, 6, 0, 5, 2, 3], ![1, 6, 0, 4, 2, 3], ![1, 5, 4, 3, 0, 2]], proof := .tail 82 }

theorem namedLeaf122_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 17914)) namedLeaf122 = true :=
  by decide +kernel

def namedLeaf123 : LeafData := { rows := ![![2, 6, 3, 5, 4, 1], ![2, 3, 4, 5, 6, 0], ![1, 0, 6, 3, 5, 4], ![1, 6, 0, 2, 5, 4], ![1, 5, 6, 0, 2, 3], ![1, 4, 6, 0, 2, 3], ![1, 4, 5, 3, 0, 2]], proof := .tail 409 }

theorem namedLeaf123_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 17915)) namedLeaf123 = true :=
  by decide +kernel

def namedLeaf124 : LeafData := { rows := ![![2, 6, 3, 5, 4, 1], ![2, 3, 4, 5, 6, 0], ![1, 0, 6, 3, 5, 4], ![1, 6, 0, 2, 5, 4], ![1, 6, 5, 0, 2, 3], ![1, 6, 4, 0, 2, 3], ![1, 5, 4, 3, 0, 2]], proof := .tail 64 }

theorem namedLeaf124_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 17916)) namedLeaf124 = true :=
  by decide +kernel

def namedLeaf125 : LeafData := { rows := ![![2, 6, 3, 5, 4, 1], ![2, 3, 5, 4, 6, 0], ![1, 0, 6, 3, 5, 4], ![1, 6, 0, 2, 5, 4], ![5, 1, 6, 0, 2, 3], ![4, 1, 6, 0, 2, 3], ![1, 4, 5, 3, 0, 2]], proof := .tail 92 }

theorem namedLeaf125_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 17917)) namedLeaf125 = true :=
  by decide +kernel

def namedLeaf126 : LeafData := { rows := ![![2, 6, 3, 4, 5, 1], ![2, 3, 4, 6, 5, 0], ![1, 0, 6, 3, 4, 5], ![1, 6, 0, 2, 4, 5], ![1, 6, 0, 2, 3, 5], ![6, 1, 0, 2, 3, 4], ![5, 1, 4, 3, 0, 2]], proof := .tail 162 }

theorem namedLeaf126_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 17918)) namedLeaf126 = true :=
  by decide +kernel

def namedLeaf127 : LeafData := { rows := ![![2, 6, 3, 4, 5, 1], ![2, 3, 4, 6, 5, 0], ![1, 0, 6, 3, 4, 5], ![1, 6, 0, 2, 5, 4], ![1, 6, 0, 2, 5, 3], ![6, 1, 0, 2, 4, 3], ![5, 1, 4, 3, 0, 2]], proof := .tail 146 }

theorem namedLeaf127_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 17919)) namedLeaf127 = true :=
  by decide +kernel

def fallback : LeafData := { rows := fun _ _ => 0, proof := .tail 0 }
def lookup (offset : ℕ) : LeafData :=
  if offset < 128 then (if offset < 64 then (if offset < 32 then (if offset < 16 then (if offset < 8 then (if offset < 4 then (if offset < 2 then (if offset < 1 then (namedLeaf000) else (namedLeaf001)) else (if offset < 3 then (namedLeaf002) else (namedLeaf003))) else (if offset < 6 then (if offset < 5 then (namedLeaf004) else (namedLeaf005)) else (if offset < 7 then (namedLeaf006) else (namedLeaf007)))) else (if offset < 12 then (if offset < 10 then (if offset < 9 then (namedLeaf008) else (namedLeaf009)) else (if offset < 11 then (namedLeaf010) else (namedLeaf011))) else (if offset < 14 then (if offset < 13 then (namedLeaf012) else (namedLeaf013)) else (if offset < 15 then (namedLeaf014) else (namedLeaf015))))) else (if offset < 24 then (if offset < 20 then (if offset < 18 then (if offset < 17 then (namedLeaf016) else (namedLeaf017)) else (if offset < 19 then (namedLeaf018) else (namedLeaf019))) else (if offset < 22 then (if offset < 21 then (namedLeaf020) else (namedLeaf021)) else (if offset < 23 then (namedLeaf022) else (namedLeaf023)))) else (if offset < 28 then (if offset < 26 then (if offset < 25 then (namedLeaf024) else (namedLeaf025)) else (if offset < 27 then (namedLeaf026) else (namedLeaf027))) else (if offset < 30 then (if offset < 29 then (namedLeaf028) else (namedLeaf029)) else (if offset < 31 then (namedLeaf030) else (namedLeaf031)))))) else (if offset < 48 then (if offset < 40 then (if offset < 36 then (if offset < 34 then (if offset < 33 then (namedLeaf032) else (namedLeaf033)) else (if offset < 35 then (namedLeaf034) else (namedLeaf035))) else (if offset < 38 then (if offset < 37 then (namedLeaf036) else (namedLeaf037)) else (if offset < 39 then (namedLeaf038) else (namedLeaf039)))) else (if offset < 44 then (if offset < 42 then (if offset < 41 then (namedLeaf040) else (namedLeaf041)) else (if offset < 43 then (namedLeaf042) else (namedLeaf043))) else (if offset < 46 then (if offset < 45 then (namedLeaf044) else (namedLeaf045)) else (if offset < 47 then (namedLeaf046) else (namedLeaf047))))) else (if offset < 56 then (if offset < 52 then (if offset < 50 then (if offset < 49 then (namedLeaf048) else (namedLeaf049)) else (if offset < 51 then (namedLeaf050) else (namedLeaf051))) else (if offset < 54 then (if offset < 53 then (namedLeaf052) else (namedLeaf053)) else (if offset < 55 then (namedLeaf054) else (namedLeaf055)))) else (if offset < 60 then (if offset < 58 then (if offset < 57 then (namedLeaf056) else (namedLeaf057)) else (if offset < 59 then (namedLeaf058) else (namedLeaf059))) else (if offset < 62 then (if offset < 61 then (namedLeaf060) else (namedLeaf061)) else (if offset < 63 then (namedLeaf062) else (namedLeaf063))))))) else (if offset < 96 then (if offset < 80 then (if offset < 72 then (if offset < 68 then (if offset < 66 then (if offset < 65 then (namedLeaf064) else (namedLeaf065)) else (if offset < 67 then (namedLeaf066) else (namedLeaf067))) else (if offset < 70 then (if offset < 69 then (namedLeaf068) else (namedLeaf069)) else (if offset < 71 then (namedLeaf070) else (namedLeaf071)))) else (if offset < 76 then (if offset < 74 then (if offset < 73 then (namedLeaf072) else (namedLeaf073)) else (if offset < 75 then (namedLeaf074) else (namedLeaf075))) else (if offset < 78 then (if offset < 77 then (namedLeaf076) else (namedLeaf077)) else (if offset < 79 then (namedLeaf078) else (namedLeaf079))))) else (if offset < 88 then (if offset < 84 then (if offset < 82 then (if offset < 81 then (namedLeaf080) else (namedLeaf081)) else (if offset < 83 then (namedLeaf082) else (namedLeaf083))) else (if offset < 86 then (if offset < 85 then (namedLeaf084) else (namedLeaf085)) else (if offset < 87 then (namedLeaf086) else (namedLeaf087)))) else (if offset < 92 then (if offset < 90 then (if offset < 89 then (namedLeaf088) else (namedLeaf089)) else (if offset < 91 then (namedLeaf090) else (namedLeaf091))) else (if offset < 94 then (if offset < 93 then (namedLeaf092) else (namedLeaf093)) else (if offset < 95 then (namedLeaf094) else (namedLeaf095)))))) else (if offset < 112 then (if offset < 104 then (if offset < 100 then (if offset < 98 then (if offset < 97 then (namedLeaf096) else (namedLeaf097)) else (if offset < 99 then (namedLeaf098) else (namedLeaf099))) else (if offset < 102 then (if offset < 101 then (namedLeaf100) else (namedLeaf101)) else (if offset < 103 then (namedLeaf102) else (namedLeaf103)))) else (if offset < 108 then (if offset < 106 then (if offset < 105 then (namedLeaf104) else (namedLeaf105)) else (if offset < 107 then (namedLeaf106) else (namedLeaf107))) else (if offset < 110 then (if offset < 109 then (namedLeaf108) else (namedLeaf109)) else (if offset < 111 then (namedLeaf110) else (namedLeaf111))))) else (if offset < 120 then (if offset < 116 then (if offset < 114 then (if offset < 113 then (namedLeaf112) else (namedLeaf113)) else (if offset < 115 then (namedLeaf114) else (namedLeaf115))) else (if offset < 118 then (if offset < 117 then (namedLeaf116) else (namedLeaf117)) else (if offset < 119 then (namedLeaf118) else (namedLeaf119)))) else (if offset < 124 then (if offset < 122 then (if offset < 121 then (namedLeaf120) else (namedLeaf121)) else (if offset < 123 then (namedLeaf122) else (namedLeaf123))) else (if offset < 126 then (if offset < 125 then (namedLeaf124) else (namedLeaf125)) else (if offset < 127 then (namedLeaf126) else (namedLeaf127)))))))) else fallback

theorem point_checked (j : Fin 128) :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 (17792 + j.val))) (lookup j.val) = true := by
  have hjbound : j.val < 128 := j.isLt
  by_cases h64 : j.val < 64
  · by_cases h32 : j.val < 32
    · by_cases h16 : j.val < 16
      · by_cases h8 : j.val < 8
        · by_cases h4 : j.val < 4
          · by_cases h2 : j.val < 2
            · by_cases h1 : j.val < 1
              · have hj : j = ⟨0, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 0
                  omega
                subst j
                exact namedLeaf000_checked
              · have hj : j = ⟨1, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 1
                  omega
                subst j
                exact namedLeaf001_checked
            · by_cases h3 : j.val < 3
              · have hj : j = ⟨2, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 2
                  omega
                subst j
                exact namedLeaf002_checked
              · have hj : j = ⟨3, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 3
                  omega
                subst j
                exact namedLeaf003_checked
          · by_cases h6 : j.val < 6
            · by_cases h5 : j.val < 5
              · have hj : j = ⟨4, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 4
                  omega
                subst j
                exact namedLeaf004_checked
              · have hj : j = ⟨5, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 5
                  omega
                subst j
                exact namedLeaf005_checked
            · by_cases h7 : j.val < 7
              · have hj : j = ⟨6, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 6
                  omega
                subst j
                exact namedLeaf006_checked
              · have hj : j = ⟨7, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 7
                  omega
                subst j
                exact namedLeaf007_checked
        · by_cases h12 : j.val < 12
          · by_cases h10 : j.val < 10
            · by_cases h9 : j.val < 9
              · have hj : j = ⟨8, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 8
                  omega
                subst j
                exact namedLeaf008_checked
              · have hj : j = ⟨9, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 9
                  omega
                subst j
                exact namedLeaf009_checked
            · by_cases h11 : j.val < 11
              · have hj : j = ⟨10, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 10
                  omega
                subst j
                exact namedLeaf010_checked
              · have hj : j = ⟨11, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 11
                  omega
                subst j
                exact namedLeaf011_checked
          · by_cases h14 : j.val < 14
            · by_cases h13 : j.val < 13
              · have hj : j = ⟨12, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 12
                  omega
                subst j
                exact namedLeaf012_checked
              · have hj : j = ⟨13, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 13
                  omega
                subst j
                exact namedLeaf013_checked
            · by_cases h15 : j.val < 15
              · have hj : j = ⟨14, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 14
                  omega
                subst j
                exact namedLeaf014_checked
              · have hj : j = ⟨15, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 15
                  omega
                subst j
                exact namedLeaf015_checked
      · by_cases h24 : j.val < 24
        · by_cases h20 : j.val < 20
          · by_cases h18 : j.val < 18
            · by_cases h17 : j.val < 17
              · have hj : j = ⟨16, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 16
                  omega
                subst j
                exact namedLeaf016_checked
              · have hj : j = ⟨17, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 17
                  omega
                subst j
                exact namedLeaf017_checked
            · by_cases h19 : j.val < 19
              · have hj : j = ⟨18, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 18
                  omega
                subst j
                exact namedLeaf018_checked
              · have hj : j = ⟨19, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 19
                  omega
                subst j
                exact namedLeaf019_checked
          · by_cases h22 : j.val < 22
            · by_cases h21 : j.val < 21
              · have hj : j = ⟨20, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 20
                  omega
                subst j
                exact namedLeaf020_checked
              · have hj : j = ⟨21, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 21
                  omega
                subst j
                exact namedLeaf021_checked
            · by_cases h23 : j.val < 23
              · have hj : j = ⟨22, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 22
                  omega
                subst j
                exact namedLeaf022_checked
              · have hj : j = ⟨23, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 23
                  omega
                subst j
                exact namedLeaf023_checked
        · by_cases h28 : j.val < 28
          · by_cases h26 : j.val < 26
            · by_cases h25 : j.val < 25
              · have hj : j = ⟨24, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 24
                  omega
                subst j
                exact namedLeaf024_checked
              · have hj : j = ⟨25, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 25
                  omega
                subst j
                exact namedLeaf025_checked
            · by_cases h27 : j.val < 27
              · have hj : j = ⟨26, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 26
                  omega
                subst j
                exact namedLeaf026_checked
              · have hj : j = ⟨27, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 27
                  omega
                subst j
                exact namedLeaf027_checked
          · by_cases h30 : j.val < 30
            · by_cases h29 : j.val < 29
              · have hj : j = ⟨28, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 28
                  omega
                subst j
                exact namedLeaf028_checked
              · have hj : j = ⟨29, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 29
                  omega
                subst j
                exact namedLeaf029_checked
            · by_cases h31 : j.val < 31
              · have hj : j = ⟨30, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 30
                  omega
                subst j
                exact namedLeaf030_checked
              · have hj : j = ⟨31, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 31
                  omega
                subst j
                exact namedLeaf031_checked
    · by_cases h48 : j.val < 48
      · by_cases h40 : j.val < 40
        · by_cases h36 : j.val < 36
          · by_cases h34 : j.val < 34
            · by_cases h33 : j.val < 33
              · have hj : j = ⟨32, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 32
                  omega
                subst j
                exact namedLeaf032_checked
              · have hj : j = ⟨33, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 33
                  omega
                subst j
                exact namedLeaf033_checked
            · by_cases h35 : j.val < 35
              · have hj : j = ⟨34, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 34
                  omega
                subst j
                exact namedLeaf034_checked
              · have hj : j = ⟨35, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 35
                  omega
                subst j
                exact namedLeaf035_checked
          · by_cases h38 : j.val < 38
            · by_cases h37 : j.val < 37
              · have hj : j = ⟨36, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 36
                  omega
                subst j
                exact namedLeaf036_checked
              · have hj : j = ⟨37, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 37
                  omega
                subst j
                exact namedLeaf037_checked
            · by_cases h39 : j.val < 39
              · have hj : j = ⟨38, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 38
                  omega
                subst j
                exact namedLeaf038_checked
              · have hj : j = ⟨39, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 39
                  omega
                subst j
                exact namedLeaf039_checked
        · by_cases h44 : j.val < 44
          · by_cases h42 : j.val < 42
            · by_cases h41 : j.val < 41
              · have hj : j = ⟨40, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 40
                  omega
                subst j
                exact namedLeaf040_checked
              · have hj : j = ⟨41, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 41
                  omega
                subst j
                exact namedLeaf041_checked
            · by_cases h43 : j.val < 43
              · have hj : j = ⟨42, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 42
                  omega
                subst j
                exact namedLeaf042_checked
              · have hj : j = ⟨43, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 43
                  omega
                subst j
                exact namedLeaf043_checked
          · by_cases h46 : j.val < 46
            · by_cases h45 : j.val < 45
              · have hj : j = ⟨44, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 44
                  omega
                subst j
                exact namedLeaf044_checked
              · have hj : j = ⟨45, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 45
                  omega
                subst j
                exact namedLeaf045_checked
            · by_cases h47 : j.val < 47
              · have hj : j = ⟨46, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 46
                  omega
                subst j
                exact namedLeaf046_checked
              · have hj : j = ⟨47, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 47
                  omega
                subst j
                exact namedLeaf047_checked
      · by_cases h56 : j.val < 56
        · by_cases h52 : j.val < 52
          · by_cases h50 : j.val < 50
            · by_cases h49 : j.val < 49
              · have hj : j = ⟨48, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 48
                  omega
                subst j
                exact namedLeaf048_checked
              · have hj : j = ⟨49, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 49
                  omega
                subst j
                exact namedLeaf049_checked
            · by_cases h51 : j.val < 51
              · have hj : j = ⟨50, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 50
                  omega
                subst j
                exact namedLeaf050_checked
              · have hj : j = ⟨51, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 51
                  omega
                subst j
                exact namedLeaf051_checked
          · by_cases h54 : j.val < 54
            · by_cases h53 : j.val < 53
              · have hj : j = ⟨52, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 52
                  omega
                subst j
                exact namedLeaf052_checked
              · have hj : j = ⟨53, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 53
                  omega
                subst j
                exact namedLeaf053_checked
            · by_cases h55 : j.val < 55
              · have hj : j = ⟨54, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 54
                  omega
                subst j
                exact namedLeaf054_checked
              · have hj : j = ⟨55, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 55
                  omega
                subst j
                exact namedLeaf055_checked
        · by_cases h60 : j.val < 60
          · by_cases h58 : j.val < 58
            · by_cases h57 : j.val < 57
              · have hj : j = ⟨56, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 56
                  omega
                subst j
                exact namedLeaf056_checked
              · have hj : j = ⟨57, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 57
                  omega
                subst j
                exact namedLeaf057_checked
            · by_cases h59 : j.val < 59
              · have hj : j = ⟨58, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 58
                  omega
                subst j
                exact namedLeaf058_checked
              · have hj : j = ⟨59, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 59
                  omega
                subst j
                exact namedLeaf059_checked
          · by_cases h62 : j.val < 62
            · by_cases h61 : j.val < 61
              · have hj : j = ⟨60, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 60
                  omega
                subst j
                exact namedLeaf060_checked
              · have hj : j = ⟨61, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 61
                  omega
                subst j
                exact namedLeaf061_checked
            · by_cases h63 : j.val < 63
              · have hj : j = ⟨62, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 62
                  omega
                subst j
                exact namedLeaf062_checked
              · have hj : j = ⟨63, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 63
                  omega
                subst j
                exact namedLeaf063_checked
  · by_cases h96 : j.val < 96
    · by_cases h80 : j.val < 80
      · by_cases h72 : j.val < 72
        · by_cases h68 : j.val < 68
          · by_cases h66 : j.val < 66
            · by_cases h65 : j.val < 65
              · have hj : j = ⟨64, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 64
                  omega
                subst j
                exact namedLeaf064_checked
              · have hj : j = ⟨65, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 65
                  omega
                subst j
                exact namedLeaf065_checked
            · by_cases h67 : j.val < 67
              · have hj : j = ⟨66, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 66
                  omega
                subst j
                exact namedLeaf066_checked
              · have hj : j = ⟨67, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 67
                  omega
                subst j
                exact namedLeaf067_checked
          · by_cases h70 : j.val < 70
            · by_cases h69 : j.val < 69
              · have hj : j = ⟨68, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 68
                  omega
                subst j
                exact namedLeaf068_checked
              · have hj : j = ⟨69, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 69
                  omega
                subst j
                exact namedLeaf069_checked
            · by_cases h71 : j.val < 71
              · have hj : j = ⟨70, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 70
                  omega
                subst j
                exact namedLeaf070_checked
              · have hj : j = ⟨71, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 71
                  omega
                subst j
                exact namedLeaf071_checked
        · by_cases h76 : j.val < 76
          · by_cases h74 : j.val < 74
            · by_cases h73 : j.val < 73
              · have hj : j = ⟨72, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 72
                  omega
                subst j
                exact namedLeaf072_checked
              · have hj : j = ⟨73, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 73
                  omega
                subst j
                exact namedLeaf073_checked
            · by_cases h75 : j.val < 75
              · have hj : j = ⟨74, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 74
                  omega
                subst j
                exact namedLeaf074_checked
              · have hj : j = ⟨75, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 75
                  omega
                subst j
                exact namedLeaf075_checked
          · by_cases h78 : j.val < 78
            · by_cases h77 : j.val < 77
              · have hj : j = ⟨76, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 76
                  omega
                subst j
                exact namedLeaf076_checked
              · have hj : j = ⟨77, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 77
                  omega
                subst j
                exact namedLeaf077_checked
            · by_cases h79 : j.val < 79
              · have hj : j = ⟨78, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 78
                  omega
                subst j
                exact namedLeaf078_checked
              · have hj : j = ⟨79, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 79
                  omega
                subst j
                exact namedLeaf079_checked
      · by_cases h88 : j.val < 88
        · by_cases h84 : j.val < 84
          · by_cases h82 : j.val < 82
            · by_cases h81 : j.val < 81
              · have hj : j = ⟨80, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 80
                  omega
                subst j
                exact namedLeaf080_checked
              · have hj : j = ⟨81, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 81
                  omega
                subst j
                exact namedLeaf081_checked
            · by_cases h83 : j.val < 83
              · have hj : j = ⟨82, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 82
                  omega
                subst j
                exact namedLeaf082_checked
              · have hj : j = ⟨83, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 83
                  omega
                subst j
                exact namedLeaf083_checked
          · by_cases h86 : j.val < 86
            · by_cases h85 : j.val < 85
              · have hj : j = ⟨84, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 84
                  omega
                subst j
                exact namedLeaf084_checked
              · have hj : j = ⟨85, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 85
                  omega
                subst j
                exact namedLeaf085_checked
            · by_cases h87 : j.val < 87
              · have hj : j = ⟨86, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 86
                  omega
                subst j
                exact namedLeaf086_checked
              · have hj : j = ⟨87, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 87
                  omega
                subst j
                exact namedLeaf087_checked
        · by_cases h92 : j.val < 92
          · by_cases h90 : j.val < 90
            · by_cases h89 : j.val < 89
              · have hj : j = ⟨88, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 88
                  omega
                subst j
                exact namedLeaf088_checked
              · have hj : j = ⟨89, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 89
                  omega
                subst j
                exact namedLeaf089_checked
            · by_cases h91 : j.val < 91
              · have hj : j = ⟨90, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 90
                  omega
                subst j
                exact namedLeaf090_checked
              · have hj : j = ⟨91, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 91
                  omega
                subst j
                exact namedLeaf091_checked
          · by_cases h94 : j.val < 94
            · by_cases h93 : j.val < 93
              · have hj : j = ⟨92, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 92
                  omega
                subst j
                exact namedLeaf092_checked
              · have hj : j = ⟨93, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 93
                  omega
                subst j
                exact namedLeaf093_checked
            · by_cases h95 : j.val < 95
              · have hj : j = ⟨94, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 94
                  omega
                subst j
                exact namedLeaf094_checked
              · have hj : j = ⟨95, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 95
                  omega
                subst j
                exact namedLeaf095_checked
    · by_cases h112 : j.val < 112
      · by_cases h104 : j.val < 104
        · by_cases h100 : j.val < 100
          · by_cases h98 : j.val < 98
            · by_cases h97 : j.val < 97
              · have hj : j = ⟨96, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 96
                  omega
                subst j
                exact namedLeaf096_checked
              · have hj : j = ⟨97, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 97
                  omega
                subst j
                exact namedLeaf097_checked
            · by_cases h99 : j.val < 99
              · have hj : j = ⟨98, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 98
                  omega
                subst j
                exact namedLeaf098_checked
              · have hj : j = ⟨99, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 99
                  omega
                subst j
                exact namedLeaf099_checked
          · by_cases h102 : j.val < 102
            · by_cases h101 : j.val < 101
              · have hj : j = ⟨100, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 100
                  omega
                subst j
                exact namedLeaf100_checked
              · have hj : j = ⟨101, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 101
                  omega
                subst j
                exact namedLeaf101_checked
            · by_cases h103 : j.val < 103
              · have hj : j = ⟨102, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 102
                  omega
                subst j
                exact namedLeaf102_checked
              · have hj : j = ⟨103, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 103
                  omega
                subst j
                exact namedLeaf103_checked
        · by_cases h108 : j.val < 108
          · by_cases h106 : j.val < 106
            · by_cases h105 : j.val < 105
              · have hj : j = ⟨104, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 104
                  omega
                subst j
                exact namedLeaf104_checked
              · have hj : j = ⟨105, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 105
                  omega
                subst j
                exact namedLeaf105_checked
            · by_cases h107 : j.val < 107
              · have hj : j = ⟨106, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 106
                  omega
                subst j
                exact namedLeaf106_checked
              · have hj : j = ⟨107, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 107
                  omega
                subst j
                exact namedLeaf107_checked
          · by_cases h110 : j.val < 110
            · by_cases h109 : j.val < 109
              · have hj : j = ⟨108, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 108
                  omega
                subst j
                exact namedLeaf108_checked
              · have hj : j = ⟨109, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 109
                  omega
                subst j
                exact namedLeaf109_checked
            · by_cases h111 : j.val < 111
              · have hj : j = ⟨110, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 110
                  omega
                subst j
                exact namedLeaf110_checked
              · have hj : j = ⟨111, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 111
                  omega
                subst j
                exact namedLeaf111_checked
      · by_cases h120 : j.val < 120
        · by_cases h116 : j.val < 116
          · by_cases h114 : j.val < 114
            · by_cases h113 : j.val < 113
              · have hj : j = ⟨112, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 112
                  omega
                subst j
                exact namedLeaf112_checked
              · have hj : j = ⟨113, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 113
                  omega
                subst j
                exact namedLeaf113_checked
            · by_cases h115 : j.val < 115
              · have hj : j = ⟨114, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 114
                  omega
                subst j
                exact namedLeaf114_checked
              · have hj : j = ⟨115, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 115
                  omega
                subst j
                exact namedLeaf115_checked
          · by_cases h118 : j.val < 118
            · by_cases h117 : j.val < 117
              · have hj : j = ⟨116, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 116
                  omega
                subst j
                exact namedLeaf116_checked
              · have hj : j = ⟨117, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 117
                  omega
                subst j
                exact namedLeaf117_checked
            · by_cases h119 : j.val < 119
              · have hj : j = ⟨118, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 118
                  omega
                subst j
                exact namedLeaf118_checked
              · have hj : j = ⟨119, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 119
                  omega
                subst j
                exact namedLeaf119_checked
        · by_cases h124 : j.val < 124
          · by_cases h122 : j.val < 122
            · by_cases h121 : j.val < 121
              · have hj : j = ⟨120, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 120
                  omega
                subst j
                exact namedLeaf120_checked
              · have hj : j = ⟨121, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 121
                  omega
                subst j
                exact namedLeaf121_checked
            · by_cases h123 : j.val < 123
              · have hj : j = ⟨122, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 122
                  omega
                subst j
                exact namedLeaf122_checked
              · have hj : j = ⟨123, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 123
                  omega
                subst j
                exact namedLeaf123_checked
          · by_cases h126 : j.val < 126
            · by_cases h125 : j.val < 125
              · have hj : j = ⟨124, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 124
                  omega
                subst j
                exact namedLeaf124_checked
              · have hj : j = ⟨125, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 125
                  omega
                subst j
                exact namedLeaf125_checked
            · by_cases h127 : j.val < 127
              · have hj : j = ⟨126, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 126
                  omega
                subst j
                exact namedLeaf126_checked
              · have hj : j = ⟨127, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 127
                  omega
                subst j
                exact namedLeaf127_checked

theorem correct (id : Fin 24698) (hlow : 17792 ≤ id.val) (hhigh : id.val < 17920) :
    leafCheck library (N4R2WordTree.catalog id) (lookup (id.val - 17792)) = true := by
  let j : Fin 128 := ⟨id.val - 17792, by omega⟩
  have hsum : 17792 + j.val = id.val := by dsimp [j]; omega
  have hindex : Fin.ofNat 24698 (17792 + j.val) = id := by
    apply Fin.ext
    simp only [Fin.ofNat, hsum, Nat.mod_eq_of_lt id.isLt]
  have hh := point_checked j
  rw [hindex] at hh
  exact hh

#print axioms point_checked
#print axioms correct
end Jsp404.N4R2OuterLeftData.LeafShard139
