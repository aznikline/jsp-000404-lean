import Jsp000404.N4R2OuterLeftReplay
import Jsp000404.N4R2WordCatalog

set_option autoImplicit false
set_option pp.fullNames true
set_option maxRecDepth 8192
set_option maxHeartbeats 0
set_option Elab.async false

namespace Jsp404.N4R2OuterLeftData.LeafShard042
open N4R2OuterLeftReplay

-- Cycle fingerprint 005608c9a256afd1d05928eaf0a5e43183d34d27db3ebb0077bea0bda30df9a6.
def localCycle00000 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 3 5, .distance 5 6, .distance 4 5, .distance 2 5, .distance 0 2, .distance 2 4, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, 0, -1, -1, 0, -1, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false, true, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 31 2, .triangle 33 0, .triangle 34 0, .gapLower 5 2, .triangle 7 0, .triangle 6 0, .triangle 25 1, .corridorLower 2 3, .thetaLower 2]

-- Cycle fingerprint 0158166f80d85369570afd50872a03feaa3763aa1ce05ecae4231d8beeaf09ff.
def localCycle00001 : Cycle where
  length := 4
  data := {
    node := ![.distance 1 2, .distance 1 3, .distance 3 5, .distance 2 5, .distance 1 2]
    constant := ![-3, 2, 0, -1]
    coefficient := ![0, 0, 0, 0]
    strict := ![false, true, false, false] }
  origin := ![.gapLower 1 4, .gapUpper 3 5, .gapLower 5 4, .triangle 17 0]

-- Cycle fingerprint 045a47aa8a1b7663b322bf31be0bc5ba1ffc4879a5175c9666b1e9fca6760b1b.
def localCycle00002 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 4 5, .distance 0 4, .distance 0 3, .distance 3 6, .distance 4 6, .distance 2 4, .theta 4]
    constant := ![3, -1, -1, 0, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 31 0, .triangle 12 0, .triangle 9 1, .triangle 11 0, .triangle 32 1, .triangle 29 0, .gapLower 4 0]

-- Cycle fingerprint 05ebf710f335af7e71392728fa557d499ddf850bbddb7e23016be48a519b4d90.
def localCycle00003 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 2 5, .distance 1 2, .distance 0 2, .distance 2 3, .distance 3 4, .theta 3, .zero]
    constant := ![0, 3, -1, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 30 0, .triangle 17 0, .triangle 0 2, .triangle 5 0, .triangle 25 0, .corridorLower 3 4, .thetaLower 3]

-- Cycle fingerprint 069d06fc9fa503278fc4cdf4112d0e6fd6c9d73b66e5d871f6492c6801df73cc.
def localCycle00004 : Cycle where
  length := 8
  data := {
    node := ![.distance 2 3, .theta 2, .distance 2 5, .distance 1 2, .distance 1 6, .distance 1 3, .distance 0 3, .distance 3 4, .distance 2 3]
    constant := ![-1, 4, -1, 0, -2, 0, -1, -1]
    coefficient := ![0, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true, false, false] }
  origin := ![.corridorLower 2 3, .gapLower 2 6, .triangle 17 0, .triangle 18 2, .gapLower 1 3, .triangle 1 2, .triangle 9 0, .triangle 25 0]

-- Cycle fingerprint 06b74f9ff4c985cd7d77bdc6dd229f38f536a51dddbb534a0ac2133ca4796fec.
def localCycle00005 : Cycle where
  length := 6
  data := {
    node := ![.distance 1 4, .distance 4 6, .distance 3 6, .distance 2 6, .distance 1 2, .distance 1 3, .distance 1 4]
    constant := ![2, 0, 0, -1, -2, -2]
    coefficient := ![0, 0, 0, 0, 0, 0]
    strict := ![true, false, true, false, false, false] }
  origin := ![.gapUpper 4 4, .gapLower 6 5, .triangle 27 2, .triangle 18 0, .gapLower 1 3, .gapLower 1 2]

-- Cycle fingerprint 06d56a737c6ec7f1a5928e787caeec82dce0df292c7eca1e47e284836e73e51d.
def localCycle00006 : Cycle where
  length := 13
  data := {
    node := ![.distance 3 5, .distance 2 5, .distance 1 5, .distance 1 2, .distance 1 6, .distance 1 3, .distance 0 3, .distance 2 3, .distance 3 4, .theta 3, .zero, .theta 5, .distance 4 5, .distance 3 5]
    constant := ![0, 0, -2, 0, -2, 0, 0, -1, -1, 0, 0, 3, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![true, true, false, true, false, true, true, false, false, false, false, false, true] }
  origin := ![.triangle 26 2, .triangle 17 2, .gapLower 1 5, .triangle 18 2, .gapLower 1 3, .triangle 1 2, .triangle 5 1, .triangle 25 0, .corridorLower 3 4, .thetaLower 3, .thetaUpper 5, .corridorUpper 4 5, .triangle 31 2]

-- Cycle fingerprint 091d9ce7f8a84869bba9202c29c79b28d40db82d8092c1e85873d4db42e1722f.
def localCycle00007 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 1 3, .distance 3 6, .distance 2 6, .distance 2 5, .distance 0 2, .distance 2 4, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, -1, -1, 0, 0, -1, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, false, false, true, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 19 0, .triangle 21 0, .triangle 27 2, .triangle 30 1, .triangle 7 0, .triangle 6 0, .triangle 25 1, .corridorLower 2 3, .thetaLower 2]

-- Cycle fingerprint 0a67ab1cc262e3508b05b83499084f91922ab55b11422464d955f724d45b4bf4.
def localCycle00008 : Cycle where
  length := 9
  data := {
    node := ![.distance 3 4, .distance 4 6, .distance 1 4, .distance 1 3, .distance 3 5, .distance 2 5, .distance 0 2, .distance 2 4, .theta 4, .distance 3 4]
    constant := ![-1, -1, 0, -1, 0, -1, -1, 0, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![false, false, false, false, true, false, false, false, false] }
  origin := ![.triangle 32 0, .triangle 23 0, .gapLower 1 3, .triangle 20 0, .triangle 26 2, .triangle 7 0, .triangle 6 0, .gapLower 4 0, .corridorUpper 3 4]

-- Cycle fingerprint 0be961b25cc229563c6cba0056560d1842fcb7bc0b385d13f18362d915b703a1.
def localCycle00009 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 1 4, .distance 4 6, .distance 3 4, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 22 0, .triangle 23 0, .triangle 32 0, .triangle 25 0, .corridorLower 2 3, .thetaLower 2]

-- Cycle fingerprint 0c7f1a1700506d202fe54180ee112e13a08a936cfffba7520fd163e72f736439.
def localCycle00010 : Cycle where
  length := 11
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 1 2, .distance 0 2, .distance 0 3, .distance 3 4, .distance 2 4, .distance 4 6, .distance 5 6, .theta 5]
    constant := ![3, 0, 0, -1, 0, 0, -1, 0, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, true, false, true, false, true, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 17 0, .triangle 0 2, .triangle 5 2, .triangle 9 0, .triangle 25 2, .triangle 29 0, .triangle 34 1, .corridorLower 5 6]

-- Cycle fingerprint 0d9262c56835a5e1025b3d86e164e04cffd0d8e9769f22d8e1df43b83b4cc239.
def localCycle00011 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 1 2, .distance 1 3, .distance 1 6, .distance 1 4, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, 0, -1, 0, -2, 0, -2, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, true, false, true, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 17 0, .triangle 15 2, .gapLower 1 3, .triangle 23 1, .gapLower 1 1, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint 0fbd66fbf9b5db5d9ab52cb107cce6cc2f9c699c908be25237a7d96ee412c5c9.
def localCycle00012 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 4, .distance 4 5, .distance 2 5, .distance 2 6, .distance 0 2, .distance 2 4, .distance 2 3, .theta 2]
    constant := ![3, 0, -1, 0, 0, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, true, false, false, true, false] }
  origin := ![.corridorUpper 1 2, .triangle 16 2, .triangle 22 0, .triangle 28 2, .triangle 30 2, .triangle 8 0, .triangle 6 0, .triangle 25 1, .corridorLower 2 3]

-- Cycle fingerprint 1116645633dd26963bd9770d3fa368f6b6ca9b5de5c38042e02672dd8097b585.
def localCycle00013 : Cycle where
  length := 6
  data := {
    node := ![.distance 1 4, .distance 4 6, .distance 3 6, .distance 2 6, .distance 1 2, .distance 1 3, .distance 1 4]
    constant := ![2, 0, 0, -1, -2, 0]
    coefficient := ![0, 0, 0, 0, 0, 0]
    strict := ![true, false, false, false, false, true] }
  origin := ![.gapUpper 4 4, .gapLower 6 5, .gapLower 6 4, .triangle 18 0, .gapLower 1 3, .triangle 19 2]

-- Cycle fingerprint 12f4d76b21c88fbac0f2d84efa3249eaaa2e9dc9466ceb3c3cc0718e7b9a7c71.
def localCycle00014 : Cycle where
  length := 8
  data := {
    node := ![.distance 4 5, .distance 3 5, .distance 2 5, .distance 1 2, .distance 0 1, .theta 1, .zero, .theta 5, .distance 4 5]
    constant := ![0, 0, -1, -1, -3, 0, 0, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 1]
    strict := ![true, true, false, false, false, false, false, false] }
  origin := ![.triangle 31 2, .triangle 26 2, .triangle 17 0, .triangle 0 0, .gapLower 1 0, .thetaLower 1, .thetaUpper 5, .corridorUpper 4 5]

-- Cycle fingerprint 154cc6c1d9ee5b3a3ec855178f91ef67e0f4b0abb6d6e73d69d22c736cb25e2b.
def localCycle00015 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 4 5, .distance 1 4, .distance 4 6, .distance 2 6, .distance 0 2, .distance 2 4, .theta 4]
    constant := ![3, -1, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 31 0, .triangle 22 0, .triangle 23 0, .triangle 29 2, .triangle 8 0, .triangle 6 0, .gapLower 4 0]

-- Cycle fingerprint 17382abccbc61d42555fd9f220612c51bd41ab6b5db02b93acf2f942d58e4ca6.
def localCycle00016 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .theta 1, .distance 1 5, .distance 1 2, .distance 0 2, .distance 0 6, .distance 0 3, .distance 3 4, .distance 2 3, .theta 2]
    constant := ![0, 2, -2, 0, 0, 0, -1, -1, -1]
    coefficient := ![0, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![true, false, false, true, true, true, false, false, false] }
  origin := ![.thetaNext 1, .gapLower 1 6, .gapLower 1 5, .triangle 0 2, .triangle 8 2, .triangle 11 1, .triangle 9 0, .triangle 25 0, .corridorLower 2 3]

-- Cycle fingerprint 17e91a842f99d2f7dffbb993e4e76fb02f7d8456522d3df44a37b09413947723.
def localCycle00017 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 4, .distance 4 5, .distance 5 6, .distance 2 5, .distance 0 2, .distance 2 4, .distance 2 3, .theta 2]
    constant := ![3, 0, -1, -1, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false, true, false] }
  origin := ![.corridorUpper 1 2, .triangle 16 2, .triangle 22 0, .triangle 34 0, .triangle 30 0, .triangle 7 0, .triangle 6 0, .triangle 25 1, .corridorLower 2 3]

-- Cycle fingerprint 18b0baeeb6749f12b17ddab2d3dc3c66eeb599aeb2fb815bd8b8b45365b5fff8.
def localCycle00018 : Cycle where
  length := 6
  data := {
    node := ![.theta 4, .distance 3 4, .distance 4 5, .distance 1 4, .distance 4 6, .distance 2 4, .theta 4]
    constant := ![3, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 31 0, .triangle 22 0, .triangle 23 0, .triangle 29 0, .gapLower 4 0]

-- Cycle fingerprint 1bf0d5482d6bb12e2297b299bf8382d6484111c9c5e0561f52ae23cdf799bea1.
def localCycle00019 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 4, .distance 1 5, .distance 5 6, .distance 2 5, .distance 0 2, .distance 2 4, .distance 2 3, .theta 2]
    constant := ![3, 0, 0, -1, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, false, false, true, false] }
  origin := ![.corridorUpper 1 2, .triangle 16 2, .triangle 22 2, .triangle 24 0, .triangle 30 0, .triangle 7 0, .triangle 6 0, .triangle 25 1, .corridorLower 2 3]

-- Cycle fingerprint 1bfd8615c597c9f0fa8f6cc9a48c1ee86847654d9e054ce0e54dd69531079cb1.
def localCycle00020 : Cycle where
  length := 16
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 2 6, .distance 1 2, .distance 1 4, .distance 4 5, .distance 2 5, .distance 0 2, .distance 2 4, .distance 2 3, .theta 2, .theta 1, .theta 0, .zero]
    constant := ![0, 3, 0, 0, 0, -1, 0, -1, 0, -1, -1, 0, -1, 0, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, true, false, true, false, true, false, false, true, false, true, true, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 27 2, .triangle 18 0, .triangle 16 2, .triangle 22 0, .triangle 28 2, .triangle 7 0, .triangle 6 0, .triangle 25 1, .corridorLower 2 3, .thetaNext 1, .thetaNext 0, .thetaLower 0]

-- Cycle fingerprint 1ea60661b85ec42f252f73b1c35972c7765880379535b48e3efada01b8a15420.
def localCycle00021 : Cycle where
  length := 6
  data := {
    node := ![.distance 1 4, .distance 4 6, .distance 3 6, .distance 2 6, .distance 1 2, .distance 1 3, .distance 1 4]
    constant := ![2, 0, 0, -1, -3, 0]
    coefficient := ![0, 0, 0, 0, 0, 0]
    strict := ![true, false, true, false, false, true] }
  origin := ![.gapUpper 4 4, .gapLower 6 5, .triangle 27 2, .triangle 18 0, .gapLower 1 3, .triangle 19 2]

-- Cycle fingerprint 208d1d27217ea54e33f44cdd07a45884af16bebc8a325944b8ac43fb338ff154.
def localCycle00022 : Cycle where
  length := 12
  data := {
    node := ![.theta 2, .distance 1 2, .distance 2 5, .distance 0 2, .distance 2 4, .distance 2 3, .distance 3 6, .distance 4 6, .distance 5 6, .theta 5, .theta 4, .theta 3, .theta 2]
    constant := ![3, -1, -1, -1, 0, -1, 0, 0, -1, 0, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, true, true, false, true, true, true] }
  origin := ![.corridorUpper 1 2, .triangle 17 0, .triangle 7 0, .triangle 6 0, .triangle 25 1, .triangle 27 0, .triangle 32 1, .triangle 34 1, .corridorLower 5 6, .thetaNext 4, .thetaNext 3, .thetaNext 2]

-- Cycle fingerprint 21f02e089288829587da3e14cf13074016d2256dad9ea2eac915e6875ef46f1b.
def localCycle00023 : Cycle where
  length := 12
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 1 5, .distance 1 2, .distance 1 3, .distance 1 6, .distance 0 6, .distance 3 6, .distance 2 6, .distance 5 6, .theta 5]
    constant := ![3, 0, 0, 0, -2, 0, -2, 0, 0, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, true, false, true, true, true, true, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 17 2, .gapLower 1 5, .triangle 15 2, .gapLower 1 3, .triangle 4 2, .triangle 11 1, .triangle 27 2, .triangle 30 1, .corridorLower 5 6]

-- Cycle fingerprint 22769f6afa2ed47c7d734fbb8e899b1127e6ed45b4f0436dea93d4049363a679.
def localCycle00024 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 3 5, .distance 5 6, .distance 2 5, .distance 1 2, .distance 0 2, .distance 2 3, .distance 3 4, .theta 3]
    constant := ![4, -1, -1, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, false] }
  origin := ![.gapLower 3 6, .triangle 33 0, .triangle 30 0, .triangle 17 0, .triangle 0 2, .triangle 5 0, .triangle 25 0, .corridorLower 3 4]

-- Cycle fingerprint 240063ee855dd3dfe487d8debcb1797461acded74ec4f3d7681ff597fa9dddb6.
def localCycle00025 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 1 3, .distance 3 6, .distance 0 3, .distance 3 4, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, 0, -1, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 20 0, .triangle 21 0, .triangle 11 0, .triangle 9 0, .triangle 25 0, .corridorLower 2 3, .thetaLower 2]

-- Cycle fingerprint 24b430471619c9823450480b4aec52017578cb0748b312d4355116eb2ae54584.
def localCycle00026 : Cycle where
  length := 8
  data := {
    node := ![.distance 2 3, .distance 3 4, .theta 3, .theta 2, .theta 1, .distance 1 5, .distance 0 5, .distance 0 2, .distance 2 3]
    constant := ![-1, -1, 0, 0, 1, 0, 0, -1]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![false, false, true, true, false, true, true, false] }
  origin := ![.triangle 25 0, .corridorLower 3 4, .thetaNext 2, .thetaNext 1, .gapLower 1 6, .triangle 3 2, .triangle 7 1, .triangle 5 0]

-- Cycle fingerprint 28731a2a68f763e8c499580de7b25f713fbf534fd73b40a4d204a191117a2095.
def localCycle00027 : Cycle where
  length := 7
  data := {
    node := ![.theta 1, .distance 1 5, .distance 0 5, .distance 0 3, .distance 3 6, .distance 2 3, .theta 2, .theta 1]
    constant := ![1, 0, 0, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, false, true] }
  origin := ![.gapLower 1 6, .triangle 3 2, .triangle 10 1, .triangle 11 0, .triangle 27 0, .corridorLower 2 3, .thetaNext 1]

-- Cycle fingerprint 28846befb3ba2481b62a18517227615f1b2d3d717b900e1f3e4df91ec768f476.
def localCycle00028 : Cycle where
  length := 10
  data := {
    node := ![.theta 0, .zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 1 2, .distance 1 6, .distance 1 4, .distance 0 1, .theta 0]
    constant := ![0, 0, 3, 0, 0, -1, 0, 0, -3, -1]
    coefficient := ![0, 1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false, true, true, false, false] }
  origin := ![.thetaLower 0, .thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 17 0, .triangle 18 2, .triangle 23 1, .gapLower 1 1, .corridorLower 0 1]

-- Cycle fingerprint 2d2f12c3ffbfc84ed28506b06833d8afda9cb66250f190d96c39f668c1029b58.
def localCycle00029 : Cycle where
  length := 5
  data := {
    node := ![.distance 1 3, .distance 3 5, .distance 2 5, .distance 1 5, .distance 1 2, .distance 1 3]
    constant := ![2, 0, 0, -2, 0]
    coefficient := ![0, 0, 0, 0, 0]
    strict := ![true, false, true, false, true] }
  origin := ![.gapUpper 3 5, .gapLower 5 4, .triangle 17 2, .gapLower 1 5, .triangle 15 2]

-- Cycle fingerprint 2d96ed1b18808ad91ee90e9600f28afb063d31300ad9e189b3f6d2d884f47fe7.
def localCycle00030 : Cycle where
  length := 13
  data := {
    node := ![.distance 4 5, .distance 1 4, .distance 1 3, .distance 3 6, .distance 2 3, .theta 2, .distance 1 2, .distance 2 5, .distance 0 2, .distance 2 4, .distance 4 6, .theta 4, .distance 3 4, .distance 4 5]
    constant := ![-1, 0, -1, -1, -1, 3, -1, -1, -1, -1, -1, 3, -1]
    coefficient := ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0]
    strict := ![false, false, false, false, false, false, false, false, false, false, false, false, false] }
  origin := ![.triangle 22 0, .gapLower 1 3, .triangle 21 0, .triangle 27 0, .corridorLower 2 3, .corridorUpper 1 2, .triangle 17 0, .triangle 7 0, .triangle 6 0, .triangle 29 0, .corridorLower 4 6, .corridorUpper 3 4, .triangle 31 0]

-- Cycle fingerprint 2fbf59e74dadc47ae8ecf6ed7c2c1d699395fe91be01a7d55f55a67ecdb12e5b.
def localCycle00031 : Cycle where
  length := 12
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 1 5, .distance 1 6, .distance 1 2, .distance 0 2, .distance 2 3, .distance 3 4, .theta 3, .zero, .theta 5]
    constant := ![3, 0, 0, 0, -2, -2, 0, -1, -1, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, true, true, false, false, true, false, false, false, false, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 17 2, .gapLower 1 5, .gapLower 1 4, .triangle 0 2, .triangle 5 0, .triangle 25 0, .corridorLower 3 4, .thetaLower 3, .thetaUpper 5]

-- Cycle fingerprint 311469dba1ff2774978c5c4fd0960a3003046f40662538594d778c819269996b.
def localCycle00032 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 4, .distance 1 3, .distance 3 5, .distance 2 5, .distance 0 2, .distance 2 4, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, 0, -1, -1, -1, 0, -1, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, true, false, false, true, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 0, .triangle 19 0, .triangle 20 0, .triangle 26 2, .triangle 7 0, .triangle 6 0, .triangle 25 1, .corridorLower 2 3, .thetaLower 2]

-- Cycle fingerprint 31c2206412be8aafa78cbeead9f69e0a25752ac8f89e8fe08edf9d5aa5eaecd2.
def localCycle00033 : Cycle where
  length := 6
  data := {
    node := ![.theta 4, .distance 3 4, .distance 1 3, .distance 3 5, .distance 5 6, .distance 4 5, .theta 4]
    constant := ![3, -1, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 19 0, .triangle 20 0, .triangle 33 0, .triangle 34 0, .corridorLower 4 5]

-- Cycle fingerprint 329495e67ad5058bf8d9fbad8419522a5beaf48e39266d8d9a2d6c02c84f42fd.
def localCycle00034 : Cycle where
  length := 12
  data := {
    node := ![.theta 2, .distance 1 2, .distance 2 5, .distance 0 2, .distance 2 6, .distance 5 6, .theta 5, .distance 4 5, .distance 3 4, .distance 0 3, .distance 3 6, .distance 2 3, .theta 2]
    constant := ![3, -1, -1, -1, 0, -1, 3, -1, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, false, false, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 17 0, .triangle 7 0, .triangle 8 0, .triangle 30 1, .corridorLower 5 6, .corridorUpper 4 5, .triangle 31 0, .triangle 9 0, .triangle 11 0, .triangle 27 0, .corridorLower 2 3]

-- Cycle fingerprint 35171f2e3e2c23ba5d3fc819da80ab14b6848343479bd81bec6e930e6c002e71.
def localCycle00035 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 4 5, .distance 1 5, .distance 2 5, .distance 0 2, .distance 2 4, .distance 4 6, .theta 4]
    constant := ![3, -1, 0, 0, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 31 0, .gapLower 5 4, .triangle 17 1, .triangle 7 0, .triangle 6 0, .triangle 29 0, .corridorLower 4 6]

-- Cycle fingerprint 35e57b4b11d60dcd12138a2b4e44172f71183b9e974a9f4c69b251cfdccf221f.
def localCycle00036 : Cycle where
  length := 9
  data := {
    node := ![.distance 2 5, .distance 1 2, .distance 1 3, .distance 0 1, .theta 1, .zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 5]
    constant := ![-1, -2, -1, -2, 0, 0, 3, 0, 0]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, false, false, false, false, true, true] }
  origin := ![.triangle 17 0, .gapLower 1 4, .triangle 1 0, .gapLower 1 0, .thetaLower 1, .thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 2]

-- Cycle fingerprint 38486847fd41fbd915c90035089294d58e6c316d93f5c96f5118e25b0d16d403.
def localCycle00037 : Cycle where
  length := 4
  data := {
    node := ![.distance 4 6, .distance 3 6, .distance 1 3, .distance 1 4, .distance 4 6]
    constant := ![0, -1, -2, 2]
    coefficient := ![0, 0, 0, 0]
    strict := ![true, false, false, true] }
  origin := ![.triangle 32 2, .triangle 21 0, .gapLower 1 2, .gapUpper 4 4]

-- Cycle fingerprint 38f662fa8e5f39c4acd588d94485ec8b8d87cf834131b27ea9fea11f93144c99.
def localCycle00038 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 1 2, .distance 1 6, .distance 1 3, .distance 0 1, .theta 1, .zero]
    constant := ![0, 3, 0, 0, -1, 0, 0, -1, -3, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, true, true, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 17 0, .triangle 18 2, .triangle 21 1, .triangle 1 0, .gapLower 1 0, .thetaLower 1]

-- Cycle fingerprint 38f93bc1d7bbc085c928c1183bb8eaaad79838a89b95968320d867078e7e587c.
def localCycle00039 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 6, .distance 1 2, .distance 1 3, .distance 1 4, .distance 4 6, .distance 3 6, .distance 2 6, .distance 1 6]
    constant := ![-3, 0, 0, 2, 0, 0, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, false, false] }
  origin := ![.gapLower 1 4, .triangle 15 2, .triangle 19 2, .gapUpper 4 4, .gapLower 6 5, .gapLower 6 4, .gapLower 6 3]

-- Cycle fingerprint 39bfe8fc389b756d300d0aa67f879a09cd193fa61ae551b42c46310fd4971ec8.
def localCycle00040 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 1 3, .distance 1 4, .distance 4 6, .distance 3 4, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, 0, -1, 0, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 20 0, .triangle 19 2, .triangle 23 0, .triangle 32 0, .triangle 25 0, .corridorLower 2 3, .thetaLower 2]

-- Cycle fingerprint 3a18b8b65be2b0655f33d6d6fab02c4ac489fc1b7cdbb836456b66c5cd97424c.
def localCycle00041 : Cycle where
  length := 6
  data := {
    node := ![.theta 1, .zero, .theta 5, .distance 4 5, .distance 1 4, .distance 0 1, .theta 1]
    constant := ![0, 0, 3, -1, -2, -2]
    coefficient := ![0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.thetaLower 1, .thetaUpper 5, .corridorUpper 4 5, .triangle 22 0, .gapLower 1 1, .gapLower 1 0]

-- Cycle fingerprint 3ab3ebd97656ecfc6fa057b4b03aabc6695487a2db3919e2875e678f5c2296b4.
def localCycle00042 : Cycle where
  length := 12
  data := {
    node := ![.distance 2 3, .distance 3 4, .theta 3, .zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 1 2, .distance 1 6, .distance 1 3, .distance 0 3, .distance 2 3]
    constant := ![-1, -1, 0, 0, 3, 0, 0, -1, 0, -2, 0, 0]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, false, true, false, true, true] }
  origin := ![.triangle 25 0, .corridorLower 3 4, .thetaLower 3, .thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 17 0, .triangle 18 2, .gapLower 1 3, .triangle 1 2, .triangle 5 1]

-- Cycle fingerprint 3ac10ac919e4c7cd128844d3f62c602e8c9a5bdaddcaee9478a03f7f8b657c30.
def localCycle00043 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 6, .distance 1 2, .distance 1 3, .distance 1 4, .distance 4 6, .distance 3 6, .distance 2 6, .distance 1 6]
    constant := ![-2, 0, 0, 2, 0, 0, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, false, true] }
  origin := ![.gapLower 1 4, .triangle 15 2, .triangle 19 2, .gapUpper 4 4, .gapLower 6 5, .gapLower 6 4, .triangle 18 2]

-- Cycle fingerprint 3b4bb8512944e9086a6ffc562bc7c0591332854d6626c2a9386584d73667b450.
def localCycle00044 : Cycle where
  length := 14
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 4, .distance 1 4, .distance 4 5, .distance 2 5, .distance 0 2, .distance 2 4, .distance 2 3, .theta 2, .theta 1, .theta 0, .zero]
    constant := ![0, 3, 0, -1, 0, -1, 0, -1, -1, 0, -1, 0, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, true, false, false, true, false, true, true, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 0, .triangle 19 2, .triangle 22 0, .triangle 28 2, .triangle 7 0, .triangle 6 0, .triangle 25 1, .corridorLower 2 3, .thetaNext 1, .thetaNext 0, .thetaLower 0]

-- Cycle fingerprint 3c2988434f60e5999c0d47588c9a2f9a4965d252e1ef6230fabaac5b6bd5acbb.
def localCycle00045 : Cycle where
  length := 7
  data := {
    node := ![.zero, .theta 5, .distance 0 5, .distance 0 2, .distance 2 3, .distance 3 4, .theta 3, .zero]
    constant := ![0, 2, 0, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, false, false] }
  origin := ![.thetaUpper 5, .gapUpper 5 0, .triangle 7 1, .triangle 5 0, .triangle 25 0, .corridorLower 3 4, .thetaLower 3]

-- Cycle fingerprint 3e3f0e300677c458e29edec580c0387ccf06291fb56c76764cf0933f22416dd5.
def localCycle00046 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .theta 1, .distance 1 5, .distance 0 5, .distance 0 2, .distance 0 6, .distance 0 3, .distance 3 4, .distance 2 3, .theta 2]
    constant := ![0, 1, 0, 0, 0, 0, -1, -1, -1]
    coefficient := ![0, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![true, false, true, true, true, true, false, false, false] }
  origin := ![.thetaNext 1, .gapLower 1 6, .triangle 3 2, .triangle 7 1, .triangle 8 2, .triangle 11 1, .triangle 9 0, .triangle 25 0, .corridorLower 2 3]

-- Cycle fingerprint 3e7ad457b401cc337afa951f07d720964828c583dde1a5c8b647ef4be1ebe34d.
def localCycle00047 : Cycle where
  length := 8
  data := {
    node := ![.theta 2, .distance 1 2, .distance 2 5, .distance 5 6, .distance 0 5, .distance 0 2, .distance 2 4, .distance 2 3, .theta 2]
    constant := ![3, -1, -1, -1, 0, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, true, false] }
  origin := ![.corridorUpper 1 2, .triangle 17 0, .triangle 30 0, .triangle 14 0, .triangle 7 1, .triangle 6 0, .triangle 25 1, .corridorLower 2 3]

-- Cycle fingerprint 431f0f152a995af9b5761718a21f9d740fa06b1e0a66f709c1997cdc59e0834f.
def localCycle00048 : Cycle where
  length := 3
  data := {
    node := ![.distance 0 1, .theta 1, .distance 1 5, .distance 0 1]
    constant := ![-2, 2, -1]
    coefficient := ![0, 1, 0]
    strict := ![false, false, false] }
  origin := ![.gapLower 1 0, .gapLower 1 6, .triangle 3 0]

-- Cycle fingerprint 43238c2814afdabacf339b8f4efb39a98d86b8f04849bfd72d196035415ce54c.
def localCycle00049 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 4 5, .distance 3 4, .distance 4 6, .distance 5 6, .distance 1 5, .distance 2 5, .distance 0 2, .distance 2 4, .theta 4]
    constant := ![4, -1, -1, 0, -1, 0, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true, false, false, false] }
  origin := ![.gapLower 4 6, .triangle 31 0, .triangle 32 0, .triangle 34 1, .triangle 24 0, .triangle 17 1, .triangle 7 0, .triangle 6 0, .gapLower 4 0]

-- Cycle fingerprint 4534aeeda82d4997dd22d78770b80f6da4dc0efd7e9f40def56b7c81f346ee53.
def localCycle00050 : Cycle where
  length := 15
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 1 5, .distance 5 6, .distance 0 5, .distance 0 2, .distance 2 3, .distance 3 4, .theta 3, .theta 2, .theta 1, .theta 0, .zero]
    constant := ![0, 3, 0, 0, 0, -1, -1, 0, -1, -1, -1, 0, 0, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, true, false, false, true, false, false, false, true, true, true, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 17 2, .triangle 24 0, .triangle 14 0, .triangle 7 1, .triangle 5 0, .triangle 25 0, .corridorLower 3 4, .thetaNext 2, .thetaNext 1, .thetaNext 0, .thetaLower 0]

-- Cycle fingerprint 46045d2fea693f3a5d0c00c54a2fe0cded58be729706c07eb484e2c8771b868c.
def localCycle00051 : Cycle where
  length := 5
  data := {
    node := ![.distance 1 3, .distance 3 5, .distance 2 5, .distance 1 5, .distance 1 2, .distance 1 3]
    constant := ![2, 0, 0, -3, 0]
    coefficient := ![0, 0, 0, 0, 0]
    strict := ![true, false, false, false, true] }
  origin := ![.gapUpper 3 5, .gapLower 5 4, .gapLower 5 3, .gapLower 1 5, .triangle 15 2]

-- Cycle fingerprint 48514aa6dda3faf224d0cbee35ff11004c0d670fd0a854003514750b6c61c55b.
def localCycle00052 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 1 3, .distance 3 5, .distance 4 5, .distance 5 6, .distance 2 5, .distance 0 2, .distance 2 4, .theta 4]
    constant := ![3, -1, -1, 0, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 19 0, .triangle 20 0, .triangle 31 1, .triangle 34 0, .triangle 30 0, .triangle 7 0, .triangle 6 0, .gapLower 4 0]

-- Cycle fingerprint 4ba9575e8ca722304744cd6f685006e132d0d1d773c752b03096f9988955a5fc.
def localCycle00053 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 6, .distance 0 6, .distance 2 6, .distance 5 6, .theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 1 2, .distance 1 6]
    constant := ![0, 0, 0, -1, 3, 0, 0, -1, -2]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0, 0]
    strict := ![true, true, true, false, false, true, true, false, false] }
  origin := ![.triangle 4 2, .triangle 8 1, .triangle 30 1, .corridorLower 5 6, .corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 17 0, .gapLower 1 4]

-- Cycle fingerprint 4d61a8903661d74d463405b9e31e4a15b585f459ba01e8eb7f04249335f72564.
def localCycle00054 : Cycle where
  length := 14
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 4, .distance 4 5, .distance 2 5, .distance 0 2, .distance 2 6, .distance 5 6, .theta 5, .theta 4, .distance 3 4, .distance 1 3, .distance 3 6, .distance 2 3, .theta 2]
    constant := ![3, 0, -1, 0, -1, -1, 0, -1, 0, 3, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, true, false, true, false, false, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 16 2, .triangle 22 0, .triangle 28 2, .triangle 7 0, .triangle 8 0, .triangle 30 1, .corridorLower 5 6, .thetaNext 4, .corridorUpper 3 4, .triangle 19 0, .triangle 21 0, .triangle 27 0, .corridorLower 2 3]

-- Cycle fingerprint 4da31bf05da5e62affc8cb8f34b74813b312d4c54133b889b1c4d6154e1bb494.
def localCycle00055 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 1 3, .distance 3 5, .distance 2 5, .distance 0 2, .distance 2 4, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, -1, -1, 0, -1, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, true, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 19 0, .triangle 20 0, .triangle 26 2, .triangle 7 0, .triangle 6 0, .triangle 25 1, .corridorLower 2 3, .thetaLower 2]

-- Cycle fingerprint 4f68588fd573d426c8f8cc7766f2350f95251c5e481a21e1e1cbf1856eb28882.
def localCycle00056 : Cycle where
  length := 12
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 1 5, .distance 1 2, .distance 1 6, .distance 1 3, .distance 1 4, .distance 0 1, .theta 0, .zero, .theta 5]
    constant := ![3, 0, 0, 0, -2, 0, 0, 0, -2, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, true, true, false, true, true, true, false, false, false, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 17 2, .gapLower 1 5, .triangle 18 2, .triangle 21 1, .triangle 19 2, .gapLower 1 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 5]

-- Cycle fingerprint 50869eb8443b1bd9b59b2757bf2f08db36b953780a391871584f52b1d0f01e8f.
def localCycle00057 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .distance 2 3, .distance 3 4, .distance 4 6, .distance 5 6, .distance 0 5, .distance 0 2]
    constant := ![-1, -1, -1, 0, 2, 0]
    coefficient := ![0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, true] }
  origin := ![.triangle 5 0, .triangle 25 0, .triangle 32 0, .triangle 34 1, .gapUpper 5 1, .triangle 7 1]

-- Cycle fingerprint 5222c12010a7cb18308e6d25ad72b63cd450be3325d7d11294eb56b8e3524172.
def localCycle00058 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 1 2, .distance 1 6, .distance 1 4, .distance 0 1]
    constant := ![-1, 0, 0, 3, 0, 0, -1, 0, -2, -2]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, false, true, false, false] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 17 0, .triangle 18 2, .gapLower 1 2, .gapLower 1 1]

-- Cycle fingerprint 53c083aed503d7fe9a4cc4d2010892ee4c04addae3a2b2f70b9b4a33d4eda225.
def localCycle00059 : Cycle where
  length := 5
  data := {
    node := ![.distance 1 3, .distance 3 5, .distance 2 5, .distance 1 5, .distance 1 2, .distance 1 3]
    constant := ![2, 0, 0, -2, -2]
    coefficient := ![0, 0, 0, 0, 0]
    strict := ![true, false, true, false, false] }
  origin := ![.gapUpper 3 5, .gapLower 5 4, .triangle 17 2, .gapLower 1 5, .gapLower 1 4]

-- Cycle fingerprint 54ba7fa52f075cf0c583f61de0b34b2f9f210a2cdb05857cc7ba3b5c6acdeda5.
def localCycle00060 : Cycle where
  length := 9
  data := {
    node := ![.distance 2 5, .distance 1 2, .distance 1 6, .distance 0 6, .distance 2 6, .distance 5 6, .theta 5, .distance 4 5, .distance 3 5, .distance 2 5]
    constant := ![-1, -3, 0, 0, 0, -1, 3, 0, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 0, 0]
    strict := ![false, false, true, true, true, false, false, true, true] }
  origin := ![.triangle 17 0, .gapLower 1 4, .triangle 4 2, .triangle 8 1, .triangle 30 1, .corridorLower 5 6, .corridorUpper 4 5, .triangle 31 2, .triangle 26 2]

-- Cycle fingerprint 55ae4f485519d609555706de983ee37ec2ff453ea7eb87dc6c2753bf20824570.
def localCycle00061 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .theta 1, .zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 1 2, .distance 1 6, .distance 1 4, .distance 0 1]
    constant := ![-2, 0, 0, 3, 0, 0, -1, 0, -2, -1]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, false, true, false, false] }
  origin := ![.gapLower 1 0, .thetaLower 1, .thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 17 0, .triangle 18 2, .gapLower 1 2, .triangle 2 0]

-- Cycle fingerprint 5989a94c01118eccc4dfc095fcb449ea2b0829adee6d2f5515a145ae7a962a1f.
def localCycle00062 : Cycle where
  length := 5
  data := {
    node := ![.distance 1 4, .distance 4 6, .distance 3 6, .distance 1 6, .distance 1 3, .distance 1 4]
    constant := ![2, 0, 0, -3, 0]
    coefficient := ![0, 0, 0, 0, 0]
    strict := ![true, false, false, false, true] }
  origin := ![.gapUpper 4 4, .gapLower 6 5, .gapLower 6 4, .gapLower 1 3, .triangle 19 2]

-- Cycle fingerprint 5ac32f9eb172b12949a2783959c8cfe25a15479ba5329993886e5f2e6a1dcfc2.
def localCycle00063 : Cycle where
  length := 9
  data := {
    node := ![.distance 2 6, .distance 2 3, .distance 3 4, .theta 3, .theta 2, .theta 1, .distance 1 5, .distance 0 5, .distance 0 2, .distance 2 6]
    constant := ![0, -1, -1, 0, 0, 2, 0, 0, -1]
    coefficient := ![0, 0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![true, false, false, true, true, false, true, true, false] }
  origin := ![.triangle 27 1, .triangle 25 0, .corridorLower 3 4, .thetaNext 2, .thetaNext 1, .gapLower 1 6, .triangle 3 2, .triangle 7 1, .triangle 8 0]

-- Cycle fingerprint 5b1e082196d45d956e0499b463c185ec0322fac01ef6e44910bfc3a546c51031.
def localCycle00064 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 1 3, .distance 3 5, .distance 2 5, .distance 0 2, .distance 2 6, .distance 2 4, .theta 4]
    constant := ![3, -1, -1, 0, -1, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 19 0, .triangle 20 0, .triangle 26 2, .triangle 7 0, .triangle 8 0, .triangle 29 1, .gapLower 4 0]

-- Cycle fingerprint 5b967218135ac33c8c1d55c96067d6071a91717c5551088e199adb2d63f5df83.
def localCycle00065 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .theta 1, .distance 1 5, .distance 1 2, .distance 0 2, .distance 2 6, .distance 2 3, .distance 3 4, .theta 3, .theta 2]
    constant := ![0, 2, -2, 0, -1, 0, -1, -1, 0]
    coefficient := ![0, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![true, false, false, true, false, true, false, false, true] }
  origin := ![.thetaNext 1, .gapLower 1 6, .gapLower 1 5, .triangle 0 2, .triangle 8 0, .triangle 27 1, .triangle 25 0, .corridorLower 3 4, .thetaNext 2]

-- Cycle fingerprint 5c2ddbfa321042763e251e75836bb74aab7c84fcf317accf6888d4ca8e3a2292.
def localCycle00066 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 1 3, .distance 3 6, .distance 2 6, .distance 0 2, .distance 2 4, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, -1, -1, 0, -1, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, true, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 19 0, .triangle 21 0, .triangle 27 2, .triangle 8 0, .triangle 6 0, .triangle 25 1, .corridorLower 2 3, .thetaLower 2]

-- Cycle fingerprint 5ca896964e3f70182a9cd49811c227b10757cdb8ef8c4bac93f74f526a87c906.
def localCycle00067 : Cycle where
  length := 6
  data := {
    node := ![.theta 0, .zero, .theta 5, .distance 4 5, .distance 1 4, .distance 0 1, .theta 0]
    constant := ![0, 0, 3, -1, -3, -1]
    coefficient := ![0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.thetaLower 0, .thetaUpper 5, .corridorUpper 4 5, .triangle 22 0, .gapLower 1 1, .corridorLower 0 1]

-- Cycle fingerprint 5cb23b8c42af5df83a45a09b797b37c9120978a74f911afb0f5295e0b7606202.
def localCycle00068 : Cycle where
  length := 7
  data := {
    node := ![.theta 2, .distance 1 2, .distance 2 6, .distance 2 5, .distance 0 2, .distance 2 4, .distance 2 3, .theta 2]
    constant := ![3, -1, 0, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, false] }
  origin := ![.corridorUpper 1 2, .triangle 18 0, .triangle 30 1, .triangle 7 0, .triangle 6 0, .triangle 25 1, .corridorLower 2 3]

-- Cycle fingerprint 5e0907d4bb099f62912e88b17a831a411c57635d33992304da34f43a50bee105.
def localCycle00069 : Cycle where
  length := 14
  data := {
    node := ![.distance 1 5, .distance 1 2, .distance 1 3, .distance 1 6, .distance 1 4, .distance 0 4, .distance 3 4, .distance 2 3, .theta 2, .zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 1 5]
    constant := ![-2, 0, 0, -2, 0, 0, -1, -1, 0, 0, 3, 0, 0, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![false, true, true, false, true, true, false, false, false, false, false, true, true, true] }
  origin := ![.gapLower 1 5, .triangle 15 2, .triangle 21 2, .gapLower 1 2, .triangle 2 2, .triangle 9 1, .triangle 25 0, .corridorLower 2 3, .thetaLower 2, .thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 17 2]

-- Cycle fingerprint 5e29f29680339a5164dc989c89d8022feaa528ba15801bee92dcc6b4bd323934.
def localCycle00070 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 1 4, .distance 4 5, .distance 2 4, .distance 4 6, .distance 5 6, .theta 5, .theta 4]
    constant := ![3, 0, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, true, false, true] }
  origin := ![.corridorUpper 3 4, .triangle 19 2, .triangle 22 0, .triangle 28 0, .triangle 29 0, .triangle 34 1, .corridorLower 5 6, .thetaNext 4]

-- Cycle fingerprint 5e54365cdfea0e473546173cd5493532391ca51538b3b17ff9bd45e43d602c44.
def localCycle00071 : Cycle where
  length := 12
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 1 5, .distance 1 6, .distance 0 6, .distance 0 2, .distance 2 3, .distance 3 4, .theta 3, .zero, .theta 5]
    constant := ![3, 0, 0, 0, -3, 0, 0, -1, -1, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, true, true, false, true, true, false, false, false, false, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 17 2, .gapLower 1 5, .triangle 4 2, .triangle 8 1, .triangle 5 0, .triangle 25 0, .corridorLower 3 4, .thetaLower 3, .thetaUpper 5]

-- Cycle fingerprint 5f93ab30f7e3049e0fa0d7e19aaace070f871b67125ba77226deb65b4d4f708d.
def localCycle00072 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 5 6, .distance 3 5, .distance 3 4, .distance 1 3, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, -1, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 34 0, .triangle 33 0, .triangle 31 1, .triangle 19 0, .triangle 1 0, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint 5fe55bbf39c4259badb3cd86068e51220eb974cf096303fc2f46359e66bf7320.
def localCycle00073 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 4 5, .distance 1 4, .distance 4 6, .distance 5 6, .distance 2 5, .distance 0 2, .distance 2 4, .theta 4]
    constant := ![3, -1, -1, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 31 0, .triangle 22 0, .triangle 23 0, .triangle 34 1, .triangle 30 0, .triangle 7 0, .triangle 6 0, .gapLower 4 0]

-- Cycle fingerprint 602622dff3f5dc1b84416479edc249459e95c0bc7c480ea07ebfd27b71c33196.
def localCycle00074 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 4, .distance 4 6, .distance 2 6, .distance 2 5, .distance 0 2, .distance 2 4, .distance 2 3, .theta 2]
    constant := ![3, 0, -1, 0, 0, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, true, false, false, true, false] }
  origin := ![.corridorUpper 1 2, .triangle 16 2, .triangle 23 0, .triangle 29 2, .triangle 30 1, .triangle 7 0, .triangle 6 0, .triangle 25 1, .corridorLower 2 3]

-- Cycle fingerprint 622d9789ef1a687e0c3b7a22189688c42b8b4cd2ffa3a75e97fa61bbf5e81c76.
def localCycle00075 : Cycle where
  length := 11
  data := {
    node := ![.distance 2 3, .theta 2, .zero, .theta 5, .distance 4 5, .distance 3 5, .distance 1 3, .distance 1 6, .distance 1 4, .distance 0 4, .distance 3 4, .distance 2 3]
    constant := ![-1, 0, 0, 3, 0, -1, -2, -2, 0, 0, -1]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, false, true, true, false] }
  origin := ![.corridorLower 2 3, .thetaLower 2, .thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 20 0, .gapLower 1 3, .gapLower 1 2, .triangle 2 2, .triangle 9 1, .triangle 25 0]

-- Cycle fingerprint 6230d942593691bef280046360890cd1c7d369ea0b4e43fbc53264f94d3f49b2.
def localCycle00076 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 6, .distance 0 1, .theta 0, .zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 1 5, .distance 1 2, .distance 1 6]
    constant := ![-1, -1, 0, 0, 3, 0, 0, 0, -2, -2]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, true, false, false] }
  origin := ![.triangle 4 0, .corridorLower 0 1, .thetaLower 0, .thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 17 2, .gapLower 1 5, .gapLower 1 4]

-- Cycle fingerprint 654bc77373e666e7ad47376ee94bc25c438d9e9a7a580cb55c8c35227a04bb6d.
def localCycle00077 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 1 4, .distance 4 6, .distance 5 6, .distance 2 5, .distance 0 2, .distance 2 4, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, -1, -1, 0, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, false, true, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 22 0, .triangle 23 0, .triangle 34 1, .triangle 30 0, .triangle 7 0, .triangle 6 0, .triangle 25 1, .corridorLower 2 3, .thetaLower 2]

-- Cycle fingerprint 6b2b592a12da90b1a8409d0f8c65016203d7d47c37dbd08cc1b0c80003d9ce36.
def localCycle00078 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 1 3, .distance 3 6, .distance 2 3, .distance 3 4, .theta 3, .zero]
    constant := ![0, 3, 0, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 20 0, .triangle 21 0, .triangle 27 0, .triangle 25 0, .corridorLower 3 4, .thetaLower 3]

-- Cycle fingerprint 6d5d4f77a782f6d81181b67fbd85f95c813924f1ee54d0b01943fbb07dce548b.
def localCycle00079 : Cycle where
  length := 10
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 4, .distance 4 5, .distance 2 5, .distance 0 2, .distance 0 4, .distance 0 3, .distance 3 6, .distance 2 3, .theta 2]
    constant := ![3, 0, -1, 0, -1, 0, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, true, true, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 16 2, .triangle 22 0, .triangle 28 2, .triangle 7 0, .triangle 6 2, .triangle 9 1, .triangle 11 0, .triangle 27 0, .corridorLower 2 3]

-- Cycle fingerprint 6dd7c4f118e1a5b3293747b6fee6177e04caf2507ce7e7cd78b7adfec1eb93ce.
def localCycle00080 : Cycle where
  length := 9
  data := {
    node := ![.distance 2 5, .distance 1 5, .distance 1 2, .distance 1 6, .distance 0 6, .distance 0 3, .distance 3 4, .distance 2 3, .theta 2, .distance 2 5]
    constant := ![0, -2, -2, 0, 0, -1, -1, -1, 4]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![false, false, false, true, true, false, false, false, false] }
  origin := ![.gapLower 5 3, .gapLower 1 5, .gapLower 1 4, .triangle 4 2, .triangle 11 1, .triangle 9 0, .triangle 25 0, .corridorLower 2 3, .gapLower 2 6]

-- Cycle fingerprint 6f205bef44b28ea66ec0c51eff2b38daf17772e92c99104d1ffa2542b7d6edb3.
def localCycle00081 : Cycle where
  length := 12
  data := {
    node := ![.theta 2, .distance 1 2, .distance 2 5, .distance 0 2, .distance 2 6, .distance 5 6, .theta 5, .distance 4 5, .distance 3 4, .distance 1 3, .distance 3 6, .distance 2 3, .theta 2]
    constant := ![3, -1, -1, -1, 0, -1, 3, -1, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, false, false, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 17 0, .triangle 7 0, .triangle 8 0, .triangle 30 1, .corridorLower 5 6, .corridorUpper 4 5, .triangle 31 0, .triangle 19 0, .triangle 21 0, .triangle 27 0, .corridorLower 2 3]

-- Cycle fingerprint 6fdccbe3b11bb85ac2380a1d2a1a82367480590c5d2ccd5c5963281b9dffc693.
def localCycle00082 : Cycle where
  length := 10
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 0 2, .distance 2 3, .distance 2 4, .distance 4 6, .distance 3 6, .distance 5 6, .theta 5]
    constant := ![3, 0, 0, -1, -1, 0, -1, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, true, false, true, true, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 7 0, .triangle 5 0, .triangle 25 2, .triangle 29 0, .triangle 32 2, .triangle 33 1, .corridorLower 5 6]

-- Cycle fingerprint 737a2d14012170adfaaecb5b159d4254bf73e0d6f5f6ee0850df7204e68a0d91.
def localCycle00083 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 4 6, .distance 2 6, .distance 1 2, .distance 2 5, .distance 0 2, .distance 2 4, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, -1, 0, -1, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, false, true, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 32 0, .triangle 29 2, .triangle 18 0, .triangle 17 0, .triangle 7 0, .triangle 6 0, .triangle 25 1, .corridorLower 2 3, .thetaLower 2]

-- Cycle fingerprint 74094a6bdc5a3374df4bbc6b89789447143c00116c99b2fd34113ecf5b4ced97.
def localCycle00084 : Cycle where
  length := 3
  data := {
    node := ![.distance 4 6, .distance 1 6, .distance 1 4, .distance 4 6]
    constant := ![0, -3, 2]
    coefficient := ![0, 0, 0]
    strict := ![false, false, true] }
  origin := ![.gapLower 6 5, .gapLower 1 2, .gapUpper 4 4]

-- Cycle fingerprint 76335023f0c904c6f261277a59d066730548bd5d4ff74d3926a07eecba2bcb59.
def localCycle00085 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 1 2, .distance 1 6, .distance 1 3, .distance 1 4, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, 0, -1, 0, -2, -2, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, true, false, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 17 0, .triangle 18 2, .gapLower 1 3, .gapLower 1 2, .triangle 2 0, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint 766dc52885521b9765c1f1f6b8f5938036dec94cbd7c9559d4b7877fff73b4f8.
def localCycle00086 : Cycle where
  length := 8
  data := {
    node := ![.theta 2, .distance 1 2, .distance 2 5, .distance 0 2, .distance 0 4, .distance 4 6, .distance 2 4, .distance 2 3, .theta 2]
    constant := ![3, -1, -1, 0, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 17 0, .triangle 7 0, .triangle 6 2, .triangle 13 0, .triangle 29 0, .gapLower 2 1, .corridorLower 2 3]

-- Cycle fingerprint 76968d2f16f5815cb64523c9e5edb021398c5dbf47df5989d003718056a5743b.
def localCycle00087 : Cycle where
  length := 9
  data := {
    node := ![.distance 2 5, .distance 1 2, .distance 1 6, .distance 1 3, .distance 1 4, .distance 0 4, .distance 3 4, .distance 2 3, .theta 2, .distance 2 5]
    constant := ![-1, -2, 0, -2, 0, 0, -1, -1, 4]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![false, false, true, false, true, true, false, false, false] }
  origin := ![.triangle 17 0, .gapLower 1 4, .triangle 21 1, .gapLower 1 2, .triangle 2 2, .triangle 9 1, .triangle 25 0, .corridorLower 2 3, .gapLower 2 6]

-- Cycle fingerprint 7730149eb2ef3300b23bc7a15d8838bf4e256e8e5db9ece57d2cf78254274467.
def localCycle00088 : Cycle where
  length := 4
  data := {
    node := ![.distance 1 3, .distance 1 4, .distance 4 6, .distance 3 6, .distance 1 3]
    constant := ![-3, 2, 0, -1]
    coefficient := ![0, 0, 0, 0]
    strict := ![false, true, false, false] }
  origin := ![.gapLower 1 2, .gapUpper 4 4, .gapLower 6 5, .triangle 21 0]

-- Cycle fingerprint 7874815586de22c39c33f0013a9fffd8c6cb65dd8d414c97ff0e16db1b5367fb.
def localCycle00089 : Cycle where
  length := 4
  data := {
    node := ![.distance 1 2, .distance 1 3, .distance 3 5, .distance 2 5, .distance 1 2]
    constant := ![-2, 2, 0, -1]
    coefficient := ![0, 0, 0, 0]
    strict := ![false, true, false, false] }
  origin := ![.gapLower 1 4, .gapUpper 3 5, .gapLower 5 4, .triangle 17 0]

-- Cycle fingerprint 795a7905646e7d0eebe61d3318af63e5b936dfb42cf8e274ea2148e19cbc3fd1.
def localCycle00090 : Cycle where
  length := 6
  data := {
    node := ![.theta 2, .distance 1 2, .distance 2 5, .distance 0 2, .distance 2 6, .distance 2 3, .theta 2]
    constant := ![3, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false] }
  origin := ![.corridorUpper 1 2, .triangle 17 0, .triangle 7 0, .triangle 8 0, .triangle 27 1, .corridorLower 2 3]

-- Cycle fingerprint 79d22e7a4b4f72575d8924ed9f4b04a323cd63649a754e8b9219cae7ff7077aa.
def localCycle00091 : Cycle where
  length := 10
  data := {
    node := ![.distance 4 6, .distance 3 4, .distance 4 5, .distance 1 4, .distance 1 3, .distance 0 1, .theta 0, .zero, .theta 6, .distance 5 6, .distance 4 6]
    constant := ![-1, -1, -1, 0, -1, -1, 0, 0, 3, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![false, false, false, false, false, false, false, false, false, true] }
  origin := ![.triangle 32 0, .triangle 31 0, .triangle 22 0, .gapLower 1 2, .triangle 1 0, .corridorLower 0 1, .thetaLower 0, .thetaUpper 6, .corridorUpper 5 6, .triangle 34 2]

-- Cycle fingerprint 7da67067e3f866a0ded0bb1dd8906df63c38d60f1ccef5a8484ce5620ed03a3d.
def localCycle00092 : Cycle where
  length := 13
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 0 2, .distance 0 3, .distance 0 4, .distance 4 6, .distance 3 6, .distance 2 3, .distance 3 4, .theta 3, .zero]
    constant := ![0, 3, 0, 0, -1, 0, 0, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, true, true, false, true, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 7 0, .triangle 5 2, .triangle 9 2, .triangle 13 0, .triangle 32 2, .triangle 27 0, .triangle 25 0, .corridorLower 3 4, .thetaLower 3]

-- Cycle fingerprint 7ddc466313d065038d0c0dd99086a2fa090c750cd12c4b5ba7bd1221f6b1f7a3.
def localCycle00093 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 3, .distance 3 4, .distance 2 3, .distance 3 6, .distance 4 6, .distance 5 6, .distance 0 5, .distance 0 3]
    constant := ![-1, -1, -1, 0, 0, 2, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, true, true] }
  origin := ![.triangle 9 0, .triangle 25 0, .triangle 27 0, .triangle 32 1, .triangle 34 1, .gapUpper 5 1, .triangle 10 1]

-- Cycle fingerprint 7e8968f36c04a71a15de1c4a1a52ee5f696fde08458a6a3f0935b0360333c7fc.
def localCycle00094 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 0 2, .distance 0 3, .distance 3 6, .distance 2 3, .distance 3 4, .theta 3, .zero]
    constant := ![0, 3, 0, 0, -1, 0, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, true, false, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 7 0, .triangle 5 2, .triangle 11 0, .triangle 27 0, .triangle 25 0, .corridorLower 3 4, .thetaLower 3]

-- Cycle fingerprint 7f71a21734afcf5308d4646abb219f7d5c8e9bc7d3081faac1967eb7563c3cbe.
def localCycle00095 : Cycle where
  length := 3
  data := {
    node := ![.distance 2 5, .distance 1 5, .distance 1 2, .distance 2 5]
    constant := ![0, -3, 2]
    coefficient := ![0, 0, 0]
    strict := ![false, false, true] }
  origin := ![.gapLower 5 3, .gapLower 1 5, .gapUpper 2 5]

-- Cycle fingerprint 7fe9e006b5fd6dae75b2a2ff1fa9225f4be6b5eacaa80ae1988e735d37144b41.
def localCycle00096 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 3, .distance 0 1, .theta 1, .zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 1 2, .distance 1 6, .distance 1 3]
    constant := ![-1, -2, 0, 0, 3, 0, 0, -1, -2, 0]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, false, false, true] }
  origin := ![.triangle 1 0, .gapLower 1 0, .thetaLower 1, .thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 17 0, .gapLower 1 4, .triangle 21 1]

-- Cycle fingerprint 80e3d7a3d1a7b2cb2a5e7c93e79fcc83d06b8e126fc547136e1e1cd6a2bcc985.
def localCycle00097 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 0 3, .distance 0 4, .distance 4 6, .distance 3 4, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, 0, -1, 0, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 10 0, .triangle 9 2, .triangle 13 0, .triangle 32 0, .triangle 25 0, .corridorLower 2 3, .thetaLower 2]

-- Cycle fingerprint 842dd7fbc0e9b2fdaafb263455ffd671cbfb59c71a24f3bba60a3a6580b44fd0.
def localCycle00098 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 1 3, .distance 1 4, .distance 0 1, .theta 1, .zero]
    constant := ![0, 3, 0, -1, -2, -1, -2, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 20 0, .gapLower 1 2, .triangle 2 0, .gapLower 1 0, .thetaLower 1]

-- Cycle fingerprint 85e34a67cfa7f915b952fff670fb8018251f7d5587c1289f4542aaa85766d9db.
def localCycle00099 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .theta 1, .distance 1 5, .distance 0 5, .distance 0 2, .distance 0 6, .distance 0 3, .distance 3 4, .distance 2 3, .theta 2]
    constant := ![0, 2, 0, 0, 0, 0, -1, -1, -1]
    coefficient := ![0, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![true, false, true, true, true, true, false, false, false] }
  origin := ![.thetaNext 1, .gapLower 1 6, .triangle 3 2, .triangle 7 1, .triangle 8 2, .triangle 11 1, .triangle 9 0, .triangle 25 0, .corridorLower 2 3]

-- Cycle fingerprint 8806ef183cb91a48198a09b52db5348009f1b3e996cab34ebff9980c3b0505e8.
def localCycle00100 : Cycle where
  length := 9
  data := {
    node := ![.distance 2 5, .distance 1 5, .distance 1 2, .distance 1 6, .distance 1 3, .distance 0 3, .distance 3 4, .distance 2 3, .theta 2, .distance 2 5]
    constant := ![0, -2, 0, -2, 0, -1, -1, -1, 4]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![false, false, true, false, true, false, false, false, false] }
  origin := ![.gapLower 5 3, .gapLower 1 5, .triangle 18 2, .gapLower 1 3, .triangle 1 2, .triangle 9 0, .triangle 25 0, .corridorLower 2 3, .gapLower 2 6]

-- Cycle fingerprint 882cd229e462676a20d517f8ab1afb78e706d8312ef7b76d2e86011398152fa6.
def localCycle00101 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 3 4, .distance 4 5, .distance 5 6, .distance 2 5, .distance 0 2, .distance 2 4, .theta 4]
    constant := ![3, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 31 0, .triangle 34 0, .triangle 30 0, .triangle 7 0, .triangle 6 0, .gapLower 4 0]

-- Cycle fingerprint 88beaa8172bb7fa1b88207841dda8e760700cf3371689b1ccdbddb0270edf482.
def localCycle00102 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 1 2, .distance 1 6, .distance 1 4, .distance 0 1, .theta 1, .zero]
    constant := ![0, 3, 0, 0, -1, 0, 0, -1, -3, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, true, true, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 17 0, .triangle 18 2, .triangle 23 1, .triangle 2 0, .gapLower 1 0, .thetaLower 1]

-- Cycle fingerprint 89cea4d2dbe067dfa5dbddd516b5a23ac75715e0d31f1d6949b1960fd4bf7413.
def localCycle00103 : Cycle where
  length := 8
  data := {
    node := ![.distance 2 3, .distance 3 4, .theta 3, .theta 2, .theta 1, .distance 1 5, .distance 0 5, .distance 0 2, .distance 2 3]
    constant := ![-1, -1, 0, 0, 2, 0, 0, -1]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![false, false, true, true, false, true, true, false] }
  origin := ![.triangle 25 0, .corridorLower 3 4, .thetaNext 2, .thetaNext 1, .gapLower 1 6, .triangle 3 2, .triangle 7 1, .triangle 5 0]

-- Cycle fingerprint 8a2a39531e5651da9b4e7211ec8456e9c1029f0c0db46f0f9d55bde218b11bde.
def localCycle00104 : Cycle where
  length := 9
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 1 2, .distance 0 2, .distance 2 3, .distance 3 6, .distance 5 6, .theta 5]
    constant := ![3, 0, 0, -1, 0, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, false, true, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 17 0, .triangle 0 2, .triangle 5 0, .triangle 27 0, .triangle 33 1, .corridorLower 5 6]

-- Cycle fingerprint 8b3bbc96fa7b820d26b2866a09add1ed01f69e280d9ceb5e8a919094af0aacdf.
def localCycle00105 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 1 3, .distance 3 5, .distance 2 5, .distance 5 6, .distance 0 5, .distance 0 2, .distance 2 4, .theta 4]
    constant := ![3, -1, -1, 0, -1, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, true, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 19 0, .triangle 20 0, .triangle 26 2, .triangle 30 0, .triangle 14 0, .triangle 7 1, .triangle 6 0, .gapLower 4 0]

-- Cycle fingerprint 8cf9fe14cab6070e1115ba338ed52c3cbdf174781691d88a456aa3a206f9e1c2.
def localCycle00106 : Cycle where
  length := 13
  data := {
    node := ![.distance 4 5, .distance 0 4, .distance 0 3, .distance 3 6, .distance 2 3, .theta 2, .distance 1 2, .distance 2 5, .distance 0 2, .distance 2 4, .distance 4 6, .theta 4, .distance 3 4, .distance 4 5]
    constant := ![-1, 0, -1, -1, -1, 3, -1, -1, -1, -1, -1, 3, -1]
    coefficient := ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0]
    strict := ![false, false, false, false, false, false, false, false, false, false, false, false, false] }
  origin := ![.triangle 12 0, .gapLower 0 3, .triangle 11 0, .triangle 27 0, .corridorLower 2 3, .corridorUpper 1 2, .triangle 17 0, .triangle 7 0, .triangle 6 0, .triangle 29 0, .corridorLower 4 6, .corridorUpper 3 4, .triangle 31 0]

-- Cycle fingerprint 8e62e1f5d1a2929bfd4f842d68c00e247160720388a5831b8b83a8c702f1f9f4.
def localCycle00107 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 4 5, .distance 5 6, .distance 2 6, .distance 1 2, .distance 2 5, .distance 0 2, .distance 2 4, .theta 4]
    constant := ![3, -1, -1, 0, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 31 0, .triangle 34 0, .triangle 30 2, .triangle 18 0, .triangle 17 0, .triangle 7 0, .triangle 6 0, .gapLower 4 0]

-- Cycle fingerprint 91424af3322832163fdadc3061ca85ed65e08b051fce299e5f4904832e5601cf.
def localCycle00108 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .theta 1, .zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 1 2, .distance 1 6, .distance 1 3, .distance 0 1]
    constant := ![-2, 0, 0, 3, 0, 0, -1, 0, -2, -1]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, false, true, false, false] }
  origin := ![.gapLower 1 0, .thetaLower 1, .thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 17 0, .triangle 18 2, .gapLower 1 3, .triangle 1 0]

-- Cycle fingerprint 91f4b517a740dbe7a5de9fc088faa238e5ce4280ca80eb94285e2e7583c721c5.
def localCycle00109 : Cycle where
  length := 10
  data := {
    node := ![.theta 4, .distance 3 4, .distance 1 4, .distance 4 5, .distance 2 5, .distance 0 2, .distance 2 4, .distance 4 6, .distance 5 6, .theta 5, .theta 4]
    constant := ![3, 0, -1, 0, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, false, true, false, true] }
  origin := ![.corridorUpper 3 4, .triangle 19 2, .triangle 22 0, .triangle 28 2, .triangle 7 0, .triangle 6 0, .triangle 29 0, .triangle 34 1, .corridorLower 5 6, .thetaNext 4]

-- Cycle fingerprint 9376066d6f0715d29fc0cbe238758dc667557d852564e6bdb9439182319694cd.
def localCycle00110 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 0 3, .distance 3 4, .distance 4 6, .distance 2 4, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, 0, -1, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 10 0, .triangle 9 0, .triangle 32 0, .triangle 29 0, .gapLower 2 1, .corridorLower 2 3, .thetaLower 2]

-- Cycle fingerprint 948057cfd7e9e89fd1ef059a8629ca6b07c6e47f58867b2a9d2fc25db7b19b18.
def localCycle00111 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 1 2, .distance 1 6, .distance 1 3, .distance 1 4, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, 0, -1, 0, -2, 0, -2, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, true, false, true, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 17 0, .triangle 18 2, .gapLower 1 3, .triangle 19 2, .gapLower 1 1, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint 974b91c7a6de985e4641f6c6e0f09e28d0814673383fb2686d97111301a7c442.
def localCycle00112 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .theta 1, .distance 1 5, .distance 1 6, .distance 1 2, .distance 0 2, .distance 2 3, .distance 3 4, .theta 3, .theta 2]
    constant := ![0, 2, 0, -2, 0, -1, -1, -1, 0]
    coefficient := ![0, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![true, false, true, false, true, false, false, false, true] }
  origin := ![.thetaNext 1, .gapLower 1 6, .triangle 24 2, .gapLower 1 4, .triangle 0 2, .triangle 5 0, .triangle 25 0, .corridorLower 3 4, .thetaNext 2]

-- Cycle fingerprint 976d0aad275fd6477b6ab3c01ba3c98756851375da55f08c75c6ff08139b3640.
def localCycle00113 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 1 2, .distance 1 3, .distance 3 6, .distance 2 3, .distance 3 4, .theta 3, .theta 2, .zero]
    constant := ![0, 3, 0, 0, -1, 0, -1, -1, -1, -1, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, true, false, false, false, false, true, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 17 0, .triangle 15 2, .triangle 21 0, .triangle 27 0, .triangle 25 0, .corridorLower 3 4, .thetaNext 2, .thetaLower 2]

-- Cycle fingerprint 996412dc07df8f7979783a05495c790639f2858e8f89fa6d0f61af6efe778309.
def localCycle00114 : Cycle where
  length := 8
  data := {
    node := ![.distance 3 4, .distance 2 3, .theta 2, .distance 2 5, .distance 1 2, .distance 1 6, .distance 1 3, .distance 0 3, .distance 3 4]
    constant := ![-1, -1, 4, -1, -2, -2, 0, -1]
    coefficient := ![0, 0, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, false] }
  origin := ![.triangle 25 0, .corridorLower 2 3, .gapLower 2 6, .triangle 17 0, .gapLower 1 4, .gapLower 1 3, .triangle 1 2, .triangle 9 0]

-- Cycle fingerprint 9b6b1e396e370f4c1bd25476b0702f31a6f3f75b72d0726f609c090d534f803b.
def localCycle00115 : Cycle where
  length := 9
  data := {
    node := ![.distance 3 5, .distance 1 3, .distance 1 6, .distance 0 6, .distance 3 6, .distance 2 6, .distance 5 6, .theta 5, .distance 4 5, .distance 3 5]
    constant := ![-1, -3, 0, 0, 0, 0, -1, 3, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1, 0]
    strict := ![false, false, true, true, true, true, false, false, true] }
  origin := ![.triangle 20 0, .gapLower 1 3, .triangle 4 2, .triangle 11 1, .triangle 27 2, .triangle 30 1, .corridorLower 5 6, .corridorUpper 4 5, .triangle 31 2]

-- Cycle fingerprint 9c964198a83b33129112e41de50a89eeefc3063dede182ac2a9519adb29319f3.
def localCycle00116 : Cycle where
  length := 13
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 3 5, .distance 5 6, .distance 4 6, .distance 2 6, .distance 1 2, .distance 2 5, .distance 0 2, .distance 2 4, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, 0, -1, 0, 0, -1, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, true, false, false, false, false, true, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 31 2, .triangle 33 0, .triangle 34 2, .triangle 29 2, .triangle 18 0, .triangle 17 0, .triangle 7 0, .triangle 6 0, .triangle 25 1, .corridorLower 2 3, .thetaLower 2]

-- Cycle fingerprint 9e1c9f0ef3cd7e11bb1af27c16fa94c70b6d73b730530eade81247dd8df41832.
def localCycle00117 : Cycle where
  length := 13
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 4, .distance 4 6, .distance 5 6, .distance 2 6, .distance 1 2, .distance 2 5, .distance 0 2, .distance 2 4, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, -1, -1, 0, 0, -1, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, false, false, false, false, true, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 0, .triangle 32 0, .triangle 34 1, .triangle 30 2, .triangle 18 0, .triangle 17 0, .triangle 7 0, .triangle 6 0, .triangle 25 1, .corridorLower 2 3, .thetaLower 2]

-- Cycle fingerprint 9e86ec11c3544708252539ca771350edafd3322a3ecaf93b46aad6cccef95919.
def localCycle00118 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .theta 1, .distance 1 5, .distance 1 2, .distance 1 6, .distance 1 3, .distance 0 3, .distance 3 4, .distance 2 3, .theta 2]
    constant := ![0, 2, 0, 0, -2, 0, -1, -1, -1]
    coefficient := ![0, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![true, false, true, true, false, true, false, false, false] }
  origin := ![.thetaNext 1, .gapLower 1 6, .triangle 17 1, .triangle 18 2, .gapLower 1 3, .triangle 1 2, .triangle 9 0, .triangle 25 0, .corridorLower 2 3]

-- Cycle fingerprint 9fe4b280c92f24eb54e5abd7c12de2ab6544e45086b10b8680c11e7a498bd8c6.
def localCycle00119 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 5, .distance 3 4, .distance 1 3, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 0, .triangle 31 0, .triangle 19 0, .triangle 1 0, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint a2b21b8ae1aba497ffdb1c15f8e3964eb92a3da6983ea47dd6c04f137fbee8b5.
def localCycle00120 : Cycle where
  length := 12
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 1 2, .distance 1 6, .distance 0 6, .distance 0 3, .distance 3 4, .distance 2 3, .theta 2, .zero, .theta 5]
    constant := ![3, 0, 0, -1, -3, 0, 0, -1, -1, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, true, false, false, true, true, false, false, false, false, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 17 0, .gapLower 1 4, .triangle 4 2, .triangle 11 1, .triangle 9 0, .triangle 25 0, .corridorLower 2 3, .thetaLower 2, .thetaUpper 5]

-- Cycle fingerprint a7a2b3a54eb9d7340b7b3026e1085dfe27b9b4bebc60e1ecfdf0eefaf2c871a8.
def localCycle00121 : Cycle where
  length := 9
  data := {
    node := ![.distance 2 5, .distance 1 5, .distance 1 2, .distance 0 2, .distance 2 6, .distance 5 6, .theta 5, .distance 4 5, .distance 3 5, .distance 2 5]
    constant := ![0, -2, 0, -1, 0, -1, 3, 0, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 0, 0]
    strict := ![true, false, true, false, true, false, false, true, true] }
  origin := ![.triangle 17 2, .gapLower 1 5, .triangle 0 2, .triangle 8 0, .triangle 30 1, .corridorLower 5 6, .corridorUpper 4 5, .triangle 31 2, .triangle 26 2]

-- Cycle fingerprint a80d7195054f7adba5e3d4c4549e5eb46875ece6885107776858ddcb1c4f08e0.
def localCycle00122 : Cycle where
  length := 8
  data := {
    node := ![.theta 2, .distance 1 2, .distance 2 5, .distance 0 2, .distance 2 4, .distance 2 3, .distance 3 6, .theta 3, .theta 2]
    constant := ![3, -1, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, true] }
  origin := ![.corridorUpper 1 2, .triangle 17 0, .triangle 7 0, .triangle 6 0, .triangle 25 1, .triangle 27 0, .corridorLower 3 6, .thetaNext 2]

-- Cycle fingerprint a81af17a3e04e88109e12667274afdbf47ff83e1748bf59a996fd39a26b24659.
def localCycle00123 : Cycle where
  length := 7
  data := {
    node := ![.theta 2, .distance 1 2, .distance 2 5, .distance 2 6, .distance 0 2, .distance 2 4, .distance 2 3, .theta 2]
    constant := ![3, -1, 0, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, false] }
  origin := ![.corridorUpper 1 2, .triangle 17 0, .triangle 30 2, .triangle 8 0, .triangle 6 0, .triangle 25 1, .corridorLower 2 3]

-- Cycle fingerprint a8344d8541d0a117fb810c7b3da744a1851ed629ecbee0e43fa30c43a8114804.
def localCycle00124 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .theta 1, .distance 1 5, .distance 1 2, .distance 1 3, .distance 0 3, .distance 3 6, .distance 3 4, .distance 2 3, .theta 2]
    constant := ![0, 2, 0, -2, 0, -1, 0, -1, -1]
    coefficient := ![0, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![true, false, true, false, true, false, true, false, false] }
  origin := ![.thetaNext 1, .gapLower 1 6, .triangle 17 1, .gapLower 1 4, .triangle 1 2, .triangle 11 0, .triangle 32 1, .triangle 25 0, .corridorLower 2 3]

-- Cycle fingerprint a841107a34fda27fe2c4ee92a0c9c3c88a8726a4f018e565abcfb016c1cfcc6b.
def localCycle00125 : Cycle where
  length := 9
  data := {
    node := ![.distance 2 5, .distance 1 2, .distance 1 3, .distance 0 1, .theta 1, .zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 5]
    constant := ![-1, -2, -1, -2, 0, 0, 3, 0, 0]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, false, false, false, false, true, true] }
  origin := ![.triangle 17 0, .gapLower 1 3, .triangle 1 0, .gapLower 1 0, .thetaLower 1, .thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 2]

-- Cycle fingerprint aa992a3c1df8c1b874930b38e1308091bfdf3088fd7a0d405c16d8b16a8aa54b.
def localCycle00126 : Cycle where
  length := 7
  data := {
    node := ![.theta 1, .distance 1 5, .distance 0 5, .distance 0 3, .distance 3 6, .distance 2 3, .theta 2, .theta 1]
    constant := ![2, 0, 0, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, false, true] }
  origin := ![.gapLower 1 6, .triangle 3 2, .triangle 10 1, .triangle 11 0, .triangle 27 0, .corridorLower 2 3, .thetaNext 1]

-- Cycle fingerprint ac4d0a072f38e0663def90e890bf93573b3ad27b3b81e1e001d8e16c9d705731.
def localCycle00127 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 1 3, .distance 1 5, .distance 5 6, .distance 2 5, .distance 0 2, .distance 2 4, .theta 4]
    constant := ![3, -1, 0, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 19 0, .triangle 20 2, .triangle 24 0, .triangle 30 0, .triangle 7 0, .triangle 6 0, .gapLower 4 0]

-- Cycle fingerprint adc8c650003563ba294a855c14c64bcb7419aeea97af4b9e5d97970b5dc03f6d.
def localCycle00128 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 1 4, .distance 4 5, .distance 2 5, .distance 0 2, .distance 2 6, .distance 5 6, .theta 5, .theta 4]
    constant := ![3, 0, -1, 0, -1, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, true, false, true] }
  origin := ![.corridorUpper 3 4, .triangle 19 2, .triangle 22 0, .triangle 28 2, .triangle 7 0, .triangle 8 0, .triangle 30 1, .corridorLower 5 6, .thetaNext 4]

-- Cycle fingerprint adff70e09463ded8e063af2b39330f1d87acc935de77f1aba6b129356f5fbc83.
def localCycle00129 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 2, .distance 0 1, .theta 1, .zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 1 5, .distance 1 6, .distance 1 2]
    constant := ![-1, -2, 0, 0, 3, 0, 0, 0, -2, 0]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, true, false, true] }
  origin := ![.triangle 0 0, .gapLower 1 0, .thetaLower 1, .thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 17 2, .gapLower 1 5, .triangle 18 1]

-- Cycle fingerprint afda36c61c734a7a4a537164fbe3b950afffe6c6418bc45249bd36489d8d9f9f.
def localCycle00130 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 4 6, .distance 1 4, .distance 4 5, .distance 2 5, .distance 0 2, .distance 2 4, .theta 4]
    constant := ![3, -1, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 32 0, .triangle 23 0, .triangle 22 0, .triangle 28 2, .triangle 7 0, .triangle 6 0, .gapLower 4 0]

-- Cycle fingerprint b1317458d64a4baf9c5a3312d24023682fc72fd8223cc52f4ccbfc75f67acb7d.
def localCycle00131 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 4 5, .distance 5 6, .distance 3 5, .distance 2 5, .distance 1 2, .distance 0 2, .distance 2 3, .distance 3 4, .theta 4]
    constant := ![4, -1, -1, 0, -1, 0, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true, false, false, false] }
  origin := ![.gapLower 4 6, .triangle 34 0, .triangle 33 0, .triangle 26 2, .triangle 17 0, .triangle 0 2, .triangle 5 0, .triangle 25 0, .gapLower 4 0]

-- Cycle fingerprint b13e3ca157dc9975e2f6bf16ad8cb4724aaff257cc75fd092f40bf224a3562ca.
def localCycle00132 : Cycle where
  length := 8
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 4, .distance 4 5, .distance 0 4, .distance 4 6, .distance 2 4, .distance 2 3, .theta 2]
    constant := ![3, 0, -1, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 16 2, .triangle 22 0, .triangle 12 0, .triangle 13 0, .triangle 29 0, .gapLower 2 1, .corridorLower 2 3]

-- Cycle fingerprint b161608075cad7bf580348a0953d8db17d8b3ed1de01c124d51ccc1c78b4879c.
def localCycle00133 : Cycle where
  length := 13
  data := {
    node := ![.theta 2, .distance 1 2, .distance 2 5, .distance 0 2, .distance 2 4, .distance 4 6, .distance 5 6, .theta 5, .distance 4 5, .distance 3 4, .distance 0 3, .distance 3 6, .distance 2 3, .theta 2]
    constant := ![3, -1, -1, -1, -1, 0, -1, 3, -1, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, false, false, false, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 17 0, .triangle 7 0, .triangle 6 0, .triangle 29 0, .triangle 34 1, .corridorLower 5 6, .corridorUpper 4 5, .triangle 31 0, .triangle 9 0, .triangle 11 0, .triangle 27 0, .corridorLower 2 3]

-- Cycle fingerprint b22fc729e0c4c58065f8c7120d8881b3ed191ad2a31c292f3f6e63a086597100.
def localCycle00134 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .theta 1, .distance 1 5, .distance 1 6, .distance 0 6, .distance 0 2, .distance 2 3, .distance 3 4, .theta 3, .theta 2]
    constant := ![0, 2, -2, 0, 0, -1, -1, -1, 0]
    coefficient := ![0, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![true, false, false, true, true, false, false, false, true] }
  origin := ![.thetaNext 1, .gapLower 1 6, .gapLower 1 5, .triangle 4 2, .triangle 8 1, .triangle 5 0, .triangle 25 0, .corridorLower 3 4, .thetaNext 2]

-- Cycle fingerprint b7bdad8d10a1d1210895a0e2f25791f72df69813f2d1052ec1d2a8b1dd82ff7b.
def localCycle00135 : Cycle where
  length := 9
  data := {
    node := ![.distance 2 5, .distance 1 5, .distance 1 2, .distance 0 1, .theta 1, .zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 5]
    constant := ![0, -2, -1, -2, 0, 0, 3, 0, 0]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![true, false, false, false, false, false, false, true, true] }
  origin := ![.triangle 17 2, .gapLower 1 5, .triangle 0 0, .gapLower 1 0, .thetaLower 1, .thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 2]

-- Cycle fingerprint b88200b16343f5746d86e44b4512d0301f82269ba351cbf30889853bc39a97af.
def localCycle00136 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 1 4, .distance 4 6, .distance 2 6, .distance 0 2, .distance 2 4, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, -1, -1, 0, -1, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, true, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 22 0, .triangle 23 0, .triangle 29 2, .triangle 8 0, .triangle 6 0, .triangle 25 1, .corridorLower 2 3, .thetaLower 2]

-- Cycle fingerprint b9ede480aedcac050fcb5452a29f790388c20da51e102cf5b5b07b06b0bdf9b2.
def localCycle00137 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 1 2, .distance 2 6, .distance 0 2, .distance 2 3, .distance 3 4, .theta 3, .zero]
    constant := ![0, 3, 0, 0, -1, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 17 0, .triangle 18 0, .triangle 8 0, .triangle 5 0, .triangle 25 0, .corridorLower 3 4, .thetaLower 3]

-- Cycle fingerprint bb0c2b988caf45b3ba23016be3910557cee82a8dc367989404b59b8682bbe031.
def localCycle00138 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 6, .distance 1 2, .distance 1 3, .distance 1 4, .distance 4 6, .distance 3 6, .distance 2 6, .distance 1 6]
    constant := ![-2, -2, 0, 2, 0, 0, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, true] }
  origin := ![.gapLower 1 4, .gapLower 1 3, .triangle 19 2, .gapUpper 4 4, .gapLower 6 5, .gapLower 6 4, .triangle 18 2]

-- Cycle fingerprint bb6fbd9fb54945fb3ceb9c456bc69ff849b584cf04d304e3b999fa24403602bb.
def localCycle00139 : Cycle where
  length := 10
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 4, .distance 4 5, .distance 2 5, .distance 5 6, .distance 0 5, .distance 0 2, .distance 2 4, .distance 2 3, .theta 2]
    constant := ![3, 0, -1, 0, -1, -1, 0, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, true, false, true, false] }
  origin := ![.corridorUpper 1 2, .triangle 16 2, .triangle 22 0, .triangle 28 2, .triangle 30 0, .triangle 14 0, .triangle 7 1, .triangle 6 0, .triangle 25 1, .corridorLower 2 3]

-- Cycle fingerprint bd6d0d448424705a0d53456a716964ff81faf6a66b63ea29e8ed2bde0d18db1c.
def localCycle00140 : Cycle where
  length := 9
  data := {
    node := ![.distance 2 5, .distance 1 2, .distance 1 6, .distance 1 3, .distance 0 3, .distance 2 3, .distance 3 4, .theta 3, .distance 3 5, .distance 2 5]
    constant := ![-1, -2, -2, 0, 0, -1, -1, 4, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1, 0]
    strict := ![false, false, false, true, true, false, false, false, false] }
  origin := ![.triangle 17 0, .gapLower 1 4, .gapLower 1 3, .triangle 1 2, .triangle 5 1, .triangle 25 0, .corridorLower 3 4, .gapLower 3 6, .gapLower 5 4]

-- Cycle fingerprint bf9e981f3be9c2cc70f74cb9a6e6fb3f31794b4ebd637fa1206cf2ef9002eecc.
def localCycle00141 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 4, .distance 0 1, .theta 0, .zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 1 5, .distance 1 6, .distance 1 4]
    constant := ![-2, -1, 0, 0, 3, 0, 0, 0, -2, 0]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, true, false, true] }
  origin := ![.gapLower 1 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 17 2, .gapLower 1 5, .triangle 23 1]

-- Cycle fingerprint c1807434527fb5780df61aea12456c6436c7a69faa72b565fc50b5b9969cd0ef.
def localCycle00142 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 1 4, .distance 4 6, .distance 3 6, .distance 2 3, .distance 3 4, .theta 3, .zero]
    constant := ![0, 3, -1, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 22 0, .triangle 23 0, .triangle 32 2, .triangle 27 0, .triangle 25 0, .corridorLower 3 4, .thetaLower 3]

-- Cycle fingerprint c9827037260996153d4138d7f469c4bcb6eda2e90a05761b311891192e717944.
def localCycle00143 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 4, .distance 4 6, .distance 5 6, .distance 2 5, .distance 0 2, .distance 2 4, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, -1, -1, 0, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, false, true, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 0, .triangle 32 0, .triangle 34 1, .triangle 30 0, .triangle 7 0, .triangle 6 0, .triangle 25 1, .corridorLower 2 3, .thetaLower 2]

-- Cycle fingerprint ccb2762e0d8d1d6185d5f4a22d2081fdb00133f4ea8668763233848133523d05.
def localCycle00144 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 4, .distance 4 5, .distance 1 4, .distance 1 3, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, -1, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, true, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 0, .triangle 31 0, .triangle 22 0, .triangle 19 1, .triangle 1 0, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint cd2b89ab1947b4fb599ebd684fef1c759f5d46614a67db9512c3664d06b234da.
def localCycle00145 : Cycle where
  length := 11
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 1 2, .distance 1 6, .distance 1 3, .distance 1 4, .distance 0 1, .theta 1, .zero, .theta 5]
    constant := ![3, 0, 0, -1, 0, 0, -2, -1, -2, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, true, false, true, true, false, false, false, false, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 17 0, .triangle 18 2, .triangle 21 1, .gapLower 1 2, .triangle 2 0, .gapLower 1 0, .thetaLower 1, .thetaUpper 5]

-- Cycle fingerprint cec15e6823886983e9410e0eede666a8cbec9cd8826d9ec7aa9846f70b697a89.
def localCycle00146 : Cycle where
  length := 13
  data := {
    node := ![.theta 2, .distance 1 2, .distance 2 5, .distance 0 2, .distance 2 4, .distance 4 6, .distance 5 6, .theta 5, .distance 4 5, .distance 3 4, .distance 1 3, .distance 3 6, .distance 2 3, .theta 2]
    constant := ![3, -1, -1, -1, -1, 0, -1, 3, -1, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, false, false, false, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 17 0, .triangle 7 0, .triangle 6 0, .triangle 29 0, .triangle 34 1, .corridorLower 5 6, .corridorUpper 4 5, .triangle 31 0, .triangle 19 0, .triangle 21 0, .triangle 27 0, .corridorLower 2 3]

-- Cycle fingerprint d43dbfc69b4e2ed85dce24e986e9255695c33874c9753fcbc520c920e728a73a.
def localCycle00147 : Cycle where
  length := 10
  data := {
    node := ![.theta 1, .zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 1 2, .distance 1 6, .distance 1 4, .distance 0 1, .theta 1]
    constant := ![0, 0, 3, 0, 0, -1, 0, 0, -2, -2]
    coefficient := ![0, 1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false, true, true, false, false] }
  origin := ![.thetaLower 1, .thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 17 0, .triangle 18 2, .triangle 23 1, .gapLower 1 1, .gapLower 1 0]

-- Cycle fingerprint d77116ce5233ec8e5efa08051e369368298434428e819f058004c5ff30edf8c5.
def localCycle00148 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 3, .distance 3 4, .distance 2 3, .theta 2, .distance 2 5, .distance 1 2, .distance 1 6, .distance 0 6, .distance 0 3]
    constant := ![-1, -1, -1, 4, -1, -2, 0, 0]
    coefficient := ![0, 0, 0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, true] }
  origin := ![.triangle 9 0, .triangle 25 0, .corridorLower 2 3, .gapLower 2 6, .triangle 17 0, .gapLower 1 4, .triangle 4 2, .triangle 11 1]

-- Cycle fingerprint daf6a251c176425577aaed43e9670dbf6494583ea9cb37d9f61029309ee4e7c6.
def localCycle00149 : Cycle where
  length := 4
  data := {
    node := ![.distance 1 3, .distance 1 4, .distance 4 6, .distance 3 6, .distance 1 3]
    constant := ![-3, 2, 0, -1]
    coefficient := ![0, 0, 0, 0]
    strict := ![false, true, true, false] }
  origin := ![.gapLower 1 2, .gapUpper 4 4, .triangle 32 2, .triangle 21 0]

-- Cycle fingerprint db557d2021a0015a51eb79918dd0707ada3688901c26e29b34d42f5b4d8bdeff.
def localCycle00150 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 6, .distance 1 2, .distance 1 3, .distance 1 4, .distance 4 6, .distance 3 6, .distance 2 6, .distance 1 6]
    constant := ![-2, 0, -2, 2, 0, 0, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, true] }
  origin := ![.gapLower 1 4, .triangle 15 2, .gapLower 1 2, .gapUpper 4 4, .gapLower 6 5, .gapLower 6 4, .triangle 18 2]

-- Cycle fingerprint dc6e6c092bb7084010c28a30f2af97188770a03daebd90c1a1f96439b1ca639d.
def localCycle00151 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 1 3, .distance 3 6, .distance 5 6, .distance 4 5, .distance 2 5, .distance 0 2, .distance 2 4, .theta 4]
    constant := ![3, -1, -1, 0, -1, 0, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 19 0, .triangle 21 0, .triangle 33 1, .triangle 34 0, .gapLower 5 2, .triangle 7 0, .triangle 6 0, .gapLower 4 0]

-- Cycle fingerprint dcb78d66b7cff919ffbafe117b903e3622f66fc39dde06ac31a1b190eb9cbc70.
def localCycle00152 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .theta 1, .distance 1 5, .distance 1 2, .distance 0 2, .distance 0 3, .distance 3 6, .distance 3 4, .distance 2 3, .theta 2]
    constant := ![0, 2, -2, 0, 0, -1, 0, -1, -1]
    coefficient := ![0, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![true, false, false, true, true, false, true, false, false] }
  origin := ![.thetaNext 1, .gapLower 1 6, .gapLower 1 5, .triangle 0 2, .triangle 5 2, .triangle 11 0, .triangle 32 1, .triangle 25 0, .corridorLower 2 3]

-- Cycle fingerprint deb7ef2c58e2f6988ea55e89d2b9a2baf00594f5d25de0c11b0f2c7bb73823cc.
def localCycle00153 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 4 6, .distance 3 6, .distance 2 6, .distance 1 2, .distance 2 5, .distance 0 2, .distance 2 4, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, 0, 0, 0, -1, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, true, false, false, false, false, true, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 34 2, .triangle 32 2, .triangle 27 2, .triangle 18 0, .triangle 17 0, .triangle 7 0, .triangle 6 0, .triangle 25 1, .corridorLower 2 3, .thetaLower 2]

-- Cycle fingerprint e01ab1cd83be85df42c57ae816f1996fdb9d16853d9ba2d6af39caf297cde2bc.
def localCycle00154 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 4, .distance 0 1, .theta 0, .zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 1 2, .distance 1 6, .distance 1 4]
    constant := ![-2, -1, 0, 0, 3, 0, 0, -1, -2, 0]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, false, false, true] }
  origin := ![.gapLower 1 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 17 0, .gapLower 1 4, .triangle 23 1]

-- Cycle fingerprint e1731dee42e49bea2648620de756e9be8521c3f046f9554a5ca8a77c874b6ba0.
def localCycle00155 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 3 4, .distance 1 3, .distance 3 5, .distance 2 5, .distance 5 6, .theta 5, .theta 4]
    constant := ![3, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, true] }
  origin := ![.corridorUpper 3 4, .triangle 19 0, .triangle 20 0, .triangle 26 2, .triangle 30 0, .corridorLower 5 6, .thetaNext 4]

-- Cycle fingerprint e5e95cf4bb708fdc1898b9018206ad0459a5466a1454d6902bc1d722596d614f.
def localCycle00156 : Cycle where
  length := 9
  data := {
    node := ![.distance 3 4, .distance 4 6, .distance 1 4, .distance 1 3, .distance 0 1, .theta 0, .zero, .theta 5, .distance 4 5, .distance 3 4]
    constant := ![-1, -1, 0, -1, -1, 0, 0, 3, -1]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![false, false, false, false, false, false, false, false, false] }
  origin := ![.triangle 32 0, .triangle 23 0, .gapLower 1 2, .triangle 1 0, .corridorLower 0 1, .thetaLower 0, .thetaUpper 5, .corridorUpper 4 5, .triangle 31 0]

-- Cycle fingerprint e9569852329a590009ddffc418ed62a36305355aa026f617329b8ff51b795163.
def localCycle00157 : Cycle where
  length := 10
  data := {
    node := ![.theta 4, .distance 3 4, .distance 3 5, .distance 5 6, .distance 4 6, .distance 1 4, .distance 4 5, .distance 2 5, .distance 0 2, .distance 2 4, .theta 4]
    constant := ![3, 0, -1, 0, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, true, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 31 2, .triangle 33 0, .triangle 34 2, .triangle 23 0, .triangle 22 0, .triangle 28 2, .triangle 7 0, .triangle 6 0, .gapLower 4 0]

-- Cycle fingerprint e981d5c252197d9a2574b72029690c57b29217a604904740e18d85f7ff7a4cea.
def localCycle00158 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 3, .distance 0 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 3 5, .distance 5 6, .distance 4 5, .distance 1 4, .distance 1 3]
    constant := ![-1, -1, 0, 0, 3, 0, -1, -1, -1, 0]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, false, false, false] }
  origin := ![.triangle 1 0, .corridorLower 0 1, .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 31 2, .triangle 33 0, .triangle 34 0, .triangle 22 0, .gapLower 1 2]

-- Cycle fingerprint ea18f63e92504dfbe0e76877dfdbd397c1ea9ad9153be35b9772f12a3edd0b8d.
def localCycle00159 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .theta 1, .zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 1 5, .distance 1 6, .distance 1 2, .distance 0 1]
    constant := ![-2, 0, 0, 3, 0, 0, 0, 0, -2, -1]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, true, true, false, false] }
  origin := ![.gapLower 1 0, .thetaLower 1, .thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 17 2, .triangle 24 2, .gapLower 1 4, .triangle 0 0]

-- Cycle fingerprint ebc01b42dc58a8c6a7ddc9189fbb9217fee02a6317808255fe549f92420e2178.
def localCycle00160 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 4, .distance 1 3, .distance 3 6, .distance 2 6, .distance 0 2, .distance 2 4, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, -1, -1, -1, 0, -1, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, false, true, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 0, .triangle 19 0, .triangle 21 0, .triangle 27 2, .triangle 8 0, .triangle 6 0, .triangle 25 1, .corridorLower 2 3, .thetaLower 2]

-- Cycle fingerprint eef247554e78386528b8e158f3c9e82fb8923638938624dba120f59edfe15207.
def localCycle00161 : Cycle where
  length := 13
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 4, .distance 1 3, .distance 3 6, .distance 4 6, .distance 5 6, .distance 2 5, .distance 0 2, .distance 2 4, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, -1, -1, -1, 0, 0, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, false, false, false, true, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 0, .triangle 19 0, .triangle 21 0, .triangle 32 1, .triangle 34 1, .triangle 30 0, .triangle 7 0, .triangle 6 0, .triangle 25 1, .corridorLower 2 3, .thetaLower 2]

-- Cycle fingerprint f04f61890bf2990d89e72b5117b836de9a9ecc7065fa2f69e2314e5902195936.
def localCycle00162 : Cycle where
  length := 4
  data := {
    node := ![.distance 1 3, .distance 1 4, .distance 4 6, .distance 3 6, .distance 1 3]
    constant := ![-2, 2, 0, -1]
    coefficient := ![0, 0, 0, 0]
    strict := ![false, true, false, false] }
  origin := ![.gapLower 1 2, .gapUpper 4 4, .gapLower 6 5, .triangle 21 0]

-- Cycle fingerprint f131f95cabd3837880c5b2fbc7687dfdb0dd23adf17f2d1b2eae7741fa546be7.
def localCycle00163 : Cycle where
  length := 6
  data := {
    node := ![.distance 1 4, .distance 4 6, .distance 3 6, .distance 2 6, .distance 1 2, .distance 1 3, .distance 1 4]
    constant := ![2, 0, 0, -1, -2, 0]
    coefficient := ![0, 0, 0, 0, 0, 0]
    strict := ![true, false, true, false, false, true] }
  origin := ![.gapUpper 4 4, .gapLower 6 5, .triangle 27 2, .triangle 18 0, .gapLower 1 3, .triangle 19 2]

-- Cycle fingerprint f20190f75c09e174af535698ee3cab4eb7e4c1dbab5dc99e060e63f52927ca4d.
def localCycle00164 : Cycle where
  length := 8
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 5, .distance 5 6, .distance 2 5, .distance 0 2, .distance 2 4, .distance 2 3, .theta 2]
    constant := ![3, 0, -1, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, true, false] }
  origin := ![.corridorUpper 1 2, .triangle 17 2, .triangle 24 0, .triangle 30 0, .triangle 7 0, .triangle 6 0, .triangle 25 1, .corridorLower 2 3]

-- Cycle fingerprint f225191b0f76cc73d6480dd49923d336d22f436c36af2166605bb5fd1e794bdb.
def localCycle00165 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 1 3, .distance 1 4, .distance 4 6, .distance 3 6, .distance 2 3, .distance 3 4, .theta 3, .zero]
    constant := ![0, 3, 0, -1, 0, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, true, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 20 0, .triangle 19 2, .triangle 23 0, .triangle 32 2, .triangle 27 0, .triangle 25 0, .corridorLower 3 4, .thetaLower 3]

-- Cycle fingerprint fb6ed65b1e6e9345ea9c3b69d7204d3684d762083cdc93d652c2a272aa16fd4b.
def localCycle00166 : Cycle where
  length := 9
  data := {
    node := ![.distance 3 5, .distance 1 3, .distance 1 6, .distance 1 4, .distance 0 1, .theta 1, .zero, .theta 5, .distance 4 5, .distance 3 5]
    constant := ![-1, -2, 0, -1, -2, 0, 0, 3, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![false, false, true, false, false, false, false, false, true] }
  origin := ![.triangle 20 0, .gapLower 1 3, .triangle 23 1, .triangle 2 0, .gapLower 1 0, .thetaLower 1, .thetaUpper 5, .corridorUpper 4 5, .triangle 31 2]

-- Cycle fingerprint fbdc37128bf8d300755fef3f61af438a864cc23f73275e770a6bbfde5c8ee837.
def localCycle00167 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .theta 1, .distance 1 5, .distance 0 5, .distance 0 2, .distance 2 6, .distance 2 3, .distance 3 4, .theta 3, .theta 2]
    constant := ![0, 1, 0, 0, -1, 0, -1, -1, 0]
    coefficient := ![0, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![true, false, true, true, false, true, false, false, true] }
  origin := ![.thetaNext 1, .gapLower 1 6, .triangle 3 2, .triangle 7 1, .triangle 8 0, .triangle 27 1, .triangle 25 0, .corridorLower 3 4, .thetaNext 2]

-- Cycle fingerprint fc5fce1c7900f57357738a62aa2816e324ae3947c93607758c097957c640d938.
def localCycle00168 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .theta 1, .distance 1 5, .distance 1 2, .distance 1 6, .distance 1 4, .distance 0 4, .distance 3 4, .distance 2 3, .theta 2]
    constant := ![0, 2, 0, 0, -2, 0, 0, -1, -1]
    coefficient := ![0, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![true, false, true, true, false, true, true, false, false] }
  origin := ![.thetaNext 1, .gapLower 1 6, .triangle 17 1, .triangle 18 2, .gapLower 1 2, .triangle 2 2, .triangle 9 1, .triangle 25 0, .corridorLower 2 3]

-- Cycle fingerprint fcd5912c20af377c9e9beb01d81f9d56c0a49f940ea93fa5473d74f4a2339ecc.
def localCycle00169 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 6, .distance 3 6, .distance 2 3, .theta 2, .theta 1, .distance 1 5, .distance 1 3, .distance 1 6, .distance 0 6]
    constant := ![0, -1, -1, 0, 2, 0, -2, 0]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![true, false, false, true, false, true, false, true] }
  origin := ![.triangle 11 1, .triangle 27 0, .corridorLower 2 3, .thetaNext 1, .gapLower 1 6, .triangle 20 1, .gapLower 1 3, .triangle 4 2]

-- Cycle fingerprint fd4fdccf749fac173fbdf24c0cb762b2268d5acb602241239f48227f7330cb5a.
def localCycle00170 : Cycle where
  length := 13
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 5 6, .distance 1 5, .distance 2 5, .distance 0 2, .distance 2 4, .distance 2 3, .theta 2, .theta 1, .theta 0, .zero]
    constant := ![0, 3, 0, -1, -1, 0, -1, -1, 0, -1, 0, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, false, false, true, false, true, true, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 33 0, .triangle 24 0, .triangle 17 1, .triangle 7 0, .triangle 6 0, .triangle 25 1, .corridorLower 2 3, .thetaNext 1, .thetaNext 0, .thetaLower 0]

-- Cycle fingerprint fd53f3034cd1b31e0847311af00a82c077d7056e0a634ea2276378b705759956.
def localCycle00171 : Cycle where
  length := 11
  data := {
    node := ![.theta 0, .zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 1 2, .distance 1 6, .distance 1 3, .distance 1 4, .distance 0 1, .theta 0]
    constant := ![0, 0, 3, 0, 0, -1, -2, 0, -2, -1, -1]
    coefficient := ![0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false, false, true, false, false, false] }
  origin := ![.thetaLower 0, .thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 17 0, .gapLower 1 4, .triangle 21 1, .gapLower 1 2, .triangle 2 0, .corridorLower 0 1]

-- Cycle fingerprint fe4a0dd61b1a07f49cc06b1a4a9214570aa8ab6f6d2a3a8a90f1045144d59df0.
def localCycle00172 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 5 6, .distance 2 6, .distance 1 2, .distance 2 5, .distance 0 2, .distance 2 4, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, 0, -1, 0, -1, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false, false, false, true, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 33 0, .triangle 30 2, .triangle 18 0, .triangle 17 0, .triangle 7 0, .triangle 6 0, .triangle 25 1, .corridorLower 2 3, .thetaLower 2]

def library : Library := fun id => if id < 86 then (if id < 43 then (if id < 21 then (if id < 10 then (if id < 5 then (if id < 2 then (if id < 1 then (if id = 0 then some localCycle00000 else none) else (if id = 1 then some localCycle00001 else none)) else (if id < 3 then (if id = 2 then some localCycle00002 else none) else (if id < 4 then (if id = 3 then some localCycle00003 else none) else (if id = 4 then some localCycle00004 else none)))) else (if id < 7 then (if id < 6 then (if id = 5 then some localCycle00005 else none) else (if id = 6 then some localCycle00006 else none)) else (if id < 8 then (if id = 7 then some localCycle00007 else none) else (if id < 9 then (if id = 8 then some localCycle00008 else none) else (if id = 9 then some localCycle00009 else none))))) else (if id < 15 then (if id < 12 then (if id < 11 then (if id = 10 then some localCycle00010 else none) else (if id = 11 then some localCycle00011 else none)) else (if id < 13 then (if id = 12 then some localCycle00012 else none) else (if id < 14 then (if id = 13 then some localCycle00013 else none) else (if id = 14 then some localCycle00014 else none)))) else (if id < 18 then (if id < 16 then (if id = 15 then some localCycle00015 else none) else (if id < 17 then (if id = 16 then some localCycle00016 else none) else (if id = 17 then some localCycle00017 else none))) else (if id < 19 then (if id = 18 then some localCycle00018 else none) else (if id < 20 then (if id = 19 then some localCycle00019 else none) else (if id = 20 then some localCycle00020 else none)))))) else (if id < 32 then (if id < 26 then (if id < 23 then (if id < 22 then (if id = 21 then some localCycle00021 else none) else (if id = 22 then some localCycle00022 else none)) else (if id < 24 then (if id = 23 then some localCycle00023 else none) else (if id < 25 then (if id = 24 then some localCycle00024 else none) else (if id = 25 then some localCycle00025 else none)))) else (if id < 29 then (if id < 27 then (if id = 26 then some localCycle00026 else none) else (if id < 28 then (if id = 27 then some localCycle00027 else none) else (if id = 28 then some localCycle00028 else none))) else (if id < 30 then (if id = 29 then some localCycle00029 else none) else (if id < 31 then (if id = 30 then some localCycle00030 else none) else (if id = 31 then some localCycle00031 else none))))) else (if id < 37 then (if id < 34 then (if id < 33 then (if id = 32 then some localCycle00032 else none) else (if id = 33 then some localCycle00033 else none)) else (if id < 35 then (if id = 34 then some localCycle00034 else none) else (if id < 36 then (if id = 35 then some localCycle00035 else none) else (if id = 36 then some localCycle00036 else none)))) else (if id < 40 then (if id < 38 then (if id = 37 then some localCycle00037 else none) else (if id < 39 then (if id = 38 then some localCycle00038 else none) else (if id = 39 then some localCycle00039 else none))) else (if id < 41 then (if id = 40 then some localCycle00040 else none) else (if id < 42 then (if id = 41 then some localCycle00041 else none) else (if id = 42 then some localCycle00042 else none))))))) else (if id < 64 then (if id < 53 then (if id < 48 then (if id < 45 then (if id < 44 then (if id = 43 then some localCycle00043 else none) else (if id = 44 then some localCycle00044 else none)) else (if id < 46 then (if id = 45 then some localCycle00045 else none) else (if id < 47 then (if id = 46 then some localCycle00046 else none) else (if id = 47 then some localCycle00047 else none)))) else (if id < 50 then (if id < 49 then (if id = 48 then some localCycle00048 else none) else (if id = 49 then some localCycle00049 else none)) else (if id < 51 then (if id = 50 then some localCycle00050 else none) else (if id < 52 then (if id = 51 then some localCycle00051 else none) else (if id = 52 then some localCycle00052 else none))))) else (if id < 58 then (if id < 55 then (if id < 54 then (if id = 53 then some localCycle00053 else none) else (if id = 54 then some localCycle00054 else none)) else (if id < 56 then (if id = 55 then some localCycle00055 else none) else (if id < 57 then (if id = 56 then some localCycle00056 else none) else (if id = 57 then some localCycle00057 else none)))) else (if id < 61 then (if id < 59 then (if id = 58 then some localCycle00058 else none) else (if id < 60 then (if id = 59 then some localCycle00059 else none) else (if id = 60 then some localCycle00060 else none))) else (if id < 62 then (if id = 61 then some localCycle00061 else none) else (if id < 63 then (if id = 62 then some localCycle00062 else none) else (if id = 63 then some localCycle00063 else none)))))) else (if id < 75 then (if id < 69 then (if id < 66 then (if id < 65 then (if id = 64 then some localCycle00064 else none) else (if id = 65 then some localCycle00065 else none)) else (if id < 67 then (if id = 66 then some localCycle00066 else none) else (if id < 68 then (if id = 67 then some localCycle00067 else none) else (if id = 68 then some localCycle00068 else none)))) else (if id < 72 then (if id < 70 then (if id = 69 then some localCycle00069 else none) else (if id < 71 then (if id = 70 then some localCycle00070 else none) else (if id = 71 then some localCycle00071 else none))) else (if id < 73 then (if id = 72 then some localCycle00072 else none) else (if id < 74 then (if id = 73 then some localCycle00073 else none) else (if id = 74 then some localCycle00074 else none))))) else (if id < 80 then (if id < 77 then (if id < 76 then (if id = 75 then some localCycle00075 else none) else (if id = 76 then some localCycle00076 else none)) else (if id < 78 then (if id = 77 then some localCycle00077 else none) else (if id < 79 then (if id = 78 then some localCycle00078 else none) else (if id = 79 then some localCycle00079 else none)))) else (if id < 83 then (if id < 81 then (if id = 80 then some localCycle00080 else none) else (if id < 82 then (if id = 81 then some localCycle00081 else none) else (if id = 82 then some localCycle00082 else none))) else (if id < 84 then (if id = 83 then some localCycle00083 else none) else (if id < 85 then (if id = 84 then some localCycle00084 else none) else (if id = 85 then some localCycle00085 else none)))))))) else (if id < 129 then (if id < 107 then (if id < 96 then (if id < 91 then (if id < 88 then (if id < 87 then (if id = 86 then some localCycle00086 else none) else (if id = 87 then some localCycle00087 else none)) else (if id < 89 then (if id = 88 then some localCycle00088 else none) else (if id < 90 then (if id = 89 then some localCycle00089 else none) else (if id = 90 then some localCycle00090 else none)))) else (if id < 93 then (if id < 92 then (if id = 91 then some localCycle00091 else none) else (if id = 92 then some localCycle00092 else none)) else (if id < 94 then (if id = 93 then some localCycle00093 else none) else (if id < 95 then (if id = 94 then some localCycle00094 else none) else (if id = 95 then some localCycle00095 else none))))) else (if id < 101 then (if id < 98 then (if id < 97 then (if id = 96 then some localCycle00096 else none) else (if id = 97 then some localCycle00097 else none)) else (if id < 99 then (if id = 98 then some localCycle00098 else none) else (if id < 100 then (if id = 99 then some localCycle00099 else none) else (if id = 100 then some localCycle00100 else none)))) else (if id < 104 then (if id < 102 then (if id = 101 then some localCycle00101 else none) else (if id < 103 then (if id = 102 then some localCycle00102 else none) else (if id = 103 then some localCycle00103 else none))) else (if id < 105 then (if id = 104 then some localCycle00104 else none) else (if id < 106 then (if id = 105 then some localCycle00105 else none) else (if id = 106 then some localCycle00106 else none)))))) else (if id < 118 then (if id < 112 then (if id < 109 then (if id < 108 then (if id = 107 then some localCycle00107 else none) else (if id = 108 then some localCycle00108 else none)) else (if id < 110 then (if id = 109 then some localCycle00109 else none) else (if id < 111 then (if id = 110 then some localCycle00110 else none) else (if id = 111 then some localCycle00111 else none)))) else (if id < 115 then (if id < 113 then (if id = 112 then some localCycle00112 else none) else (if id < 114 then (if id = 113 then some localCycle00113 else none) else (if id = 114 then some localCycle00114 else none))) else (if id < 116 then (if id = 115 then some localCycle00115 else none) else (if id < 117 then (if id = 116 then some localCycle00116 else none) else (if id = 117 then some localCycle00117 else none))))) else (if id < 123 then (if id < 120 then (if id < 119 then (if id = 118 then some localCycle00118 else none) else (if id = 119 then some localCycle00119 else none)) else (if id < 121 then (if id = 120 then some localCycle00120 else none) else (if id < 122 then (if id = 121 then some localCycle00121 else none) else (if id = 122 then some localCycle00122 else none)))) else (if id < 126 then (if id < 124 then (if id = 123 then some localCycle00123 else none) else (if id < 125 then (if id = 124 then some localCycle00124 else none) else (if id = 125 then some localCycle00125 else none))) else (if id < 127 then (if id = 126 then some localCycle00126 else none) else (if id < 128 then (if id = 127 then some localCycle00127 else none) else (if id = 128 then some localCycle00128 else none))))))) else (if id < 151 then (if id < 140 then (if id < 134 then (if id < 131 then (if id < 130 then (if id = 129 then some localCycle00129 else none) else (if id = 130 then some localCycle00130 else none)) else (if id < 132 then (if id = 131 then some localCycle00131 else none) else (if id < 133 then (if id = 132 then some localCycle00132 else none) else (if id = 133 then some localCycle00133 else none)))) else (if id < 137 then (if id < 135 then (if id = 134 then some localCycle00134 else none) else (if id < 136 then (if id = 135 then some localCycle00135 else none) else (if id = 136 then some localCycle00136 else none))) else (if id < 138 then (if id = 137 then some localCycle00137 else none) else (if id < 139 then (if id = 138 then some localCycle00138 else none) else (if id = 139 then some localCycle00139 else none))))) else (if id < 145 then (if id < 142 then (if id < 141 then (if id = 140 then some localCycle00140 else none) else (if id = 141 then some localCycle00141 else none)) else (if id < 143 then (if id = 142 then some localCycle00142 else none) else (if id < 144 then (if id = 143 then some localCycle00143 else none) else (if id = 144 then some localCycle00144 else none)))) else (if id < 148 then (if id < 146 then (if id = 145 then some localCycle00145 else none) else (if id < 147 then (if id = 146 then some localCycle00146 else none) else (if id = 147 then some localCycle00147 else none))) else (if id < 149 then (if id = 148 then some localCycle00148 else none) else (if id < 150 then (if id = 149 then some localCycle00149 else none) else (if id = 150 then some localCycle00150 else none)))))) else (if id < 162 then (if id < 156 then (if id < 153 then (if id < 152 then (if id = 151 then some localCycle00151 else none) else (if id = 152 then some localCycle00152 else none)) else (if id < 154 then (if id = 153 then some localCycle00153 else none) else (if id < 155 then (if id = 154 then some localCycle00154 else none) else (if id = 155 then some localCycle00155 else none)))) else (if id < 159 then (if id < 157 then (if id = 156 then some localCycle00156 else none) else (if id < 158 then (if id = 157 then some localCycle00157 else none) else (if id = 158 then some localCycle00158 else none))) else (if id < 160 then (if id = 159 then some localCycle00159 else none) else (if id < 161 then (if id = 160 then some localCycle00160 else none) else (if id = 161 then some localCycle00161 else none))))) else (if id < 167 then (if id < 164 then (if id < 163 then (if id = 162 then some localCycle00162 else none) else (if id = 163 then some localCycle00163 else none)) else (if id < 165 then (if id = 164 then some localCycle00164 else none) else (if id < 166 then (if id = 165 then some localCycle00165 else none) else (if id = 166 then some localCycle00166 else none)))) else (if id < 170 then (if id < 168 then (if id = 167 then some localCycle00167 else none) else (if id < 169 then (if id = 168 then some localCycle00168 else none) else (if id = 169 then some localCycle00169 else none))) else (if id < 171 then (if id = 170 then some localCycle00170 else none) else (if id < 172 then (if id = 171 then some localCycle00171 else none) else (if id = 172 then some localCycle00172 else none))))))))

def namedLeaf000 : LeafData := { rows := ![![1, 4, 3, 2, 6, 5], ![0, 6, 4, 3, 2, 5], ![3, 4, 0, 6, 1, 5], ![2, 4, 0, 6, 1, 5], ![2, 3, 0, 6, 1, 5], ![6, 0, 1, 2, 3, 4], ![5, 0, 2, 3, 4, 1]], proof := .tail 9 }

theorem namedLeaf000_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5376)) namedLeaf000 = true :=
  by decide +kernel

def namedLeaf001 : LeafData := { rows := ![![1, 4, 3, 6, 2, 5], ![0, 4, 3, 6, 2, 5], ![3, 4, 6, 0, 1, 5], ![2, 4, 0, 1, 6, 5], ![2, 3, 0, 1, 6, 5], ![6, 0, 1, 2, 3, 4], ![5, 2, 0, 1, 3, 4]], proof := .low (![38, 28, 149, 62, 120, 95, 46, 147, 145, 108, 96, 135, 48, 162, 4, 154, 121, 99, 4, 87, 162, 37, 114, 100, 118, 80, 148, 16]) }

theorem namedLeaf001_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5377)) namedLeaf001 = true :=
  by decide +kernel

def namedLeaf002 : LeafData := { rows := ![![1, 4, 3, 6, 2, 5], ![0, 4, 6, 3, 2, 5], ![3, 4, 6, 0, 1, 5], ![2, 4, 0, 6, 1, 5], ![2, 3, 0, 1, 6, 5], ![6, 0, 1, 2, 3, 4], ![5, 2, 0, 3, 1, 4]], proof := .tail 25 }

theorem namedLeaf002_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5378)) namedLeaf002 = true :=
  by decide +kernel

def namedLeaf003 : LeafData := { rows := ![![1, 4, 3, 6, 2, 5], ![0, 6, 4, 3, 2, 5], ![3, 4, 6, 0, 1, 5], ![2, 4, 0, 6, 1, 5], ![2, 3, 0, 6, 1, 5], ![6, 0, 1, 2, 3, 4], ![5, 2, 0, 3, 4, 1]], proof := .tail 9 }

theorem namedLeaf003_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5379)) namedLeaf003 = true :=
  by decide +kernel

def namedLeaf004 : LeafData := { rows := ![![1, 4, 6, 3, 2, 5], ![0, 4, 6, 3, 2, 5], ![3, 4, 6, 0, 1, 5], ![2, 4, 6, 0, 1, 5], ![2, 3, 0, 1, 6, 5], ![6, 0, 1, 2, 3, 4], ![5, 2, 3, 0, 1, 4]], proof := .low (![102, 28, 84, 115, 1, 51, 27, 147, 61, 166, 36, 135, 48, 58, 11, 89, 29, 126, 75, 89, 69, 168, 89, 23, 169, 59, 124, 152]) }

theorem namedLeaf004_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5380)) namedLeaf004 = true :=
  by decide +kernel

def namedLeaf005 : LeafData := { rows := ![![1, 4, 6, 3, 2, 5], ![0, 6, 4, 3, 2, 5], ![3, 4, 6, 0, 1, 5], ![2, 4, 6, 0, 1, 5], ![2, 3, 0, 6, 1, 5], ![6, 0, 1, 2, 3, 4], ![5, 2, 3, 0, 4, 1]], proof := .tail 40 }

theorem namedLeaf005_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5381)) namedLeaf005 = true :=
  by decide +kernel

def namedLeaf006 : LeafData := { rows := ![![1, 6, 4, 3, 2, 5], ![0, 6, 4, 3, 2, 5], ![3, 4, 6, 0, 1, 5], ![2, 4, 6, 0, 1, 5], ![2, 3, 6, 0, 1, 5], ![6, 0, 1, 2, 3, 4], ![5, 2, 3, 4, 0, 1]], proof := .tail 97 }

theorem namedLeaf006_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5382)) namedLeaf006 = true :=
  by decide +kernel

def namedLeaf007 : LeafData := { rows := ![![1, 6, 4, 3, 2, 5], ![0, 6, 4, 3, 2, 5], ![3, 4, 6, 0, 1, 5], ![2, 6, 4, 0, 1, 5], ![2, 6, 3, 0, 1, 5], ![6, 0, 1, 2, 3, 4], ![5, 2, 4, 3, 0, 1]], proof := .tail 110 }

theorem namedLeaf007_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5383)) namedLeaf007 = true :=
  by decide +kernel

def namedLeaf008 : LeafData := { rows := ![![1, 6, 4, 3, 2, 5], ![0, 6, 4, 3, 2, 5], ![3, 6, 4, 0, 1, 5], ![2, 6, 4, 0, 1, 5], ![6, 2, 3, 0, 1, 5], ![6, 0, 1, 2, 3, 4], ![5, 4, 2, 3, 0, 1]], proof := .tail 10 }

theorem namedLeaf008_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5384)) namedLeaf008 = true :=
  by decide +kernel

def namedLeaf009 : LeafData := { rows := ![![1, 6, 4, 3, 2, 5], ![0, 6, 4, 3, 2, 5], ![6, 3, 4, 0, 1, 5], ![6, 2, 4, 0, 1, 5], ![6, 2, 3, 0, 1, 5], ![6, 0, 1, 2, 3, 4], ![5, 4, 3, 2, 0, 1]], proof := .tail 93 }

theorem namedLeaf009_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5385)) namedLeaf009 = true :=
  by decide +kernel

def namedLeaf010 : LeafData := { rows := ![![1, 4, 3, 2, 5, 6], ![0, 4, 3, 2, 5, 6], ![4, 3, 0, 1, 5, 6], ![4, 2, 0, 1, 5, 6], ![3, 2, 0, 1, 5, 6], ![0, 1, 2, 3, 4, 6], ![0, 1, 2, 3, 4, 5]], proof := .tail 3 }

theorem namedLeaf010_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5386)) namedLeaf010 = true :=
  by decide +kernel

def namedLeaf011 : LeafData := { rows := ![![1, 4, 3, 2, 5, 6], ![0, 4, 3, 2, 5, 6], ![4, 3, 0, 1, 5, 6], ![4, 2, 0, 1, 5, 6], ![3, 2, 0, 1, 6, 5], ![0, 1, 2, 3, 6, 4], ![0, 1, 2, 3, 5, 4]], proof := .tail 131 }

theorem namedLeaf011_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5387)) namedLeaf011 = true :=
  by decide +kernel

def namedLeaf012 : LeafData := { rows := ![![1, 4, 3, 2, 5, 6], ![0, 4, 3, 2, 5, 6], ![4, 3, 0, 1, 5, 6], ![4, 2, 0, 1, 6, 5], ![3, 2, 0, 1, 6, 5], ![0, 1, 2, 6, 3, 4], ![0, 1, 2, 5, 3, 4]], proof := .tail 24 }

theorem namedLeaf012_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5388)) namedLeaf012 = true :=
  by decide +kernel

def namedLeaf013 : LeafData := { rows := ![![1, 4, 3, 2, 5, 6], ![0, 4, 3, 2, 5, 6], ![4, 3, 0, 1, 6, 5], ![4, 2, 0, 1, 6, 5], ![3, 2, 0, 1, 6, 5], ![0, 1, 6, 2, 3, 4], ![0, 1, 5, 2, 3, 4]], proof := .tail 45 }

theorem namedLeaf013_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5389)) namedLeaf013 = true :=
  by decide +kernel

def namedLeaf014 : LeafData := { rows := ![![1, 4, 3, 2, 5, 6], ![0, 4, 3, 2, 6, 5], ![4, 3, 0, 1, 6, 5], ![4, 2, 0, 1, 6, 5], ![3, 2, 0, 1, 6, 5], ![0, 6, 1, 2, 3, 4], ![0, 5, 1, 2, 3, 4]], proof := .tail 50 }

theorem namedLeaf014_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5390)) namedLeaf014 = true :=
  by decide +kernel

def namedLeaf015 : LeafData := { rows := ![![1, 4, 3, 2, 5, 6], ![0, 4, 3, 6, 2, 5], ![4, 3, 0, 6, 1, 5], ![4, 2, 0, 1, 6, 5], ![3, 2, 0, 1, 6, 5], ![0, 6, 1, 2, 3, 4], ![0, 5, 2, 1, 3, 4]], proof := .tail 137 }

theorem namedLeaf015_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5391)) namedLeaf015 = true :=
  by decide +kernel

def namedLeaf016 : LeafData := { rows := ![![1, 4, 3, 2, 5, 6], ![0, 4, 6, 3, 2, 5], ![4, 3, 0, 6, 1, 5], ![4, 2, 0, 6, 1, 5], ![3, 2, 0, 1, 6, 5], ![0, 6, 1, 2, 3, 4], ![0, 5, 2, 3, 1, 4]], proof := .tail 78 }

theorem namedLeaf016_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5392)) namedLeaf016 = true :=
  by decide +kernel

def namedLeaf017 : LeafData := { rows := ![![1, 4, 3, 2, 5, 6], ![0, 6, 4, 3, 2, 5], ![4, 3, 0, 6, 1, 5], ![4, 2, 0, 6, 1, 5], ![3, 2, 0, 6, 1, 5], ![0, 6, 1, 2, 3, 4], ![0, 5, 2, 3, 4, 1]], proof := .tail 142 }

theorem namedLeaf017_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5393)) namedLeaf017 = true :=
  by decide +kernel

def namedLeaf018 : LeafData := { rows := ![![1, 4, 3, 2, 6, 5], ![0, 4, 3, 2, 6, 5], ![4, 3, 0, 1, 6, 5], ![4, 2, 0, 1, 6, 5], ![3, 2, 0, 1, 6, 5], ![6, 0, 1, 2, 3, 4], ![5, 0, 1, 2, 3, 4]], proof := .low (![14, 67, 88, 21, 39, 71, 26, 41, 98, 125, 159, 129, 48, 162, 13, 43, 141, 103, 5, 150, 162, 162, 138, 13, 163, 31, 112, 134]) }

theorem namedLeaf018_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5394)) namedLeaf018 = true :=
  by decide +kernel

def namedLeaf019 : LeafData := { rows := ![![1, 4, 3, 2, 6, 5], ![0, 4, 3, 6, 2, 5], ![4, 3, 0, 6, 1, 5], ![4, 2, 0, 1, 6, 5], ![3, 2, 0, 1, 6, 5], ![6, 0, 1, 2, 3, 4], ![5, 0, 2, 1, 3, 4]], proof := .tail 137 }

theorem namedLeaf019_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5395)) namedLeaf019 = true :=
  by decide +kernel

def namedLeaf020 : LeafData := { rows := ![![1, 4, 3, 2, 6, 5], ![0, 4, 6, 3, 2, 5], ![4, 3, 0, 6, 1, 5], ![4, 2, 0, 6, 1, 5], ![3, 2, 0, 1, 6, 5], ![6, 0, 1, 2, 3, 4], ![5, 0, 2, 3, 1, 4]], proof := .tail 78 }

theorem namedLeaf020_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5396)) namedLeaf020 = true :=
  by decide +kernel

def namedLeaf021 : LeafData := { rows := ![![1, 4, 3, 2, 6, 5], ![0, 6, 4, 3, 2, 5], ![4, 3, 0, 6, 1, 5], ![4, 2, 0, 6, 1, 5], ![3, 2, 0, 6, 1, 5], ![6, 0, 1, 2, 3, 4], ![5, 0, 2, 3, 4, 1]], proof := .tail 142 }

theorem namedLeaf021_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5397)) namedLeaf021 = true :=
  by decide +kernel

def namedLeaf022 : LeafData := { rows := ![![1, 4, 3, 6, 2, 5], ![0, 4, 3, 6, 2, 5], ![4, 3, 6, 0, 1, 5], ![4, 2, 0, 1, 6, 5], ![3, 2, 0, 1, 6, 5], ![6, 0, 1, 2, 3, 4], ![5, 2, 0, 1, 3, 4]], proof := .low (![38, 28, 149, 62, 60, 95, 167, 147, 145, 108, 96, 135, 48, 162, 111, 154, 56, 63, 85, 171, 162, 37, 140, 6, 42, 76, 53, 65]) }

theorem namedLeaf022_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5398)) namedLeaf022 = true :=
  by decide +kernel

def namedLeaf023 : LeafData := { rows := ![![1, 4, 3, 6, 2, 5], ![0, 4, 6, 3, 2, 5], ![4, 3, 6, 0, 1, 5], ![4, 2, 0, 6, 1, 5], ![3, 2, 0, 1, 6, 5], ![6, 0, 1, 2, 3, 4], ![5, 2, 0, 3, 1, 4]], proof := .tail 113 }

theorem namedLeaf023_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5399)) namedLeaf023 = true :=
  by decide +kernel

def namedLeaf024 : LeafData := { rows := ![![1, 4, 3, 6, 2, 5], ![0, 6, 4, 3, 2, 5], ![4, 3, 6, 0, 1, 5], ![4, 2, 0, 6, 1, 5], ![3, 2, 0, 6, 1, 5], ![6, 0, 1, 2, 3, 4], ![5, 2, 0, 3, 4, 1]], proof := .tail 165 }

theorem namedLeaf024_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5400)) namedLeaf024 = true :=
  by decide +kernel

def namedLeaf025 : LeafData := { rows := ![![1, 4, 6, 3, 2, 5], ![0, 4, 6, 3, 2, 5], ![4, 3, 6, 0, 1, 5], ![4, 2, 6, 0, 1, 5], ![3, 2, 0, 1, 6, 5], ![6, 0, 1, 2, 3, 4], ![5, 2, 3, 0, 1, 4]], proof := .tail 94 }

theorem namedLeaf025_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5401)) namedLeaf025 = true :=
  by decide +kernel

def namedLeaf026 : LeafData := { rows := ![![1, 4, 6, 3, 2, 5], ![0, 6, 4, 3, 2, 5], ![4, 3, 6, 0, 1, 5], ![4, 2, 6, 0, 1, 5], ![3, 2, 0, 6, 1, 5], ![6, 0, 1, 2, 3, 4], ![5, 2, 3, 0, 4, 1]], proof := .tail 165 }

theorem namedLeaf026_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5402)) namedLeaf026 = true :=
  by decide +kernel

def namedLeaf027 : LeafData := { rows := ![![1, 6, 4, 3, 2, 5], ![0, 6, 4, 3, 2, 5], ![4, 3, 6, 0, 1, 5], ![4, 2, 6, 0, 1, 5], ![3, 2, 6, 0, 1, 5], ![6, 0, 1, 2, 3, 4], ![5, 2, 3, 4, 0, 1]], proof := .tail 92 }

theorem namedLeaf027_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5403)) namedLeaf027 = true :=
  by decide +kernel

def namedLeaf028 : LeafData := { rows := ![![1, 4, 6, 3, 2, 5], ![0, 4, 6, 3, 2, 5], ![4, 6, 3, 0, 1, 5], ![4, 6, 2, 0, 1, 5], ![3, 2, 0, 1, 6, 5], ![6, 0, 1, 2, 3, 4], ![5, 3, 2, 0, 1, 4]], proof := .tail 104 }

theorem namedLeaf028_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5404)) namedLeaf028 = true :=
  by decide +kernel

def namedLeaf029 : LeafData := { rows := ![![1, 4, 6, 3, 2, 5], ![0, 6, 4, 3, 2, 5], ![4, 6, 3, 0, 1, 5], ![4, 6, 2, 0, 1, 5], ![3, 2, 0, 6, 1, 5], ![6, 0, 1, 2, 3, 4], ![5, 3, 2, 0, 4, 1]], proof := .tail 104 }

theorem namedLeaf029_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5405)) namedLeaf029 = true :=
  by decide +kernel

def namedLeaf030 : LeafData := { rows := ![![1, 6, 4, 3, 2, 5], ![0, 6, 4, 3, 2, 5], ![4, 6, 3, 0, 1, 5], ![4, 6, 2, 0, 1, 5], ![3, 2, 6, 0, 1, 5], ![6, 0, 1, 2, 3, 4], ![5, 3, 2, 4, 0, 1]], proof := .tail 104 }

theorem namedLeaf030_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5406)) namedLeaf030 = true :=
  by decide +kernel

def namedLeaf031 : LeafData := { rows := ![![1, 6, 4, 3, 2, 5], ![0, 6, 4, 3, 2, 5], ![6, 4, 3, 0, 1, 5], ![4, 6, 2, 0, 1, 5], ![3, 6, 2, 0, 1, 5], ![6, 0, 1, 2, 3, 4], ![5, 3, 4, 2, 0, 1]], proof := .tail 82 }

theorem namedLeaf031_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5407)) namedLeaf031 = true :=
  by decide +kernel

def namedLeaf032 : LeafData := { rows := ![![1, 6, 4, 3, 2, 5], ![0, 6, 4, 3, 2, 5], ![6, 4, 3, 0, 1, 5], ![6, 4, 2, 0, 1, 5], ![6, 3, 2, 0, 1, 5], ![6, 0, 1, 2, 3, 4], ![5, 4, 3, 2, 0, 1]], proof := .tail 57 }

theorem namedLeaf032_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5408)) namedLeaf032 = true :=
  by decide +kernel

def namedLeaf033 : LeafData := { rows := ![![1, 3, 4, 2, 5, 6], ![0, 3, 4, 5, 2, 6], ![3, 4, 0, 5, 1, 6], ![2, 0, 1, 4, 5, 6], ![2, 0, 1, 3, 5, 6], ![0, 2, 1, 3, 4, 6], ![0, 1, 2, 3, 4, 5]], proof := .tail 119 }

theorem namedLeaf033_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5409)) namedLeaf033 = true :=
  by decide +kernel

def namedLeaf034 : LeafData := { rows := ![![1, 3, 4, 2, 5, 6], ![0, 3, 4, 5, 2, 6], ![3, 4, 0, 5, 1, 6], ![2, 0, 1, 4, 5, 6], ![2, 0, 1, 3, 6, 5], ![0, 2, 1, 3, 6, 4], ![0, 1, 2, 3, 5, 4]], proof := .tail 153 }

theorem namedLeaf034_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5410)) namedLeaf034 = true :=
  by decide +kernel

def namedLeaf035 : LeafData := { rows := ![![1, 3, 4, 2, 5, 6], ![0, 3, 4, 5, 2, 6], ![3, 4, 0, 5, 1, 6], ![2, 0, 1, 4, 6, 5], ![2, 0, 1, 3, 6, 5], ![0, 2, 1, 6, 3, 4], ![0, 1, 2, 5, 3, 4]], proof := .tail 172 }

theorem namedLeaf035_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5411)) namedLeaf035 = true :=
  by decide +kernel

def namedLeaf036 : LeafData := { rows := ![![1, 3, 4, 2, 5, 6], ![0, 3, 4, 5, 2, 6], ![3, 4, 0, 5, 1, 6], ![2, 0, 1, 6, 4, 5], ![2, 0, 1, 6, 3, 5], ![0, 2, 1, 6, 3, 4], ![0, 1, 2, 5, 4, 3]], proof := .tail 117 }

theorem namedLeaf036_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5412)) namedLeaf036 = true :=
  by decide +kernel

def namedLeaf037 : LeafData := { rows := ![![1, 3, 4, 2, 5, 6], ![0, 3, 4, 5, 6, 2], ![3, 4, 0, 5, 6, 1], ![2, 0, 1, 4, 5, 6], ![2, 0, 1, 3, 5, 6], ![0, 2, 1, 3, 4, 6], ![0, 2, 1, 3, 4, 5]], proof := .tail 68 }

theorem namedLeaf037_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5413)) namedLeaf037 = true :=
  by decide +kernel

def namedLeaf038 : LeafData := { rows := ![![1, 3, 4, 2, 5, 6], ![0, 3, 4, 5, 6, 2], ![3, 4, 0, 5, 6, 1], ![2, 0, 1, 4, 5, 6], ![2, 0, 1, 3, 6, 5], ![0, 2, 1, 3, 6, 4], ![0, 2, 1, 3, 5, 4]], proof := .tail 72 }

theorem namedLeaf038_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5414)) namedLeaf038 = true :=
  by decide +kernel

def namedLeaf039 : LeafData := { rows := ![![1, 3, 4, 2, 5, 6], ![0, 3, 4, 5, 6, 2], ![3, 4, 0, 5, 6, 1], ![2, 0, 1, 4, 6, 5], ![2, 0, 1, 3, 6, 5], ![0, 2, 1, 6, 3, 4], ![0, 2, 1, 5, 3, 4]], proof := .tail 170 }

theorem namedLeaf039_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5415)) namedLeaf039 = true :=
  by decide +kernel

def namedLeaf040 : LeafData := { rows := ![![1, 3, 4, 2, 5, 6], ![0, 3, 4, 5, 6, 2], ![3, 4, 0, 5, 6, 1], ![2, 0, 1, 6, 4, 5], ![2, 0, 1, 6, 3, 5], ![0, 2, 1, 6, 3, 4], ![0, 2, 1, 5, 4, 3]], proof := .tail 49 }

theorem namedLeaf040_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5416)) namedLeaf040 = true :=
  by decide +kernel

def namedLeaf041 : LeafData := { rows := ![![1, 3, 4, 2, 5, 6], ![0, 3, 4, 6, 5, 2], ![3, 4, 0, 5, 6, 1], ![2, 0, 1, 4, 6, 5], ![2, 0, 1, 3, 6, 5], ![0, 2, 6, 1, 3, 4], ![0, 2, 5, 1, 3, 4]], proof := .tail 164 }

theorem namedLeaf041_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5417)) namedLeaf041 = true :=
  by decide +kernel

def namedLeaf042 : LeafData := { rows := ![![1, 3, 4, 2, 5, 6], ![0, 3, 4, 6, 5, 2], ![3, 4, 0, 5, 6, 1], ![2, 0, 1, 6, 4, 5], ![2, 0, 1, 6, 3, 5], ![0, 2, 6, 1, 3, 4], ![0, 2, 5, 1, 4, 3]], proof := .tail 143 }

theorem namedLeaf042_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5418)) namedLeaf042 = true :=
  by decide +kernel

def namedLeaf043 : LeafData := { rows := ![![1, 3, 4, 2, 5, 6], ![0, 3, 6, 4, 5, 2], ![3, 4, 0, 5, 6, 1], ![2, 0, 1, 6, 4, 5], ![2, 0, 6, 1, 3, 5], ![0, 2, 6, 1, 3, 4], ![0, 2, 5, 4, 1, 3]], proof := .tail 77 }

theorem namedLeaf043_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5419)) namedLeaf043 = true :=
  by decide +kernel

def namedLeaf044 : LeafData := { rows := ![![1, 3, 4, 2, 5, 6], ![0, 6, 3, 4, 5, 2], ![3, 4, 0, 5, 6, 1], ![2, 0, 6, 1, 4, 5], ![2, 0, 6, 1, 3, 5], ![0, 2, 6, 1, 3, 4], ![0, 2, 5, 4, 3, 1]], proof := .tail 161 }

theorem namedLeaf044_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5420)) namedLeaf044 = true :=
  by decide +kernel

def namedLeaf045 : LeafData := { rows := ![![1, 3, 4, 2, 5, 6], ![0, 3, 4, 6, 5, 2], ![3, 4, 0, 6, 5, 1], ![2, 0, 1, 4, 6, 5], ![2, 0, 1, 3, 6, 5], ![0, 6, 2, 1, 3, 4], ![0, 5, 2, 1, 3, 4]], proof := .tail 47 }

theorem namedLeaf045_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5421)) namedLeaf045 = true :=
  by decide +kernel

def namedLeaf046 : LeafData := { rows := ![![1, 3, 4, 2, 5, 6], ![0, 3, 4, 6, 5, 2], ![3, 4, 0, 6, 5, 1], ![2, 0, 1, 6, 4, 5], ![2, 0, 1, 6, 3, 5], ![0, 6, 2, 1, 3, 4], ![0, 5, 2, 1, 4, 3]], proof := .tail 47 }

theorem namedLeaf046_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5422)) namedLeaf046 = true :=
  by decide +kernel

def namedLeaf047 : LeafData := { rows := ![![1, 3, 4, 2, 5, 6], ![0, 3, 6, 4, 5, 2], ![3, 4, 0, 6, 5, 1], ![2, 0, 1, 6, 4, 5], ![2, 0, 6, 1, 3, 5], ![0, 6, 2, 1, 3, 4], ![0, 5, 2, 4, 1, 3]], proof := .tail 47 }

theorem namedLeaf047_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5423)) namedLeaf047 = true :=
  by decide +kernel

def namedLeaf048 : LeafData := { rows := ![![1, 3, 4, 2, 5, 6], ![0, 6, 3, 4, 5, 2], ![3, 4, 0, 6, 5, 1], ![2, 0, 6, 1, 4, 5], ![2, 0, 6, 1, 3, 5], ![0, 6, 2, 1, 3, 4], ![0, 5, 2, 4, 3, 1]], proof := .tail 47 }

theorem namedLeaf048_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5424)) namedLeaf048 = true :=
  by decide +kernel

def namedLeaf049 : LeafData := { rows := ![![1, 3, 4, 2, 6, 5], ![0, 3, 4, 6, 5, 2], ![3, 4, 0, 6, 5, 1], ![2, 0, 1, 4, 6, 5], ![2, 0, 1, 3, 6, 5], ![6, 0, 2, 1, 3, 4], ![5, 0, 2, 1, 3, 4]], proof := .tail 123 }

theorem namedLeaf049_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5425)) namedLeaf049 = true :=
  by decide +kernel

def namedLeaf050 : LeafData := { rows := ![![1, 3, 4, 2, 6, 5], ![0, 3, 4, 6, 5, 2], ![3, 4, 0, 6, 5, 1], ![2, 0, 1, 6, 4, 5], ![2, 0, 1, 6, 3, 5], ![6, 0, 2, 1, 3, 4], ![5, 0, 2, 1, 4, 3]], proof := .tail 156 }

theorem namedLeaf050_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5426)) namedLeaf050 = true :=
  by decide +kernel

def namedLeaf051 : LeafData := { rows := ![![1, 3, 4, 2, 6, 5], ![0, 3, 6, 4, 5, 2], ![3, 4, 0, 6, 5, 1], ![2, 0, 1, 6, 4, 5], ![2, 0, 6, 1, 3, 5], ![6, 0, 2, 1, 3, 4], ![5, 0, 2, 4, 1, 3]], proof := .tail 136 }

theorem namedLeaf051_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5427)) namedLeaf051 = true :=
  by decide +kernel

def namedLeaf052 : LeafData := { rows := ![![1, 3, 4, 2, 6, 5], ![0, 6, 3, 4, 5, 2], ![3, 4, 0, 6, 5, 1], ![2, 0, 6, 1, 4, 5], ![2, 0, 6, 1, 3, 5], ![6, 0, 2, 1, 3, 4], ![5, 0, 2, 4, 3, 1]], proof := .tail 160 }

theorem namedLeaf052_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5428)) namedLeaf052 = true :=
  by decide +kernel

def namedLeaf053 : LeafData := { rows := ![![1, 3, 4, 6, 2, 5], ![0, 3, 4, 6, 5, 2], ![3, 4, 6, 0, 5, 1], ![2, 0, 1, 4, 6, 5], ![2, 0, 1, 3, 6, 5], ![6, 0, 2, 1, 3, 4], ![5, 2, 0, 1, 3, 4]], proof := .tail 90 }

theorem namedLeaf053_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5429)) namedLeaf053 = true :=
  by decide +kernel

def namedLeaf054 : LeafData := { rows := ![![1, 3, 4, 6, 2, 5], ![0, 3, 4, 6, 5, 2], ![3, 4, 6, 0, 5, 1], ![2, 0, 1, 6, 4, 5], ![2, 0, 1, 6, 3, 5], ![6, 0, 2, 1, 3, 4], ![5, 2, 0, 1, 4, 3]], proof := .tail 156 }

theorem namedLeaf054_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5430)) namedLeaf054 = true :=
  by decide +kernel

def namedLeaf055 : LeafData := { rows := ![![1, 3, 4, 6, 2, 5], ![0, 3, 6, 4, 5, 2], ![3, 4, 6, 0, 5, 1], ![2, 0, 1, 6, 4, 5], ![2, 0, 6, 1, 3, 5], ![6, 0, 2, 1, 3, 4], ![5, 2, 0, 4, 1, 3]], proof := .tail 90 }

theorem namedLeaf055_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5431)) namedLeaf055 = true :=
  by decide +kernel

def namedLeaf056 : LeafData := { rows := ![![1, 3, 6, 4, 2, 5], ![0, 3, 6, 4, 5, 2], ![3, 4, 6, 0, 5, 1], ![2, 0, 1, 6, 4, 5], ![2, 6, 0, 1, 3, 5], ![6, 0, 2, 1, 3, 4], ![5, 2, 4, 0, 1, 3]], proof := .tail 86 }

theorem namedLeaf056_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5432)) namedLeaf056 = true :=
  by decide +kernel

def namedLeaf057 : LeafData := { rows := ![![1, 3, 6, 4, 2, 5], ![0, 3, 6, 4, 5, 2], ![3, 6, 4, 0, 5, 1], ![2, 0, 1, 6, 4, 5], ![6, 2, 0, 1, 3, 5], ![6, 0, 2, 1, 3, 4], ![5, 4, 2, 0, 1, 3]], proof := .tail 90 }

theorem namedLeaf057_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5433)) namedLeaf057 = true :=
  by decide +kernel

def namedLeaf058 : LeafData := { rows := ![![1, 3, 4, 6, 2, 5], ![0, 6, 3, 4, 5, 2], ![3, 4, 6, 0, 5, 1], ![2, 0, 6, 1, 4, 5], ![2, 0, 6, 1, 3, 5], ![6, 0, 2, 1, 3, 4], ![5, 2, 0, 4, 3, 1]], proof := .tail 81 }

theorem namedLeaf058_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5434)) namedLeaf058 = true :=
  by decide +kernel

def namedLeaf059 : LeafData := { rows := ![![1, 3, 6, 4, 2, 5], ![0, 6, 3, 4, 5, 2], ![3, 4, 6, 0, 5, 1], ![2, 0, 6, 1, 4, 5], ![2, 6, 0, 1, 3, 5], ![6, 0, 2, 1, 3, 4], ![5, 2, 4, 0, 3, 1]], proof := .tail 81 }

theorem namedLeaf059_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5435)) namedLeaf059 = true :=
  by decide +kernel

def namedLeaf060 : LeafData := { rows := ![![1, 3, 6, 4, 2, 5], ![0, 6, 3, 4, 5, 2], ![3, 6, 4, 0, 5, 1], ![2, 0, 6, 1, 4, 5], ![6, 2, 0, 1, 3, 5], ![6, 0, 2, 1, 3, 4], ![5, 4, 2, 0, 3, 1]], proof := .tail 146 }

theorem namedLeaf060_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5436)) namedLeaf060 = true :=
  by decide +kernel

def namedLeaf061 : LeafData := { rows := ![![1, 6, 3, 4, 2, 5], ![0, 6, 3, 4, 5, 2], ![3, 4, 6, 0, 5, 1], ![2, 6, 0, 1, 4, 5], ![2, 6, 0, 1, 3, 5], ![6, 0, 2, 1, 3, 4], ![5, 2, 4, 3, 0, 1]], proof := .tail 34 }

theorem namedLeaf061_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5437)) namedLeaf061 = true :=
  by decide +kernel

def namedLeaf062 : LeafData := { rows := ![![1, 6, 3, 4, 2, 5], ![0, 6, 3, 4, 5, 2], ![3, 6, 4, 0, 5, 1], ![2, 6, 0, 1, 4, 5], ![6, 2, 0, 1, 3, 5], ![6, 0, 2, 1, 3, 4], ![5, 4, 2, 3, 0, 1]], proof := .tail 133 }

theorem namedLeaf062_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5438)) namedLeaf062 = true :=
  by decide +kernel

def namedLeaf063 : LeafData := { rows := ![![1, 6, 3, 4, 2, 5], ![0, 6, 3, 4, 5, 2], ![6, 3, 4, 0, 5, 1], ![6, 2, 0, 1, 4, 5], ![6, 2, 0, 1, 3, 5], ![6, 0, 2, 1, 3, 4], ![5, 4, 3, 2, 0, 1]], proof := .tail 22 }

theorem namedLeaf063_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5439)) namedLeaf063 = true :=
  by decide +kernel

def namedLeaf064 : LeafData := { rows := ![![1, 3, 4, 2, 5, 6], ![0, 3, 4, 5, 2, 6], ![3, 4, 0, 5, 1, 6], ![2, 0, 1, 5, 4, 6], ![2, 0, 1, 5, 3, 6], ![0, 2, 1, 4, 3, 6], ![0, 1, 2, 3, 4, 5]], proof := .tail 144 }

theorem namedLeaf064_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5440)) namedLeaf064 = true :=
  by decide +kernel

def namedLeaf065 : LeafData := { rows := ![![1, 3, 4, 2, 5, 6], ![0, 3, 4, 5, 2, 6], ![3, 4, 0, 5, 1, 6], ![2, 0, 1, 5, 6, 4], ![2, 0, 1, 5, 6, 3], ![0, 2, 1, 4, 3, 6], ![0, 1, 2, 4, 3, 5]], proof := .tail 83 }

theorem namedLeaf065_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5441)) namedLeaf065 = true :=
  by decide +kernel

def namedLeaf066 : LeafData := { rows := ![![1, 3, 4, 2, 5, 6], ![0, 3, 4, 5, 2, 6], ![3, 4, 0, 5, 1, 6], ![2, 0, 1, 6, 5, 4], ![2, 0, 1, 5, 6, 3], ![0, 2, 1, 4, 6, 3], ![0, 1, 2, 4, 5, 3]], proof := .tail 116 }

theorem namedLeaf066_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5442)) namedLeaf066 = true :=
  by decide +kernel

def namedLeaf067 : LeafData := { rows := ![![1, 3, 4, 2, 5, 6], ![0, 3, 4, 5, 2, 6], ![3, 4, 0, 5, 1, 6], ![2, 0, 1, 6, 5, 4], ![2, 0, 1, 6, 5, 3], ![0, 2, 1, 6, 4, 3], ![0, 1, 2, 5, 4, 3]], proof := .tail 107 }

theorem namedLeaf067_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5443)) namedLeaf067 = true :=
  by decide +kernel

def namedLeaf068 : LeafData := { rows := ![![1, 3, 4, 2, 5, 6], ![0, 3, 4, 5, 6, 2], ![3, 4, 0, 5, 6, 1], ![2, 0, 1, 5, 4, 6], ![2, 0, 1, 5, 3, 6], ![0, 2, 1, 4, 3, 6], ![0, 2, 1, 3, 4, 5]], proof := .tail 91 }

theorem namedLeaf068_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5444)) namedLeaf068 = true :=
  by decide +kernel

def namedLeaf069 : LeafData := { rows := ![![1, 3, 4, 2, 5, 6], ![0, 3, 4, 5, 6, 2], ![3, 4, 0, 5, 6, 1], ![2, 0, 1, 5, 6, 4], ![2, 0, 1, 5, 6, 3], ![0, 2, 1, 4, 3, 6], ![0, 2, 1, 4, 3, 5]], proof := .tail 68 }

theorem namedLeaf069_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5445)) namedLeaf069 = true :=
  by decide +kernel

def namedLeaf070 : LeafData := { rows := ![![1, 3, 4, 2, 5, 6], ![0, 3, 4, 5, 6, 2], ![3, 4, 0, 5, 6, 1], ![2, 0, 1, 6, 5, 4], ![2, 0, 1, 5, 6, 3], ![0, 2, 1, 4, 6, 3], ![0, 2, 1, 4, 5, 3]], proof := .tail 158 }

theorem namedLeaf070_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5446)) namedLeaf070 = true :=
  by decide +kernel

def namedLeaf071 : LeafData := { rows := ![![1, 3, 4, 2, 5, 6], ![0, 3, 4, 5, 6, 2], ![3, 4, 0, 5, 6, 1], ![2, 0, 1, 6, 5, 4], ![2, 0, 1, 6, 5, 3], ![0, 2, 1, 6, 4, 3], ![0, 2, 1, 5, 4, 3]], proof := .tail 101 }

theorem namedLeaf071_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5447)) namedLeaf071 = true :=
  by decide +kernel

def namedLeaf072 : LeafData := { rows := ![![1, 3, 4, 2, 5, 6], ![0, 3, 4, 6, 5, 2], ![3, 4, 0, 5, 6, 1], ![2, 0, 1, 6, 5, 4], ![2, 0, 1, 6, 5, 3], ![0, 2, 6, 1, 4, 3], ![0, 2, 5, 1, 4, 3]], proof := .tail 101 }

theorem namedLeaf072_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5448)) namedLeaf072 = true :=
  by decide +kernel

def namedLeaf073 : LeafData := { rows := ![![1, 3, 4, 2, 5, 6], ![0, 3, 6, 4, 5, 2], ![3, 4, 0, 5, 6, 1], ![2, 0, 1, 6, 5, 4], ![2, 0, 6, 1, 5, 3], ![0, 2, 6, 1, 4, 3], ![0, 2, 5, 4, 1, 3]], proof := .tail 73 }

theorem namedLeaf073_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5449)) namedLeaf073 = true :=
  by decide +kernel

def namedLeaf074 : LeafData := { rows := ![![1, 3, 4, 2, 5, 6], ![0, 6, 3, 4, 5, 2], ![3, 4, 0, 5, 6, 1], ![2, 0, 6, 1, 5, 4], ![2, 0, 6, 1, 5, 3], ![0, 2, 6, 1, 4, 3], ![0, 2, 5, 4, 3, 1]], proof := .tail 73 }

theorem namedLeaf074_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5450)) namedLeaf074 = true :=
  by decide +kernel

def namedLeaf075 : LeafData := { rows := ![![1, 3, 4, 2, 5, 6], ![0, 3, 4, 6, 5, 2], ![3, 4, 0, 6, 5, 1], ![2, 0, 1, 6, 5, 4], ![2, 0, 1, 6, 5, 3], ![0, 6, 2, 1, 4, 3], ![0, 5, 2, 1, 4, 3]], proof := .tail 47 }

theorem namedLeaf075_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5451)) namedLeaf075 = true :=
  by decide +kernel

def namedLeaf076 : LeafData := { rows := ![![1, 3, 4, 2, 5, 6], ![0, 3, 6, 4, 5, 2], ![3, 4, 0, 6, 5, 1], ![2, 0, 1, 6, 5, 4], ![2, 0, 6, 1, 5, 3], ![0, 6, 2, 1, 4, 3], ![0, 5, 2, 4, 1, 3]], proof := .tail 15 }

theorem namedLeaf076_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5452)) namedLeaf076 = true :=
  by decide +kernel

def namedLeaf077 : LeafData := { rows := ![![1, 3, 4, 2, 5, 6], ![0, 6, 3, 4, 5, 2], ![3, 4, 0, 6, 5, 1], ![2, 0, 6, 1, 5, 4], ![2, 0, 6, 1, 5, 3], ![0, 6, 2, 1, 4, 3], ![0, 5, 2, 4, 3, 1]], proof := .tail 15 }

theorem namedLeaf077_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5453)) namedLeaf077 = true :=
  by decide +kernel

def namedLeaf078 : LeafData := { rows := ![![1, 3, 4, 2, 6, 5], ![0, 3, 4, 6, 5, 2], ![3, 4, 0, 6, 5, 1], ![2, 0, 1, 6, 5, 4], ![2, 0, 1, 6, 5, 3], ![6, 0, 2, 1, 4, 3], ![5, 0, 2, 1, 4, 3]], proof := .tail 123 }

theorem namedLeaf078_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5454)) namedLeaf078 = true :=
  by decide +kernel

def namedLeaf079 : LeafData := { rows := ![![1, 3, 4, 2, 6, 5], ![0, 3, 6, 4, 5, 2], ![3, 4, 0, 6, 5, 1], ![2, 0, 1, 6, 5, 4], ![2, 0, 6, 1, 5, 3], ![6, 0, 2, 1, 4, 3], ![5, 0, 2, 4, 1, 3]], proof := .tail 15 }

theorem namedLeaf079_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5455)) namedLeaf079 = true :=
  by decide +kernel

def namedLeaf080 : LeafData := { rows := ![![1, 3, 4, 2, 6, 5], ![0, 6, 3, 4, 5, 2], ![3, 4, 0, 6, 5, 1], ![2, 0, 6, 1, 5, 4], ![2, 0, 6, 1, 5, 3], ![6, 0, 2, 1, 4, 3], ![5, 0, 2, 4, 3, 1]], proof := .tail 15 }

theorem namedLeaf080_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5456)) namedLeaf080 = true :=
  by decide +kernel

def namedLeaf081 : LeafData := { rows := ![![1, 3, 4, 6, 2, 5], ![0, 3, 4, 6, 5, 2], ![3, 4, 6, 0, 5, 1], ![2, 0, 1, 6, 5, 4], ![2, 0, 1, 6, 5, 3], ![6, 0, 2, 1, 4, 3], ![5, 2, 0, 1, 4, 3]], proof := .tail 90 }

theorem namedLeaf081_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5457)) namedLeaf081 = true :=
  by decide +kernel

def namedLeaf082 : LeafData := { rows := ![![1, 3, 4, 6, 2, 5], ![0, 3, 6, 4, 5, 2], ![3, 4, 6, 0, 5, 1], ![2, 0, 1, 6, 5, 4], ![2, 0, 6, 1, 5, 3], ![6, 0, 2, 1, 4, 3], ![5, 2, 0, 4, 1, 3]], proof := .tail 18 }

theorem namedLeaf082_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5458)) namedLeaf082 = true :=
  by decide +kernel

def namedLeaf083 : LeafData := { rows := ![![1, 3, 6, 4, 2, 5], ![0, 3, 6, 4, 5, 2], ![3, 4, 6, 0, 5, 1], ![2, 0, 1, 6, 5, 4], ![2, 6, 0, 1, 5, 3], ![6, 0, 2, 1, 4, 3], ![5, 2, 4, 0, 1, 3]], proof := .tail 86 }

theorem namedLeaf083_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5459)) namedLeaf083 = true :=
  by decide +kernel

def namedLeaf084 : LeafData := { rows := ![![1, 3, 6, 4, 2, 5], ![0, 3, 6, 4, 5, 2], ![3, 6, 4, 0, 5, 1], ![2, 0, 1, 6, 5, 4], ![6, 2, 0, 1, 5, 3], ![6, 0, 2, 1, 4, 3], ![5, 4, 2, 0, 1, 3]], proof := .tail 35 }

theorem namedLeaf084_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5460)) namedLeaf084 = true :=
  by decide +kernel

def namedLeaf085 : LeafData := { rows := ![![1, 3, 4, 6, 2, 5], ![0, 6, 3, 4, 5, 2], ![3, 4, 6, 0, 5, 1], ![2, 0, 6, 1, 5, 4], ![2, 0, 6, 1, 5, 3], ![6, 0, 2, 1, 4, 3], ![5, 2, 0, 4, 3, 1]], proof := .tail 18 }

theorem namedLeaf085_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5461)) namedLeaf085 = true :=
  by decide +kernel

def namedLeaf086 : LeafData := { rows := ![![1, 3, 6, 4, 2, 5], ![0, 6, 3, 4, 5, 2], ![3, 4, 6, 0, 5, 1], ![2, 0, 6, 1, 5, 4], ![2, 6, 0, 1, 5, 3], ![6, 0, 2, 1, 4, 3], ![5, 2, 4, 0, 3, 1]], proof := .tail 86 }

theorem namedLeaf086_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5462)) namedLeaf086 = true :=
  by decide +kernel

def namedLeaf087 : LeafData := { rows := ![![1, 3, 6, 4, 2, 5], ![0, 6, 3, 4, 5, 2], ![3, 6, 4, 0, 5, 1], ![2, 0, 6, 1, 5, 4], ![6, 2, 0, 1, 5, 3], ![6, 0, 2, 1, 4, 3], ![5, 4, 2, 0, 3, 1]], proof := .tail 30 }

theorem namedLeaf087_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5463)) namedLeaf087 = true :=
  by decide +kernel

def namedLeaf088 : LeafData := { rows := ![![1, 6, 3, 4, 2, 5], ![0, 6, 3, 4, 5, 2], ![3, 4, 6, 0, 5, 1], ![2, 6, 0, 1, 5, 4], ![2, 6, 0, 1, 5, 3], ![6, 0, 2, 1, 4, 3], ![5, 2, 4, 3, 0, 1]], proof := .tail 2 }

theorem namedLeaf088_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5464)) namedLeaf088 = true :=
  by decide +kernel

def namedLeaf089 : LeafData := { rows := ![![1, 6, 3, 4, 2, 5], ![0, 6, 3, 4, 5, 2], ![3, 6, 4, 0, 5, 1], ![2, 6, 0, 1, 5, 4], ![6, 2, 0, 1, 5, 3], ![6, 0, 2, 1, 4, 3], ![5, 4, 2, 3, 0, 1]], proof := .tail 106 }

theorem namedLeaf089_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5465)) namedLeaf089 = true :=
  by decide +kernel

def namedLeaf090 : LeafData := { rows := ![![1, 6, 3, 4, 2, 5], ![0, 6, 3, 4, 5, 2], ![6, 3, 4, 0, 5, 1], ![6, 2, 0, 1, 5, 4], ![6, 2, 0, 1, 5, 3], ![6, 0, 2, 1, 4, 3], ![5, 4, 3, 2, 0, 1]], proof := .tail 122 }

theorem namedLeaf090_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5466)) namedLeaf090 = true :=
  by decide +kernel

def namedLeaf091 : LeafData := { rows := ![![1, 3, 4, 2, 5, 6], ![0, 3, 5, 4, 2, 6], ![3, 4, 0, 5, 1, 6], ![2, 0, 1, 5, 4, 6], ![2, 0, 5, 1, 3, 6], ![0, 2, 4, 1, 3, 6], ![0, 1, 2, 3, 4, 5]], proof := .tail 20 }

theorem namedLeaf091_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5467)) namedLeaf091 = true :=
  by decide +kernel

def namedLeaf092 : LeafData := { rows := ![![1, 3, 4, 2, 5, 6], ![0, 3, 5, 4, 2, 6], ![3, 4, 0, 5, 1, 6], ![2, 0, 1, 5, 6, 4], ![2, 0, 5, 1, 6, 3], ![0, 2, 4, 1, 3, 6], ![0, 1, 2, 4, 3, 5]], proof := .tail 130 }

theorem namedLeaf092_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5468)) namedLeaf092 = true :=
  by decide +kernel

def namedLeaf093 : LeafData := { rows := ![![1, 3, 4, 2, 5, 6], ![0, 3, 5, 4, 2, 6], ![3, 4, 0, 5, 1, 6], ![2, 0, 1, 6, 5, 4], ![2, 0, 5, 1, 6, 3], ![0, 2, 4, 1, 6, 3], ![0, 1, 2, 4, 5, 3]], proof := .tail 157 }

theorem namedLeaf093_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5469)) namedLeaf093 = true :=
  by decide +kernel

def namedLeaf094 : LeafData := { rows := ![![1, 3, 4, 2, 5, 6], ![0, 3, 5, 4, 6, 2], ![3, 4, 0, 5, 6, 1], ![2, 0, 1, 5, 4, 6], ![2, 0, 5, 1, 3, 6], ![0, 2, 4, 1, 3, 6], ![0, 2, 1, 3, 4, 5]], proof := .tail 44 }

theorem namedLeaf094_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5470)) namedLeaf094 = true :=
  by decide +kernel

def namedLeaf095 : LeafData := { rows := ![![1, 3, 4, 2, 5, 6], ![0, 3, 5, 4, 6, 2], ![3, 4, 0, 5, 6, 1], ![2, 0, 1, 5, 6, 4], ![2, 0, 5, 1, 6, 3], ![0, 2, 4, 1, 3, 6], ![0, 2, 1, 4, 3, 5]], proof := .tail 130 }

theorem namedLeaf095_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5471)) namedLeaf095 = true :=
  by decide +kernel

def namedLeaf096 : LeafData := { rows := ![![1, 3, 4, 2, 5, 6], ![0, 3, 5, 4, 6, 2], ![3, 4, 0, 5, 6, 1], ![2, 0, 1, 6, 5, 4], ![2, 0, 5, 1, 6, 3], ![0, 2, 4, 1, 6, 3], ![0, 2, 1, 4, 5, 3]], proof := .tail 157 }

theorem namedLeaf096_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5472)) namedLeaf096 = true :=
  by decide +kernel

def namedLeaf097 : LeafData := { rows := ![![1, 3, 4, 2, 5, 6], ![0, 3, 5, 6, 4, 2], ![3, 4, 0, 5, 6, 1], ![2, 0, 1, 5, 6, 4], ![2, 0, 5, 6, 1, 3], ![0, 2, 4, 1, 3, 6], ![0, 2, 4, 1, 3, 5]], proof := .tail 74 }

theorem namedLeaf097_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5473)) namedLeaf097 = true :=
  by decide +kernel

def namedLeaf098 : LeafData := { rows := ![![1, 3, 4, 2, 5, 6], ![0, 3, 5, 6, 4, 2], ![3, 4, 0, 5, 6, 1], ![2, 0, 1, 6, 5, 4], ![2, 0, 5, 6, 1, 3], ![0, 2, 4, 1, 6, 3], ![0, 2, 4, 1, 5, 3]], proof := .tail 0 }

theorem namedLeaf098_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5474)) namedLeaf098 = true :=
  by decide +kernel

def namedLeaf099 : LeafData := { rows := ![![1, 3, 4, 2, 5, 6], ![0, 3, 6, 5, 4, 2], ![3, 4, 0, 5, 6, 1], ![2, 0, 1, 6, 5, 4], ![2, 0, 5, 6, 1, 3], ![0, 2, 4, 6, 1, 3], ![0, 2, 4, 5, 1, 3]], proof := .tail 19 }

theorem namedLeaf099_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5475)) namedLeaf099 = true :=
  by decide +kernel

def namedLeaf100 : LeafData := { rows := ![![1, 3, 4, 2, 5, 6], ![0, 3, 6, 5, 4, 2], ![3, 4, 0, 5, 6, 1], ![2, 0, 1, 6, 5, 4], ![2, 0, 6, 5, 1, 3], ![0, 2, 6, 4, 1, 3], ![0, 2, 5, 4, 1, 3]], proof := .tail 17 }

theorem namedLeaf100_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5476)) namedLeaf100 = true :=
  by decide +kernel

def namedLeaf101 : LeafData := { rows := ![![1, 3, 4, 2, 5, 6], ![0, 6, 3, 5, 4, 2], ![3, 4, 0, 5, 6, 1], ![2, 0, 6, 1, 5, 4], ![2, 0, 5, 6, 1, 3], ![0, 2, 4, 6, 1, 3], ![0, 2, 4, 5, 3, 1]], proof := .tail 151 }

theorem namedLeaf101_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5477)) namedLeaf101 = true :=
  by decide +kernel

def namedLeaf102 : LeafData := { rows := ![![1, 3, 4, 2, 5, 6], ![0, 6, 3, 5, 4, 2], ![3, 4, 0, 5, 6, 1], ![2, 0, 6, 1, 5, 4], ![2, 0, 6, 5, 1, 3], ![0, 2, 6, 4, 1, 3], ![0, 2, 5, 4, 3, 1]], proof := .tail 17 }

theorem namedLeaf102_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5478)) namedLeaf102 = true :=
  by decide +kernel

def namedLeaf103 : LeafData := { rows := ![![1, 3, 4, 2, 5, 6], ![0, 3, 6, 5, 4, 2], ![3, 4, 0, 6, 5, 1], ![2, 0, 1, 6, 5, 4], ![2, 0, 6, 5, 1, 3], ![0, 6, 2, 4, 1, 3], ![0, 5, 2, 4, 1, 3]], proof := .tail 139 }

theorem namedLeaf103_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5479)) namedLeaf103 = true :=
  by decide +kernel

def namedLeaf104 : LeafData := { rows := ![![1, 3, 4, 2, 5, 6], ![0, 6, 3, 5, 4, 2], ![3, 4, 0, 6, 5, 1], ![2, 0, 6, 1, 5, 4], ![2, 0, 6, 5, 1, 3], ![0, 6, 2, 4, 1, 3], ![0, 5, 2, 4, 3, 1]], proof := .tail 139 }

theorem namedLeaf104_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5480)) namedLeaf104 = true :=
  by decide +kernel

def namedLeaf105 : LeafData := { rows := ![![1, 3, 4, 2, 6, 5], ![0, 3, 6, 5, 4, 2], ![3, 4, 0, 6, 5, 1], ![2, 0, 1, 6, 5, 4], ![2, 0, 6, 5, 1, 3], ![6, 0, 2, 4, 1, 3], ![5, 0, 2, 4, 1, 3]], proof := .tail 12 }

theorem namedLeaf105_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5481)) namedLeaf105 = true :=
  by decide +kernel

def namedLeaf106 : LeafData := { rows := ![![1, 3, 4, 2, 6, 5], ![0, 6, 3, 5, 4, 2], ![3, 4, 0, 6, 5, 1], ![2, 0, 6, 1, 5, 4], ![2, 0, 6, 5, 1, 3], ![6, 0, 2, 4, 1, 3], ![5, 0, 2, 4, 3, 1]], proof := .tail 66 }

theorem namedLeaf106_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5482)) namedLeaf106 = true :=
  by decide +kernel

def namedLeaf107 : LeafData := { rows := ![![1, 3, 4, 6, 2, 5], ![0, 3, 6, 5, 4, 2], ![3, 4, 6, 0, 5, 1], ![2, 0, 1, 6, 5, 4], ![2, 0, 6, 5, 1, 3], ![6, 0, 2, 4, 1, 3], ![5, 2, 0, 4, 1, 3]], proof := .tail 128 }

theorem namedLeaf107_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5483)) namedLeaf107 = true :=
  by decide +kernel

def namedLeaf108 : LeafData := { rows := ![![1, 3, 4, 6, 2, 5], ![0, 6, 3, 5, 4, 2], ![3, 4, 6, 0, 5, 1], ![2, 0, 6, 1, 5, 4], ![2, 0, 6, 5, 1, 3], ![6, 0, 2, 4, 1, 3], ![5, 2, 0, 4, 3, 1]], proof := .tail 54 }

theorem namedLeaf108_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5484)) namedLeaf108 = true :=
  by decide +kernel

def namedLeaf109 : LeafData := { rows := ![![1, 3, 6, 4, 2, 5], ![0, 3, 6, 5, 4, 2], ![3, 4, 6, 0, 5, 1], ![2, 0, 1, 6, 5, 4], ![2, 6, 0, 5, 1, 3], ![6, 0, 2, 4, 1, 3], ![5, 2, 4, 0, 1, 3]], proof := .tail 132 }

theorem namedLeaf109_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5485)) namedLeaf109 = true :=
  by decide +kernel

def namedLeaf110 : LeafData := { rows := ![![1, 3, 6, 4, 2, 5], ![0, 6, 3, 5, 4, 2], ![3, 4, 6, 0, 5, 1], ![2, 0, 6, 1, 5, 4], ![2, 6, 0, 5, 1, 3], ![6, 0, 2, 4, 1, 3], ![5, 2, 4, 0, 3, 1]], proof := .tail 132 }

theorem namedLeaf110_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5486)) namedLeaf110 = true :=
  by decide +kernel

def namedLeaf111 : LeafData := { rows := ![![1, 6, 3, 4, 2, 5], ![0, 6, 3, 5, 4, 2], ![3, 4, 6, 0, 5, 1], ![2, 6, 0, 1, 5, 4], ![2, 6, 0, 5, 1, 3], ![6, 0, 2, 4, 1, 3], ![5, 2, 4, 3, 0, 1]], proof := .tail 132 }

theorem namedLeaf111_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5487)) namedLeaf111 = true :=
  by decide +kernel

def namedLeaf112 : LeafData := { rows := ![![1, 3, 6, 4, 2, 5], ![0, 3, 6, 5, 4, 2], ![3, 6, 4, 0, 5, 1], ![2, 0, 1, 6, 5, 4], ![6, 2, 0, 5, 1, 3], ![6, 0, 2, 4, 1, 3], ![5, 4, 2, 0, 1, 3]], proof := .tail 109 }

theorem namedLeaf112_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5488)) namedLeaf112 = true :=
  by decide +kernel

def namedLeaf113 : LeafData := { rows := ![![1, 3, 6, 4, 2, 5], ![0, 6, 3, 5, 4, 2], ![3, 6, 4, 0, 5, 1], ![2, 0, 6, 1, 5, 4], ![6, 2, 0, 5, 1, 3], ![6, 0, 2, 4, 1, 3], ![5, 4, 2, 0, 3, 1]], proof := .tail 109 }

theorem namedLeaf113_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5489)) namedLeaf113 = true :=
  by decide +kernel

def namedLeaf114 : LeafData := { rows := ![![1, 6, 3, 4, 2, 5], ![0, 6, 3, 5, 4, 2], ![3, 6, 4, 0, 5, 1], ![2, 6, 0, 1, 5, 4], ![6, 2, 0, 5, 1, 3], ![6, 0, 2, 4, 1, 3], ![5, 4, 2, 3, 0, 1]], proof := .tail 79 }

theorem namedLeaf114_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5490)) namedLeaf114 = true :=
  by decide +kernel

def namedLeaf115 : LeafData := { rows := ![![1, 6, 3, 4, 2, 5], ![0, 6, 3, 5, 4, 2], ![6, 3, 4, 0, 5, 1], ![6, 2, 0, 1, 5, 4], ![6, 2, 0, 5, 1, 3], ![6, 0, 2, 4, 1, 3], ![5, 4, 3, 2, 0, 1]], proof := .tail 70 }

theorem namedLeaf115_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5491)) namedLeaf115 = true :=
  by decide +kernel

def namedLeaf116 : LeafData := { rows := ![![1, 3, 4, 2, 5, 6], ![0, 5, 3, 4, 2, 6], ![3, 4, 0, 5, 1, 6], ![2, 0, 5, 1, 4, 6], ![2, 0, 5, 1, 3, 6], ![0, 2, 4, 3, 1, 6], ![0, 1, 2, 3, 4, 5]], proof := .tail 32 }

theorem namedLeaf116_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5492)) namedLeaf116 = true :=
  by decide +kernel

def namedLeaf117 : LeafData := { rows := ![![1, 3, 4, 2, 5, 6], ![0, 5, 3, 4, 2, 6], ![3, 4, 0, 5, 1, 6], ![2, 0, 5, 1, 6, 4], ![2, 0, 5, 1, 6, 3], ![0, 2, 4, 3, 1, 6], ![0, 1, 2, 4, 3, 5]], proof := .tail 8 }

theorem namedLeaf117_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5493)) namedLeaf117 = true :=
  by decide +kernel

def namedLeaf118 : LeafData := { rows := ![![1, 3, 4, 2, 5, 6], ![0, 5, 3, 4, 6, 2], ![3, 4, 0, 5, 6, 1], ![2, 0, 5, 1, 4, 6], ![2, 0, 5, 1, 3, 6], ![0, 2, 4, 3, 1, 6], ![0, 2, 1, 3, 4, 5]], proof := .tail 32 }

theorem namedLeaf118_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5494)) namedLeaf118 = true :=
  by decide +kernel

def namedLeaf119 : LeafData := { rows := ![![1, 3, 4, 2, 5, 6], ![0, 5, 3, 4, 6, 2], ![3, 4, 0, 5, 6, 1], ![2, 0, 5, 1, 6, 4], ![2, 0, 5, 1, 6, 3], ![0, 2, 4, 3, 1, 6], ![0, 2, 1, 4, 3, 5]], proof := .tail 8 }

theorem namedLeaf119_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5495)) namedLeaf119 = true :=
  by decide +kernel

def namedLeaf120 : LeafData := { rows := ![![1, 3, 4, 2, 5, 6], ![0, 5, 3, 6, 4, 2], ![3, 4, 0, 5, 6, 1], ![2, 0, 5, 1, 6, 4], ![2, 0, 5, 6, 1, 3], ![0, 2, 4, 3, 1, 6], ![0, 2, 4, 1, 3, 5]], proof := .tail 55 }

theorem namedLeaf120_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5496)) namedLeaf120 = true :=
  by decide +kernel

def namedLeaf121 : LeafData := { rows := ![![1, 3, 4, 2, 5, 6], ![0, 5, 6, 3, 4, 2], ![3, 4, 0, 5, 6, 1], ![2, 0, 5, 6, 1, 4], ![2, 0, 5, 6, 1, 3], ![0, 2, 4, 3, 1, 6], ![0, 2, 4, 3, 1, 5]], proof := .tail 7 }

theorem namedLeaf121_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5497)) namedLeaf121 = true :=
  by decide +kernel

def namedLeaf122 : LeafData := { rows := ![![1, 3, 4, 2, 5, 6], ![0, 6, 5, 3, 4, 2], ![3, 4, 0, 5, 6, 1], ![2, 0, 5, 6, 1, 4], ![2, 0, 5, 6, 1, 3], ![0, 2, 4, 3, 6, 1], ![0, 2, 4, 3, 5, 1]], proof := .tail 127 }

theorem namedLeaf122_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5498)) namedLeaf122 = true :=
  by decide +kernel

def namedLeaf123 : LeafData := { rows := ![![1, 3, 4, 2, 5, 6], ![0, 6, 5, 3, 4, 2], ![3, 4, 0, 5, 6, 1], ![2, 0, 6, 5, 1, 4], ![2, 0, 5, 6, 1, 3], ![0, 2, 4, 6, 3, 1], ![0, 2, 4, 5, 3, 1]], proof := .tail 33 }

theorem namedLeaf123_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5499)) namedLeaf123 = true :=
  by decide +kernel

def namedLeaf124 : LeafData := { rows := ![![1, 3, 4, 2, 5, 6], ![0, 6, 5, 3, 4, 2], ![3, 4, 0, 5, 6, 1], ![2, 0, 6, 5, 1, 4], ![2, 0, 6, 5, 1, 3], ![0, 2, 6, 4, 3, 1], ![0, 2, 5, 4, 3, 1]], proof := .tail 52 }

theorem namedLeaf124_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5500)) namedLeaf124 = true :=
  by decide +kernel

def namedLeaf125 : LeafData := { rows := ![![1, 3, 4, 2, 5, 6], ![0, 6, 5, 3, 4, 2], ![3, 4, 0, 6, 5, 1], ![2, 0, 6, 5, 1, 4], ![2, 0, 6, 5, 1, 3], ![0, 6, 2, 4, 3, 1], ![0, 5, 2, 4, 3, 1]], proof := .tail 105 }

theorem namedLeaf125_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5501)) namedLeaf125 = true :=
  by decide +kernel

def namedLeaf126 : LeafData := { rows := ![![1, 3, 4, 2, 6, 5], ![0, 6, 5, 3, 4, 2], ![3, 4, 0, 6, 5, 1], ![2, 0, 6, 5, 1, 4], ![2, 0, 6, 5, 1, 3], ![6, 0, 2, 4, 3, 1], ![5, 0, 2, 4, 3, 1]], proof := .tail 155 }

theorem namedLeaf126_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5502)) namedLeaf126 = true :=
  by decide +kernel

def namedLeaf127 : LeafData := { rows := ![![1, 3, 4, 6, 2, 5], ![0, 6, 5, 3, 4, 2], ![3, 4, 6, 0, 5, 1], ![2, 0, 6, 5, 1, 4], ![2, 0, 6, 5, 1, 3], ![6, 0, 2, 4, 3, 1], ![5, 2, 0, 4, 3, 1]], proof := .tail 64 }

theorem namedLeaf127_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5503)) namedLeaf127 = true :=
  by decide +kernel

def fallback : LeafData := { rows := fun _ _ => 0, proof := .tail 0 }
def lookup (offset : ℕ) : LeafData :=
  if offset < 128 then (if offset < 64 then (if offset < 32 then (if offset < 16 then (if offset < 8 then (if offset < 4 then (if offset < 2 then (if offset < 1 then (namedLeaf000) else (namedLeaf001)) else (if offset < 3 then (namedLeaf002) else (namedLeaf003))) else (if offset < 6 then (if offset < 5 then (namedLeaf004) else (namedLeaf005)) else (if offset < 7 then (namedLeaf006) else (namedLeaf007)))) else (if offset < 12 then (if offset < 10 then (if offset < 9 then (namedLeaf008) else (namedLeaf009)) else (if offset < 11 then (namedLeaf010) else (namedLeaf011))) else (if offset < 14 then (if offset < 13 then (namedLeaf012) else (namedLeaf013)) else (if offset < 15 then (namedLeaf014) else (namedLeaf015))))) else (if offset < 24 then (if offset < 20 then (if offset < 18 then (if offset < 17 then (namedLeaf016) else (namedLeaf017)) else (if offset < 19 then (namedLeaf018) else (namedLeaf019))) else (if offset < 22 then (if offset < 21 then (namedLeaf020) else (namedLeaf021)) else (if offset < 23 then (namedLeaf022) else (namedLeaf023)))) else (if offset < 28 then (if offset < 26 then (if offset < 25 then (namedLeaf024) else (namedLeaf025)) else (if offset < 27 then (namedLeaf026) else (namedLeaf027))) else (if offset < 30 then (if offset < 29 then (namedLeaf028) else (namedLeaf029)) else (if offset < 31 then (namedLeaf030) else (namedLeaf031)))))) else (if offset < 48 then (if offset < 40 then (if offset < 36 then (if offset < 34 then (if offset < 33 then (namedLeaf032) else (namedLeaf033)) else (if offset < 35 then (namedLeaf034) else (namedLeaf035))) else (if offset < 38 then (if offset < 37 then (namedLeaf036) else (namedLeaf037)) else (if offset < 39 then (namedLeaf038) else (namedLeaf039)))) else (if offset < 44 then (if offset < 42 then (if offset < 41 then (namedLeaf040) else (namedLeaf041)) else (if offset < 43 then (namedLeaf042) else (namedLeaf043))) else (if offset < 46 then (if offset < 45 then (namedLeaf044) else (namedLeaf045)) else (if offset < 47 then (namedLeaf046) else (namedLeaf047))))) else (if offset < 56 then (if offset < 52 then (if offset < 50 then (if offset < 49 then (namedLeaf048) else (namedLeaf049)) else (if offset < 51 then (namedLeaf050) else (namedLeaf051))) else (if offset < 54 then (if offset < 53 then (namedLeaf052) else (namedLeaf053)) else (if offset < 55 then (namedLeaf054) else (namedLeaf055)))) else (if offset < 60 then (if offset < 58 then (if offset < 57 then (namedLeaf056) else (namedLeaf057)) else (if offset < 59 then (namedLeaf058) else (namedLeaf059))) else (if offset < 62 then (if offset < 61 then (namedLeaf060) else (namedLeaf061)) else (if offset < 63 then (namedLeaf062) else (namedLeaf063))))))) else (if offset < 96 then (if offset < 80 then (if offset < 72 then (if offset < 68 then (if offset < 66 then (if offset < 65 then (namedLeaf064) else (namedLeaf065)) else (if offset < 67 then (namedLeaf066) else (namedLeaf067))) else (if offset < 70 then (if offset < 69 then (namedLeaf068) else (namedLeaf069)) else (if offset < 71 then (namedLeaf070) else (namedLeaf071)))) else (if offset < 76 then (if offset < 74 then (if offset < 73 then (namedLeaf072) else (namedLeaf073)) else (if offset < 75 then (namedLeaf074) else (namedLeaf075))) else (if offset < 78 then (if offset < 77 then (namedLeaf076) else (namedLeaf077)) else (if offset < 79 then (namedLeaf078) else (namedLeaf079))))) else (if offset < 88 then (if offset < 84 then (if offset < 82 then (if offset < 81 then (namedLeaf080) else (namedLeaf081)) else (if offset < 83 then (namedLeaf082) else (namedLeaf083))) else (if offset < 86 then (if offset < 85 then (namedLeaf084) else (namedLeaf085)) else (if offset < 87 then (namedLeaf086) else (namedLeaf087)))) else (if offset < 92 then (if offset < 90 then (if offset < 89 then (namedLeaf088) else (namedLeaf089)) else (if offset < 91 then (namedLeaf090) else (namedLeaf091))) else (if offset < 94 then (if offset < 93 then (namedLeaf092) else (namedLeaf093)) else (if offset < 95 then (namedLeaf094) else (namedLeaf095)))))) else (if offset < 112 then (if offset < 104 then (if offset < 100 then (if offset < 98 then (if offset < 97 then (namedLeaf096) else (namedLeaf097)) else (if offset < 99 then (namedLeaf098) else (namedLeaf099))) else (if offset < 102 then (if offset < 101 then (namedLeaf100) else (namedLeaf101)) else (if offset < 103 then (namedLeaf102) else (namedLeaf103)))) else (if offset < 108 then (if offset < 106 then (if offset < 105 then (namedLeaf104) else (namedLeaf105)) else (if offset < 107 then (namedLeaf106) else (namedLeaf107))) else (if offset < 110 then (if offset < 109 then (namedLeaf108) else (namedLeaf109)) else (if offset < 111 then (namedLeaf110) else (namedLeaf111))))) else (if offset < 120 then (if offset < 116 then (if offset < 114 then (if offset < 113 then (namedLeaf112) else (namedLeaf113)) else (if offset < 115 then (namedLeaf114) else (namedLeaf115))) else (if offset < 118 then (if offset < 117 then (namedLeaf116) else (namedLeaf117)) else (if offset < 119 then (namedLeaf118) else (namedLeaf119)))) else (if offset < 124 then (if offset < 122 then (if offset < 121 then (namedLeaf120) else (namedLeaf121)) else (if offset < 123 then (namedLeaf122) else (namedLeaf123))) else (if offset < 126 then (if offset < 125 then (namedLeaf124) else (namedLeaf125)) else (if offset < 127 then (namedLeaf126) else (namedLeaf127)))))))) else fallback

theorem point_checked (j : Fin 128) :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 (5376 + j.val))) (lookup j.val) = true := by
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

theorem correct (id : Fin 24698) (hlow : 5376 ≤ id.val) (hhigh : id.val < 5504) :
    leafCheck library (N4R2WordTree.catalog id) (lookup (id.val - 5376)) = true := by
  let j : Fin 128 := ⟨id.val - 5376, by omega⟩
  have hsum : 5376 + j.val = id.val := by dsimp [j]; omega
  have hindex : Fin.ofNat 24698 (5376 + j.val) = id := by
    apply Fin.ext
    simp only [Fin.ofNat, hsum, Nat.mod_eq_of_lt id.isLt]
  have hh := point_checked j
  rw [hindex] at hh
  exact hh

#print axioms point_checked
#print axioms correct
end Jsp404.N4R2OuterLeftData.LeafShard042
