import Jsp000404.N4R2OuterLeftReplay
import Jsp000404.N4R2WordCatalog

set_option autoImplicit false
set_option pp.fullNames true
set_option maxRecDepth 8192
set_option maxHeartbeats 0
set_option Elab.async false

namespace Jsp404.N4R2OuterLeftData.LeafShard000
open N4R2OuterLeftReplay

-- Cycle fingerprint 0087fe0cde3eed79a39807dc9c7deb6e9f930a4fc59d26b62512cddafad3c739.
def localCycle00000 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 3, .distance 1 2, .distance 0 1, .theta 1, .zero, .theta 3, .distance 2 3, .distance 3 6, .distance 1 6, .distance 1 4, .distance 1 3]
    constant := ![0, -1, -2, 0, 0, 3, -1, 0, -2, 0]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![true, false, false, false, false, false, false, false, false, true] }
  origin := ![.triangle 15 1, .triangle 0 0, .gapLower 1 0, .thetaLower 1, .thetaUpper 3, .corridorUpper 2 3, .triangle 27 0, .gapLower 6 2, .gapLower 1 5, .triangle 19 1]

-- Cycle fingerprint 012b9ffa2f694b10800abc233b2b0065137d695b58a595975dc814765443b13a.
def localCycle00001 : Cycle where
  length := 11
  data := {
    node := ![.theta 1, .zero, .theta 3, .distance 2 3, .distance 3 5, .distance 3 6, .distance 1 6, .distance 1 4, .distance 1 3, .distance 1 2, .distance 0 1, .theta 1]
    constant := ![0, 0, 3, -1, 0, 0, -2, 0, 0, -1, -2]
    coefficient := ![0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, true, true, false, false] }
  origin := ![.thetaLower 1, .thetaUpper 3, .corridorUpper 2 3, .triangle 26 0, .triangle 33 2, .gapLower 6 3, .gapLower 1 4, .triangle 19 1, .triangle 15 1, .triangle 0 0, .gapLower 1 0]

-- Cycle fingerprint 012caebf3fc5ee0b062d7f8a2869f5abb5a27f231d963b8aaa5bdeda199a55d1.
def localCycle00002 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 4, .distance 4 5, .distance 2 4, .distance 2 3, .distance 1 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, -1, -1, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, true, false, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 0, .triangle 31 0, .triangle 28 0, .triangle 25 1, .triangle 15 0, .triangle 0 0, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint 01d0d25c9a65b30ca34b756a8a7a155d965f3c652930760f56a70e7523d64a03.
def localCycle00003 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 2, .distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 3 5, .distance 3 6, .distance 1 6, .distance 1 4, .distance 1 2]
    constant := ![-2, -1, 0, 0, 3, -1, 0, 0, -2, 0]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, true, false, true] }
  origin := ![.gapLower 1 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 26 0, .triangle 33 2, .triangle 21 2, .gapLower 1 4, .triangle 16 1]

-- Cycle fingerprint 02639423485bf2743bc63ac7b8e06ee7d1b88be8aaf9c3b54651b460196b32d8.
def localCycle00004 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 2 3, .distance 3 4, .distance 4 5, .distance 1 4, .distance 1 3, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, 0, -1, -1, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, false, true, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 27 0, .triangle 25 0, .triangle 31 0, .triangle 22 0, .triangle 19 1, .triangle 1 0, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint 02dd4e0e3fb02433eb9c007a8eac8da91c0790df0ecfb8770f11c6040be74cd5.
def localCycle00005 : Cycle where
  length := 4
  data := {
    node := ![.distance 1 4, .distance 1 5, .distance 5 6, .distance 4 6, .distance 1 4]
    constant := ![-3, -1, 0, 2]
    coefficient := ![0, 0, 0, 0]
    strict := ![false, false, true, true] }
  origin := ![.gapLower 1 5, .triangle 24 0, .triangle 34 2, .gapUpper 4 3]

-- Cycle fingerprint 05144428d8d666dab3e22de4af3c91728d46033ecbc47119b3ac4fb7b0313e8b.
def localCycle00006 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 2 4, .distance 1 4, .distance 1 5, .distance 1 6, .distance 1 3, .distance 1 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, 0, 0, 0, -2, -2, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, true, true, false, false, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 16 2, .triangle 22 2, .triangle 24 2, .gapLower 1 3, .gapLower 1 2, .triangle 0 0, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint 0711e128e426893115e7ba88dd472024711f6569bfa17cf59f02da2bab5aa25f.
def localCycle00007 : Cycle where
  length := 11
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 2 4, .distance 2 5, .distance 5 6, .distance 3 5, .distance 1 3, .distance 1 2, .distance 0 1]
    constant := ![-1, 0, 0, 3, 0, 0, -1, -1, -1, 0, -1]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, false, false, false, false, false] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 25 2, .triangle 28 2, .triangle 30 0, .triangle 33 0, .triangle 20 0, .gapLower 1 2, .triangle 0 0]

-- Cycle fingerprint 08028d6301beb373a0576aa290d8af5a4318eeedbd12cb7284e6e8f341359091.
def localCycle00008 : Cycle where
  length := 11
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 3 5, .distance 5 6, .distance 1 5, .distance 1 4, .distance 1 3, .distance 1 2, .distance 0 1]
    constant := ![-1, 0, 0, 3, -1, -1, -1, 0, 0, 0, -1]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, true, true, true, false] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 26 0, .triangle 33 0, .triangle 24 0, .triangle 22 1, .triangle 19 1, .triangle 15 1, .triangle 0 0]

-- Cycle fingerprint 08f1fcb5a9aa3b41004071ed9de7e6586d58eebd57fca328fff3e186737496ff.
def localCycle00009 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 4, .distance 4 6, .distance 2 4, .distance 2 3, .distance 1 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, -1, -1, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 0, .triangle 32 0, .triangle 29 0, .gapLower 2 3, .triangle 15 0, .triangle 0 0, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint 0960a777e6a0f8ed64280dc50e8ce9a35186a3997b732c0fb82adab7b1b14aaf.
def localCycle00010 : Cycle where
  length := 5
  data := {
    node := ![.distance 1 2, .distance 2 5, .distance 3 5, .distance 1 5, .distance 1 3, .distance 1 2]
    constant := ![2, 0, 0, -3, 0]
    coefficient := ![0, 0, 0, 0, 0]
    strict := ![true, false, false, false, true] }
  origin := ![.gapUpper 2 2, .gapLower 5 4, .gapLower 5 3, .gapLower 1 3, .triangle 15 1]

-- Cycle fingerprint 09dfa431ee781f51624bfc8227f5a650a6db90644b248ac862210637f084d462.
def localCycle00011 : Cycle where
  length := 4
  data := {
    node := ![.distance 1 5, .distance 1 3, .distance 1 2, .distance 2 5, .distance 1 5]
    constant := ![-2, -2, 2, 0]
    coefficient := ![0, 0, 0, 0]
    strict := ![false, false, true, true] }
  origin := ![.gapLower 1 3, .gapLower 1 2, .gapUpper 2 2, .triangle 17 2]

-- Cycle fingerprint 0b6118ca521b3333b2e9b58d5e7f63859cfa58d59d77212969336474d16d3344.
def localCycle00012 : Cycle where
  length := 12
  data := {
    node := ![.distance 4 5, .distance 5 6, .distance 0 5, .distance 0 4, .distance 0 1, .theta 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 2 4, .distance 1 4, .distance 4 5]
    constant := ![-1, -1, 0, 0, -3, 0, 0, 0, 3, 0, 0, -1]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, true, false, true, false, false, false, true, true, false] }
  origin := ![.triangle 34 0, .triangle 14 0, .gapLower 0 4, .triangle 2 1, .gapLower 1 0, .thetaNext 0, .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 16 2, .triangle 22 0]

-- Cycle fingerprint 0cacf45b6b3ac5a6a02f0ab15b68ecdb4bfc6278ae9c60de1ecad593a1a9403d.
def localCycle00013 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 2 4, .distance 4 6, .distance 3 4, .distance 4 5, .distance 1 4, .distance 0 4, .distance 0 3, .theta 3]
    constant := ![3, 0, -1, -1, -1, -1, 0, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, true, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 25 2, .triangle 29 0, .triangle 32 0, .triangle 31 0, .triangle 22 0, .triangle 2 2, .triangle 9 1, .gapLower 3 0]

-- Cycle fingerprint 0dd53a06eb96521307c049749c81a25f40d2df9ba743c884f1278300be48dd6f.
def localCycle00014 : Cycle where
  length := 11
  data := {
    node := ![.theta 0, .zero, .theta 4, .distance 3 4, .distance 2 3, .distance 3 5, .distance 4 5, .distance 5 6, .distance 1 5, .distance 1 4, .distance 0 1, .theta 0]
    constant := ![0, 0, 3, -1, -1, 0, -1, -1, 0, -1, -1]
    coefficient := ![0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, false, false, false, false] }
  origin := ![.thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 25 0, .triangle 26 0, .triangle 31 1, .triangle 34 0, .triangle 24 0, .gapLower 1 4, .triangle 2 0, .corridorLower 0 1]

-- Cycle fingerprint 0e45493ef43cbda19f96b9ec7c590f5c837f2e6bc3b6c9da5d35728e5ece6119.
def localCycle00015 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 2, .distance 0 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 2 4, .distance 2 5, .distance 1 5, .distance 1 6, .distance 1 2]
    constant := ![-2, -1, 0, 0, 3, 0, 0, 0, -2, 0]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, true, false, true] }
  origin := ![.gapLower 1 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 28 2, .triangle 17 2, .gapLower 1 4, .triangle 18 1]

-- Cycle fingerprint 1137b8546bc230d4b6e7b9431b2ed672fa4199d3daa20ba449d74dd189617831.
def localCycle00016 : Cycle where
  length := 8
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 4, .distance 2 3, .distance 3 6, .distance 4 6, .distance 1 6, .distance 5 6, .theta 5]
    constant := ![3, -1, -1, -1, 0, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, true, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 0, .triangle 25 0, .triangle 27 0, .triangle 32 1, .triangle 23 2, .triangle 24 1, .corridorLower 5 6]

-- Cycle fingerprint 122a8b6b0420c5228fdaf2f64fa772ce6c404cbcb9600661b2c6932281a0c202.
def localCycle00017 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 3, .distance 1 2, .distance 0 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 1 3]
    constant := ![-2, -2, -1, 0, 0, 3, -1]
    coefficient := ![0, 0, 0, 0, 1, 1, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 1 2, .gapLower 1 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 19 0]

-- Cycle fingerprint 12508423f527ef03f2bb502e8263e90449b457609ee0bc9b9a5ee4b6e865a8ea.
def localCycle00018 : Cycle where
  length := 5
  data := {
    node := ![.distance 5 6, .distance 4 6, .distance 1 4, .distance 1 5, .distance 1 6, .distance 5 6]
    constant := ![0, 2, 0, -2, 0]
    coefficient := ![0, 0, 0, 0, 0]
    strict := ![true, true, true, false, true] }
  origin := ![.triangle 34 2, .gapUpper 4 3, .triangle 22 2, .gapLower 1 4, .triangle 24 1]

-- Cycle fingerprint 139dab53ea9e44d919331bbc6ecf512b2358edefbafcae1b147f41932849a9a4.
def localCycle00019 : Cycle where
  length := 11
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 4 5, .distance 4 6, .distance 1 4, .distance 1 3, .distance 1 2, .distance 0 1, .theta 1, .zero, .theta 4]
    constant := ![3, 0, -1, 0, -1, 0, -2, -1, -2, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, false, true, false, false, false, false, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 28 0, .triangle 34 2, .triangle 23 0, .gapLower 1 3, .gapLower 1 2, .triangle 0 0, .gapLower 1 0, .thetaLower 1, .thetaUpper 4]

-- Cycle fingerprint 13e46ed3e757c5b38599cfa0f0d52628f9d2198742958780285756d6ed3221f0.
def localCycle00020 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 3, .distance 1 2, .distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 3 6, .distance 3 4, .distance 1 3]
    constant := ![0, -3, -1, 0, 0, 3, -1, 0, -1]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, true, false] }
  origin := ![.gapLower 1 2, .gapLower 1 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 27 0, .triangle 32 1, .triangle 19 0]

-- Cycle fingerprint 14a9803b9e46a0c197c433a93b04d45c24fc5e635258914fea426660d63fbff4.
def localCycle00021 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 4, .distance 4 6, .distance 1 4, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true] }
  origin := ![.corridorUpper 2 3, .triangle 25 0, .triangle 32 0, .triangle 23 0, .triangle 22 0, .corridorLower 4 5, .thetaNext 3]

-- Cycle fingerprint 14b83cea571525354e826ac0b9dfecc42e6a20d045f32269823a65afd68df441.
def localCycle00022 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 2, .distance 0 1, .theta 0, .zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 3, .distance 3 4, .distance 1 3, .distance 1 2]
    constant := ![-1, -1, 0, 0, 3, 0, -1, -1, -1, 0]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, false, false, false] }
  origin := ![.triangle 0 0, .corridorLower 0 1, .thetaLower 0, .thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 0, .triangle 25 0, .triangle 19 0, .gapLower 1 2]

-- Cycle fingerprint 17ceed8de7b44f004975b66118a91f5937a8fa4e701cc0070f9e7b68b9ef6d56.
def localCycle00023 : Cycle where
  length := 6
  data := {
    node := ![.distance 1 5, .distance 1 6, .distance 1 3, .distance 1 2, .theta 1, .distance 1 4, .distance 1 5]
    constant := ![0, -2, 0, -1, 2, 0]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![true, false, true, false, false, true] }
  origin := ![.triangle 24 2, .gapLower 1 3, .triangle 15 1, .corridorLower 1 2, .gapLower 1 6, .triangle 22 2]

-- Cycle fingerprint 189e133cedf6d100398a39ff47f2f398e37476d747ca18618410f2d5823701ce.
def localCycle00024 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 3, .distance 3 6, .distance 4 6, .distance 1 4, .distance 4 5, .theta 4]
    constant := ![3, -1, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 0, .triangle 27 0, .triangle 32 1, .triangle 23 0, .triangle 22 0, .corridorLower 4 5]

-- Cycle fingerprint 195801ab2b0a79c9fcd719e67580c9633925eacfa2b046c686042a78d999db7c.
def localCycle00025 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 2 4, .distance 4 5, .distance 4 6, .distance 1 6, .distance 1 4, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, -1, 0, 0, -2, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, true, false, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 28 0, .triangle 34 2, .triangle 23 2, .gapLower 1 4, .triangle 2 0, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint 1a6d98d9d94c2f2163ea11a4d1cf6fcdc3be6b1d2646327f6266eaceeb456c45.
def localCycle00026 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 4, .distance 3 6, .distance 1 6, .distance 1 5, .distance 0 5, .distance 0 3, .theta 3]
    constant := ![3, -1, 0, 0, -3, 0, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, true, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 25 0, .triangle 32 2, .triangle 21 2, .gapLower 1 4, .triangle 3 2, .triangle 10 1, .gapLower 3 0]

-- Cycle fingerprint 1b4a7dc46251110106c2099ab43791da838b5e70ddfaca32c0c411a45b946657.
def localCycle00027 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 4 6, .distance 2 4, .distance 2 3, .distance 3 5, .distance 4 5, .distance 1 4, .distance 1 3, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, -1, -1, 0, -1, 0, -1, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, true, false, true, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 32 0, .triangle 29 0, .triangle 25 1, .triangle 26 0, .triangle 31 1, .triangle 22 0, .triangle 19 1, .triangle 1 0, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint 1de52e7982a6b76571e664ad5c40c8e9c3aadd3ce4175b0239449de135979460.
def localCycle00028 : Cycle where
  length := 9
  data := {
    node := ![.distance 3 6, .distance 1 6, .distance 1 4, .distance 1 5, .distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 3 6]
    constant := ![0, -2, -2, -1, -1, 0, 0, 3, -1]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![false, false, false, false, false, false, false, false, false] }
  origin := ![.gapLower 6 2, .gapLower 1 5, .gapLower 1 4, .triangle 3 0, .corridorLower 0 1, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 27 0]

-- Cycle fingerprint 1e2da3e605511ee24289aeedcd0037e995397dbd9deb0de7ac8bbcad5966ba99.
def localCycle00029 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 3, .distance 3 6, .distance 3 4, .distance 1 3, .distance 1 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, -1, -1, 0, -1, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, false, true, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 0, .triangle 27 0, .triangle 32 1, .triangle 19 0, .triangle 15 1, .triangle 0 0, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint 1ed93f73d17490701f8e3c9c777789fe6d62a0ddc29d222c53cd6538fa77f610.
def localCycle00030 : Cycle where
  length := 6
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 4 6, .distance 1 4, .distance 4 5, .theta 4]
    constant := ![3, 0, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 29 0, .triangle 23 0, .triangle 22 0, .corridorLower 4 5]

-- Cycle fingerprint 21920a17c5e94ed5a23a25b11ab5384a66bf1075c6dedfc8c063a2af3b46649b.
def localCycle00031 : Cycle where
  length := 4
  data := {
    node := ![.distance 2 4, .distance 3 4, .distance 1 3, .distance 1 2, .distance 2 4]
    constant := ![0, -1, -2, 2]
    coefficient := ![0, 0, 0, 0]
    strict := ![false, false, false, true] }
  origin := ![.gapLower 4 3, .triangle 19 0, .gapLower 1 2, .gapUpper 2 2]

-- Cycle fingerprint 226d9f0a4b48fec9277d9ec102170239f895acd558d0ec55d29452db6d385a4e.
def localCycle00032 : Cycle where
  length := 9
  data := {
    node := ![.distance 3 5, .distance 1 5, .distance 1 6, .distance 1 4, .distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 3 5]
    constant := ![0, -2, -2, -1, -1, 0, 0, 3, -1]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![false, false, false, false, false, false, false, false, false] }
  origin := ![.gapLower 5 3, .gapLower 1 5, .gapLower 1 4, .triangle 2 0, .corridorLower 0 1, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 26 0]

-- Cycle fingerprint 229210a148f78e976ebeb8e84af4505e350ec8c3fbe187c260838e25e7dc9c01.
def localCycle00033 : Cycle where
  length := 11
  data := {
    node := ![.distance 2 3, .distance 2 5, .distance 5 6, .distance 3 5, .distance 1 3, .distance 1 2, .distance 0 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 2 3]
    constant := ![0, -1, -1, -1, 0, -1, -1, 0, 0, 3, -1]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![true, false, false, false, false, false, false, false, false, false, false] }
  origin := ![.triangle 26 2, .triangle 30 0, .triangle 33 0, .triangle 20 0, .gapLower 1 2, .triangle 0 0, .corridorLower 0 1, .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 25 0]

-- Cycle fingerprint 235237ae1fa971193162c7f5ee56d12badb500544ee83a0e241876807c593b38.
def localCycle00034 : Cycle where
  length := 9
  data := {
    node := ![.distance 2 4, .distance 1 4, .distance 1 6, .distance 1 5, .distance 0 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 2 4]
    constant := ![0, -2, -2, -1, -1, 0, 0, 3, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![true, false, false, false, false, false, false, false, true] }
  origin := ![.triangle 16 2, .gapLower 1 5, .gapLower 1 4, .triangle 3 0, .corridorLower 0 1, .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 25 2]

-- Cycle fingerprint 2709d24a8e1c12fc362072acba18ad7c8a48731c96bbdfd4ae37eaf651fda87b.
def localCycle00035 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 3, .distance 1 2, .distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 3 5, .distance 3 4, .distance 1 3]
    constant := ![0, -3, -1, 0, 0, 3, -1, 0, -1]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, true, false] }
  origin := ![.gapLower 1 2, .gapLower 1 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 26 0, .triangle 31 1, .triangle 19 0]

-- Cycle fingerprint 273ce57af3e29b59ebe281d36d0569ec8d9d62aa98e564d4ef88c5b18eb7813f.
def localCycle00036 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 2, .distance 0 1, .theta 1, .zero, .theta 4, .distance 3 4, .distance 2 3, .distance 1 2]
    constant := ![-2, -2, 0, 0, 3, -1, -1]
    coefficient := ![0, 0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 1 1, .gapLower 1 0, .thetaLower 1, .thetaUpper 4, .corridorUpper 3 4, .triangle 25 0, .triangle 15 0]

-- Cycle fingerprint 28788793aacb7de68ce36618ee27ae2b95f73c6500659b2e83ac12273b5fd013.
def localCycle00037 : Cycle where
  length := 3
  data := {
    node := ![.distance 4 6, .distance 1 6, .distance 1 4, .distance 4 6]
    constant := ![0, -3, 2]
    coefficient := ![0, 0, 0]
    strict := ![false, false, true] }
  origin := ![.gapLower 6 3, .gapLower 1 4, .gapUpper 4 2]

-- Cycle fingerprint 29634891d6e3fe04c6d66dddc4e94194fd01e4df9ef38debbe759f4f0bc779bf.
def localCycle00038 : Cycle where
  length := 9
  data := {
    node := ![.distance 3 4, .distance 1 3, .distance 1 2, .distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 3 5, .distance 3 4]
    constant := ![-1, -2, -2, -1, 0, 0, 3, -1, 0]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, false, false, false, false, false, true] }
  origin := ![.triangle 19 0, .gapLower 1 2, .gapLower 1 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 26 0, .triangle 31 1]

-- Cycle fingerprint 2a18478105fb9fb7c482cd2a96633f32d3e7a217266ac9d91ae0ffd8f786cb9f.
def localCycle00039 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 4 6, .distance 4 5, .distance 2 4, .distance 2 3, .distance 1 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, -1, 0, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true, false, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 32 0, .triangle 34 1, .triangle 28 0, .triangle 25 1, .triangle 15 0, .triangle 0 0, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint 2a59bbc2e15203f856fc8dd7430a23cc890d999084e8e7a5f958513fdf5b5c2a.
def localCycle00040 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 2, .distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 3 4, .distance 3 6, .distance 1 6, .distance 1 5, .distance 1 2]
    constant := ![-2, -1, 0, 0, 3, -1, 0, 0, -2, 0]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, true, false, true] }
  origin := ![.gapLower 1 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 25 0, .triangle 32 2, .triangle 21 2, .gapLower 1 4, .triangle 17 1]

-- Cycle fingerprint 2c7f78484fcc0139503e54d32a58fad68c73a3efe43970127a26315582f3ad09.
def localCycle00041 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 4 6, .distance 3 6, .distance 2 3, .distance 3 5, .distance 3 4, .distance 1 3, .distance 1 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, 0, -1, -1, 0, -1, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, true, false, true, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 34 2, .triangle 32 2, .triangle 27 0, .triangle 26 0, .triangle 31 1, .triangle 19 0, .triangle 15 1, .triangle 0 0, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint 2c994e5e73bdcfcc0d66c2ce87f1e6c585a5ffb8ca9a18b0635f37c1dd34dbb7.
def localCycle00042 : Cycle where
  length := 5
  data := {
    node := ![.distance 2 3, .distance 2 4, .distance 4 5, .distance 5 6, .distance 3 6, .distance 2 3]
    constant := ![0, -1, -1, 0, 2]
    coefficient := ![0, 0, 0, 0, 0]
    strict := ![true, false, false, true, true] }
  origin := ![.triangle 25 2, .triangle 28 0, .triangle 34 0, .triangle 33 2, .gapUpper 3 5]

-- Cycle fingerprint 2d163de0ab30f517dcb15f85992466b4f3f67629afcb57203176a18078912717.
def localCycle00043 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 2 4, .distance 4 5, .distance 3 4, .distance 1 3, .distance 1 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, -1, -1, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, true, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 29 0, .triangle 28 0, .triangle 31 0, .triangle 19 0, .triangle 15 1, .triangle 0 0, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint 2e0e8c8d38814d1a0d11fd33863a0b53a9edbc0a76868f3e02fd56fcfb87587a.
def localCycle00044 : Cycle where
  length := 3
  data := {
    node := ![.distance 5 6, .distance 1 6, .distance 1 5, .distance 5 6]
    constant := ![0, -3, 2]
    coefficient := ![0, 0, 0]
    strict := ![false, false, true] }
  origin := ![.gapLower 6 3, .gapLower 1 4, .gapUpper 5 3]

-- Cycle fingerprint 2e271486661274e1a7c299405a1677a34c17366877ff18a8db97452392c64329.
def localCycle00045 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 2 4, .distance 4 5, .distance 4 6, .distance 1 4, .distance 1 3, .distance 0 1]
    constant := ![-1, 0, 0, 3, 0, -1, 0, -1, -3, -1]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, true, false, false, false] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 28 0, .triangle 34 2, .triangle 23 0, .gapLower 1 3, .triangle 1 0]

-- Cycle fingerprint 2f55950e43b0fe401e4c284a2c7c35f360362e110364235a21da250ff4121a65.
def localCycle00046 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 3 5, .distance 2 3, .distance 1 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 33 0, .triangle 26 0, .triangle 15 0, .triangle 0 0, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint 300545d8f82410601223935dcd57d1a1bf7915e0d61513164dbce729a1c06761.
def localCycle00047 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 2 3, .distance 3 5, .distance 4 5, .distance 1 4, .distance 1 3, .distance 1 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, -1, -1, 0, -1, 0, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, true, true, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 25 0, .triangle 26 0, .triangle 31 1, .triangle 22 0, .triangle 19 1, .triangle 15 1, .triangle 0 0, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint 328b347d031e74fd4f806662c1b096a667df60a53653bc9d511abcebf8999ae3.
def localCycle00048 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 4, .distance 3 6, .distance 2 3, .distance 1 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, -1, 0, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 0, .triangle 32 2, .triangle 27 0, .triangle 15 0, .triangle 0 0, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint 329003f79c053100348d69674c1da371af934bfe0fc74ce50fe11a0663591268.
def localCycle00049 : Cycle where
  length := 6
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 2 3, .distance 2 6, .theta 6, .theta 5]
    constant := ![3, 0, -1, 0, -2, 0]
    coefficient := ![1, 0, 0, 0, -1, 0]
    strict := ![false, true, false, true, true, true] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 26 0, .triangle 27 2, .gapUpper 6 6, .thetaNext 5]

-- Cycle fingerprint 33269564ce4201f717310950b9f0f36726ee96227190ed97c6e10336e9ff4da0.
def localCycle00050 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 2 4, .distance 2 5, .distance 2 6, .distance 1 6, .distance 1 3, .distance 0 1]
    constant := ![-1, 0, 0, 3, 0, 0, 0, 0, -3, -1]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, true, true, false, false] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 28 2, .triangle 30 2, .triangle 18 2, .gapLower 1 3, .triangle 1 0]

-- Cycle fingerprint 332cc52b7029845fffd531f30bd5044cef76231465d7003a6fea911e467a4710.
def localCycle00051 : Cycle where
  length := 6
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 3, .distance 3 5, .distance 5 6, .distance 4 5, .theta 4]
    constant := ![3, -1, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 0, .triangle 26 0, .triangle 33 0, .triangle 34 0, .corridorLower 4 5]

-- Cycle fingerprint 339fa3904dac64145b68baab64060de31f155a0ad3eee6d8a3998b66ce63cc22.
def localCycle00052 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 3 5, .distance 5 6, .distance 4 5, .distance 1 4, .distance 1 3, .distance 1 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, -1, -1, -1, 0, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, true, true, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 31 2, .triangle 33 0, .triangle 34 0, .triangle 22 0, .triangle 19 1, .triangle 15 1, .triangle 0 0, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint 33defca39a4e1123e6074f6753debdec36127430753a99725b7f446429f5e76f.
def localCycle00053 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 2, .theta 1, .distance 1 4, .distance 4 5, .distance 5 6, .distance 0 5, .distance 0 4, .distance 0 3, .distance 1 3, .distance 1 2]
    constant := ![-1, 2, -1, -1, -1, 0, 0, 2, -2]
    coefficient := ![0, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, true, false] }
  origin := ![.corridorLower 1 2, .gapLower 1 6, .triangle 22 0, .triangle 34 0, .triangle 14 0, .gapLower 0 4, .triangle 9 1, .gapUpper 3 1, .gapLower 1 2]

-- Cycle fingerprint 3589e22d1251e85e207711531ae8b200cef8913e73a5c3b9e684617c2f8c2ccf.
def localCycle00054 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 3, .distance 1 2, .distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 3 6, .distance 3 4, .distance 1 3]
    constant := ![0, -2, -1, 0, 0, 3, -1, 0, -1]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, true, false] }
  origin := ![.gapLower 1 2, .gapLower 1 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 27 0, .triangle 32 1, .triangle 19 0]

-- Cycle fingerprint 35c49055c77d0371616ebeb7f7de0a73d98e8ff1e6d5ba9e5bc8f32a413060cc.
def localCycle00055 : Cycle where
  length := 12
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 4 5, .distance 5 6, .distance 1 5, .distance 1 4, .distance 1 3, .distance 1 2, .distance 0 1, .theta 0, .zero, .theta 4]
    constant := ![3, 0, -1, -1, -1, 0, 0, 0, -1, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, false, false, false, true, true, true, false, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 28 0, .triangle 34 0, .triangle 24 0, .triangle 22 1, .triangle 19 1, .triangle 15 1, .triangle 0 0, .corridorLower 0 1, .thetaLower 0, .thetaUpper 4]

-- Cycle fingerprint 36b3bada88c33f5ba037fc3ebb030d250c383c7b458a5333466f5d38289dcb56.
def localCycle00056 : Cycle where
  length := 10
  data := {
    node := ![.theta 0, .zero, .theta 3, .distance 2 3, .distance 3 4, .distance 3 6, .distance 3 5, .distance 1 3, .distance 1 2, .distance 0 1, .theta 0]
    constant := ![0, 0, 3, -1, 0, 0, -1, 0, -2, -1]
    coefficient := ![0, 1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, false, false, false, false] }
  origin := ![.thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 25 0, .triangle 32 2, .triangle 33 1, .triangle 20 0, .gapLower 1 2, .gapLower 1 1, .corridorLower 0 1]

-- Cycle fingerprint 36c65a35219d39d53bbbdaa147e4b6bd75cf35a675142729e75cc1aa55bcdf9b.
def localCycle00057 : Cycle where
  length := 12
  data := {
    node := ![.distance 2 4, .distance 4 5, .distance 3 4, .distance 4 6, .distance 5 6, .distance 1 5, .distance 1 4, .distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 2 4]
    constant := ![-1, -1, -1, 0, -1, 0, -1, -1, 0, 0, 3, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![false, false, false, true, false, false, false, false, false, false, false, true] }
  origin := ![.triangle 28 0, .triangle 31 0, .triangle 32 0, .triangle 34 1, .triangle 24 0, .gapLower 1 4, .triangle 2 0, .corridorLower 0 1, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 25 2]

-- Cycle fingerprint 39bf04a3d9d4a8ab5499a867ab855bf2ffdd615f4acc0ac7578f67e14ecb5b0f.
def localCycle00058 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 4 5, .distance 5 6, .distance 2 5, .distance 2 4, .distance 2 3, .distance 1 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, -1, -1, -1, 0, 0, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, false, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 31 0, .triangle 34 0, .triangle 30 0, .gapLower 2 4, .triangle 25 1, .triangle 15 0, .triangle 0 0, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint 3b222e7139f8c2a7941a4dbcd87b189788ca42c78a2fcf7f11de9a3bc809f3f4.
def localCycle00059 : Cycle where
  length := 13
  data := {
    node := ![.distance 0 4, .distance 0 3, .distance 0 1, .theta 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 2 4, .distance 2 5, .distance 1 5, .distance 5 6, .distance 4 5, .distance 0 4]
    constant := ![0, 0, -3, 0, 0, 0, 3, 0, 0, 0, -1, -1, -1]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, false, true, true, true, false, false, false] }
  origin := ![.gapLower 0 3, .triangle 1 1, .gapLower 1 0, .thetaNext 0, .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 28 2, .triangle 17 2, .triangle 24 0, .triangle 34 0, .triangle 12 0]

-- Cycle fingerprint 3c7ce17d602a9b0ebcce1d56bf7de1d5c64048bf60704cb0b4f81ac9301b8412.
def localCycle00060 : Cycle where
  length := 12
  data := {
    node := ![.distance 5 6, .distance 1 5, .distance 1 4, .distance 0 1, .theta 0, .zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 3, .distance 3 4, .distance 4 6, .distance 5 6]
    constant := ![-1, 0, -1, -1, 0, 0, 3, 0, -1, -1, -1, 0]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, true, false, false, false, true] }
  origin := ![.triangle 24 0, .gapLower 1 4, .triangle 2 0, .corridorLower 0 1, .thetaLower 0, .thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 0, .triangle 25 0, .triangle 32 0, .triangle 34 1]

-- Cycle fingerprint 3e7d2e8489854d09a23508825bd844df804ce8fbef2d092478b583b51ae4aa2c.
def localCycle00061 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 5, .distance 1 4, .distance 0 1, .theta 0, .zero, .theta 5, .distance 4 5, .distance 2 4, .distance 4 6, .distance 5 6, .distance 1 5]
    constant := ![0, -1, -1, 0, 0, 3, -1, -1, 0, -1]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false, true, false] }
  origin := ![.gapLower 1 4, .triangle 2 0, .corridorLower 0 1, .thetaLower 0, .thetaUpper 5, .corridorUpper 4 5, .triangle 28 0, .triangle 29 0, .triangle 34 1, .triangle 24 0]

-- Cycle fingerprint 3f0de987ee7ec2a7df53413973586ca15e21179d12b65b74f85c16cb454f600f.
def localCycle00062 : Cycle where
  length := 5
  data := {
    node := ![.distance 2 3, .distance 2 5, .distance 5 6, .distance 4 6, .distance 3 4, .distance 2 3]
    constant := ![0, 2, 0, -1, -1]
    coefficient := ![0, 0, 0, 0, 0]
    strict := ![true, true, true, false, false] }
  origin := ![.triangle 26 2, .gapUpper 5 5, .triangle 34 2, .triangle 32 0, .triangle 25 0]

-- Cycle fingerprint 3f69a9013e4220b05c689fd9347d6dd2a5d88c159954baa6248afeecbf9a9a98.
def localCycle00063 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 5 6, .distance 3 5, .distance 2 3, .distance 3 4, .distance 1 3, .distance 1 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, -1, -1, -1, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, true, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 34 0, .triangle 33 0, .triangle 26 0, .triangle 25 0, .triangle 19 0, .triangle 15 1, .triangle 0 0, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint 411cf94a90fcf69f3f7fd26c170fc9a8383bea0af4ba86a794a9f6e717607403.
def localCycle00064 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 4, .distance 2 3, .distance 1 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 0, .triangle 25 0, .triangle 15 0, .triangle 0 0, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint 426fdf46015497c4e9aeaec0a52ec29a3c094174273d753ab7b226c9c3391222.
def localCycle00065 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 2, .distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 2 4, .distance 4 6, .distance 3 4, .distance 1 3, .distance 1 2]
    constant := ![-1, -1, 0, 0, 3, 0, -1, -1, -1, 0]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, false, false, false] }
  origin := ![.triangle 0 0, .corridorLower 0 1, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 25 2, .triangle 29 0, .triangle 32 0, .triangle 19 0, .gapLower 1 2]

-- Cycle fingerprint 46b157eed94c04617dccd74d5f8919e60284156085af571ecd7b8d571ad5e1d0.
def localCycle00066 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 4 6, .distance 2 4, .distance 2 3, .distance 3 5, .distance 1 3, .distance 1 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, -1, -1, 0, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, true, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 32 0, .triangle 29 0, .triangle 25 1, .triangle 26 0, .triangle 20 0, .triangle 15 1, .triangle 0 0, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint 46d1309cfe7c3446e8586c1bc8c745eb516923d056c17cd3068605d2346b518c.
def localCycle00067 : Cycle where
  length := 5
  data := {
    node := ![.theta 4, .distance 2 4, .distance 4 5, .distance 3 4, .distance 4 6, .theta 4]
    constant := ![3, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false] }
  origin := ![.corridorUpper 2 4, .triangle 28 0, .triangle 31 0, .triangle 32 0, .corridorLower 4 6]

-- Cycle fingerprint 48231f6e96ee9b7534b50bf49ca52027e7b4914a18fc4117acd8104141a5aab8.
def localCycle00068 : Cycle where
  length := 11
  data := {
    node := ![.theta 1, .zero, .theta 4, .distance 3 4, .distance 2 4, .distance 1 4, .distance 1 5, .distance 1 6, .distance 1 3, .distance 1 2, .distance 0 1, .theta 1]
    constant := ![0, 0, 3, 0, 0, 0, -2, 0, 0, -1, -2]
    coefficient := ![0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, true, false, true, true, false, false] }
  origin := ![.thetaLower 1, .thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 16 2, .triangle 22 2, .gapLower 1 4, .triangle 21 1, .triangle 15 1, .triangle 0 0, .gapLower 1 0]

-- Cycle fingerprint 49d76a1e53c4f47669f546791abf96f3661e74e2332e155a3789b69d8c161fe5.
def localCycle00069 : Cycle where
  length := 11
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 4 5, .distance 4 6, .distance 1 4, .distance 1 3, .distance 1 2, .distance 0 1, .theta 0, .zero, .theta 4]
    constant := ![3, 0, -1, 0, -1, 0, -2, -1, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, false, true, false, false, false, false, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 28 0, .triangle 34 2, .triangle 23 0, .gapLower 1 3, .gapLower 1 2, .triangle 0 0, .corridorLower 0 1, .thetaLower 0, .thetaUpper 4]

-- Cycle fingerprint 4a2134621c1cba5e87c2bd8b07d1666deeae267af13bca443695115d7c50dc17.
def localCycle00070 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 3 5, .distance 5 6, .distance 4 6, .distance 2 4, .distance 4 5, .distance 1 4, .distance 1 3, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, -1, 0, -1, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false, false, true, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 31 2, .triangle 33 0, .triangle 34 2, .triangle 29 0, .triangle 28 0, .triangle 22 0, .triangle 19 1, .triangle 1 0, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint 4a8b7511af9aed04ccb83c85a95afb0af95a89bcff6ddcc327159e7fc88395ef.
def localCycle00071 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 4, .distance 2 3, .distance 1 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 0, .triangle 25 0, .triangle 15 0, .triangle 0 0, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint 4a8eb83437153330bb00a598ceb08aae277fd802faddcbcd2b91d36ce36fbf5d.
def localCycle00072 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 5, .distance 3 6, .distance 1 6, .distance 1 4, .distance 0 4, .distance 0 3, .theta 3]
    constant := ![3, -1, 0, 0, -3, 0, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, true, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 26 0, .triangle 33 2, .triangle 21 2, .gapLower 1 4, .triangle 2 2, .triangle 9 1, .gapLower 3 0]

-- Cycle fingerprint 4c5e2a48156997e79a9100136c5af051b0b5c4c21b3326383803b2d96dd3cdba.
def localCycle00073 : Cycle where
  length := 13
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 4 5, .distance 1 4, .distance 4 6, .distance 5 6, .distance 0 5, .distance 0 4, .distance 0 3, .distance 0 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, -1, -1, -1, 0, -1, 0, 0, 0, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, true, true, true, true, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 31 0, .triangle 22 0, .triangle 23 0, .triangle 34 1, .triangle 14 0, .triangle 12 1, .triangle 9 1, .triangle 5 1, .triangle 0 1, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint 4cc2d446cae32e20122eae613ab82617a556b225335140f239a4f3fb53c6b566.
def localCycle00074 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 3, .theta 3, .distance 2 3, .distance 3 6, .distance 1 6, .distance 1 4, .distance 4 5, .distance 0 4, .distance 0 3]
    constant := ![0, 3, -1, 0, -3, -1, 0, 0]
    coefficient := ![0, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.gapLower 3 0, .corridorUpper 2 3, .triangle 27 0, .gapLower 6 2, .gapLower 1 5, .triangle 22 0, .gapLower 4 1, .gapLower 0 3]

-- Cycle fingerprint 4d599a757a758831129bbcdde5188a9242e1a7a5ecf19eeb3696da9a22238c4b.
def localCycle00075 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 2 3, .distance 3 4, .distance 3 5, .distance 1 3, .distance 1 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, 0, -1, -1, 0, -1, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, true, false, true, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 27 0, .triangle 25 0, .triangle 31 2, .triangle 20 0, .triangle 15 1, .triangle 0 0, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint 4d9d2802d55dda1701433d18ea77e220084ef21f09cb7c7042f73409fbe8c704.
def localCycle00076 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 3 5, .distance 5 6, .distance 4 5, .distance 2 4, .distance 2 3, .distance 1 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, -1, -1, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, true, false, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 31 2, .triangle 33 0, .triangle 34 0, .triangle 28 0, .triangle 25 1, .triangle 15 0, .triangle 0 0, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint 4dbae53827f60865e11418fb88123458f7f5f69312ca05a5ed236e0e1317ed4f.
def localCycle00077 : Cycle where
  length := 11
  data := {
    node := ![.distance 3 4, .distance 2 4, .distance 4 5, .distance 4 6, .distance 1 4, .distance 1 3, .distance 0 1, .theta 1, .theta 0, .zero, .theta 4, .distance 3 4]
    constant := ![0, -1, 0, -1, 0, -1, -3, 0, 0, 0, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1]
    strict := ![true, false, true, false, false, false, false, true, false, false, false] }
  origin := ![.triangle 25 2, .triangle 28 0, .triangle 34 2, .triangle 23 0, .gapLower 1 3, .triangle 1 0, .gapLower 1 0, .thetaNext 0, .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4]

-- Cycle fingerprint 4e9b2629dfc8c9ff953721933d193803c15c22f521a4649e4c80c6a7f9e0f5b4.
def localCycle00078 : Cycle where
  length := 3
  data := {
    node := ![.distance 1 4, .theta 1, .distance 1 6, .distance 1 4]
    constant := ![-1, 2, -2]
    coefficient := ![0, 1, 0]
    strict := ![false, false, false] }
  origin := ![.corridorLower 1 4, .gapLower 1 6, .gapLower 1 5]

-- Cycle fingerprint 4f3477b0e34706af0cf0dfce9db4b5c58c8bf58a2ed91b303cc3640a173297d4.
def localCycle00079 : Cycle where
  length := 12
  data := {
    node := ![.distance 3 4, .distance 2 4, .distance 4 5, .distance 4 6, .distance 1 6, .distance 1 4, .distance 1 3, .distance 1 2, .distance 0 1, .theta 1, .zero, .theta 4, .distance 3 4]
    constant := ![0, -1, 0, 0, -2, 0, 0, -1, -2, 0, 0, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1]
    strict := ![true, false, true, false, false, true, true, false, false, false, false, false] }
  origin := ![.triangle 25 2, .triangle 28 0, .triangle 34 2, .gapLower 6 3, .gapLower 1 4, .triangle 19 1, .triangle 15 1, .triangle 0 0, .gapLower 1 0, .thetaLower 1, .thetaUpper 4, .corridorUpper 3 4]

-- Cycle fingerprint 500a1b7422a7ef0ed28c7fc9b6c202f4702ada374d145e7357f5b698c606c142.
def localCycle00080 : Cycle where
  length := 3
  data := {
    node := ![.distance 4 5, .distance 1 4, .distance 1 5, .distance 4 5]
    constant := ![2, -3, 0]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.gapUpper 4 2, .gapLower 1 4, .triangle 22 1]

-- Cycle fingerprint 50391b31f056452a728307c39e475e6aa3a6df8b73ab5d1b1b5dd16c94a89d29.
def localCycle00081 : Cycle where
  length := 6
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 3, .distance 3 6, .distance 5 6, .distance 4 5, .theta 4]
    constant := ![3, -1, -1, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 0, .triangle 27 0, .triangle 33 1, .triangle 34 0, .corridorLower 4 5]

-- Cycle fingerprint 50ccf8affe96e164b274f1b824b49f81470c70fd310615d87acf3e40d20181f7.
def localCycle00082 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 2 4, .distance 2 5, .distance 5 6, .distance 1 6, .distance 1 5, .distance 1 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, 0, -1, 0, -2, 0, -2, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, true, false, true, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 28 2, .triangle 30 0, .triangle 24 2, .gapLower 1 4, .triangle 17 1, .gapLower 1 1, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint 515220fe0f14b6f16e5acaa584c043a44aab29921d4f070f38f6889dd824ffde.
def localCycle00083 : Cycle where
  length := 8
  data := {
    node := ![.distance 4 5, .distance 0 4, .distance 0 3, .distance 0 1, .theta 1, .distance 1 4, .distance 1 5, .distance 5 6, .distance 4 5]
    constant := ![-1, 0, 0, -2, 2, 0, -1, -1]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![false, false, true, false, false, true, false, false] }
  origin := ![.triangle 12 0, .gapLower 0 3, .triangle 1 1, .gapLower 1 0, .gapLower 1 6, .triangle 22 2, .triangle 24 0, .triangle 34 0]

-- Cycle fingerprint 53882514590344196e48df0be8594d29df226cc2ad4e6b17421332b46a6dd6c5.
def localCycle00084 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 3 5, .distance 5 6, .distance 4 6, .distance 2 4, .distance 1 4, .distance 4 5, .theta 4]
    constant := ![3, 0, -1, 0, -1, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, true, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 31 2, .triangle 33 0, .triangle 34 2, .triangle 29 0, .triangle 16 2, .triangle 22 0, .corridorLower 4 5]

-- Cycle fingerprint 54dac9c019860553ac35c5d19d23fc29cfe590ddf0a85c07f43afcc1ba8be04d.
def localCycle00085 : Cycle where
  length := 4
  data := {
    node := ![.distance 1 4, .distance 1 5, .distance 5 6, .distance 4 6, .distance 1 4]
    constant := ![-2, -1, 0, 2]
    coefficient := ![0, 0, 0, 0]
    strict := ![false, false, true, true] }
  origin := ![.gapLower 1 5, .triangle 24 0, .triangle 34 2, .gapUpper 4 3]

-- Cycle fingerprint 553385485b01d592a5de25d57013412ee1139fc367e370283bb2c23a34a4776d.
def localCycle00086 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 2, .distance 2 5, .distance 5 6, .distance 4 6, .distance 3 6, .distance 2 3, .distance 2 4, .distance 4 5, .distance 3 4, .distance 1 3, .distance 1 2]
    constant := ![2, 2, 0, 0, -1, 0, -1, -1, -1, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![true, true, true, true, false, true, false, false, false, true] }
  origin := ![.gapUpper 2 2, .gapUpper 5 5, .triangle 34 2, .triangle 32 2, .triangle 27 0, .triangle 25 2, .triangle 28 0, .triangle 31 0, .triangle 19 0, .triangle 15 1]

-- Cycle fingerprint 557ba52017e67f43ba1d956f2f1df6ebf4cfd908a536151e2b94d4215894e673.
def localCycle00087 : Cycle where
  length := 8
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 4, .distance 2 3, .distance 3 6, .distance 1 6, .distance 4 6, .distance 5 6, .theta 5]
    constant := ![3, -1, -1, -1, 0, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, true, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 0, .triangle 25 0, .triangle 27 0, .triangle 21 2, .triangle 23 1, .triangle 34 1, .corridorLower 5 6]

-- Cycle fingerprint 56f529bccfb0c7c2e5845bcd1db4f05b51420ffc89691f29d986effa41a511b1.
def localCycle00088 : Cycle where
  length := 8
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 2 3, .distance 3 4, .distance 4 6, .distance 1 6, .distance 5 6, .theta 5]
    constant := ![3, 0, -1, -1, -1, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, true, true, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 26 0, .triangle 25 0, .triangle 32 0, .triangle 23 2, .triangle 24 1, .corridorLower 5 6]

-- Cycle fingerprint 57257d339ec262bc87a512a7d5ea12e6e8ec9bfa518515ebb1d5cf5c8f35ac6e.
def localCycle00089 : Cycle where
  length := 9
  data := {
    node := ![.distance 4 5, .distance 1 5, .distance 1 6, .distance 0 1, .theta 1, .zero, .theta 4, .distance 3 4, .distance 2 4, .distance 4 5]
    constant := ![0, -2, -1, -2, 0, 0, 3, 0, -1]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, false, false, false, false, true, false] }
  origin := ![.gapLower 5 3, .gapLower 1 5, .triangle 4 0, .gapLower 1 0, .thetaLower 1, .thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 28 0]

-- Cycle fingerprint 575f09772bb820c91919545a7cf91d7f96de05c5cc6341b5c30e1305edb3efdf.
def localCycle00090 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .theta 1, .zero, .theta 3, .distance 2 3, .distance 3 6, .distance 3 4, .distance 3 5, .distance 1 5, .distance 1 3, .distance 0 1]
    constant := ![-2, 0, 0, 3, -1, 0, 0, 0, -2, -1]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, false, false, false] }
  origin := ![.gapLower 1 0, .thetaLower 1, .thetaUpper 3, .corridorUpper 2 3, .triangle 27 0, .triangle 32 1, .triangle 31 2, .gapLower 5 3, .gapLower 1 3, .triangle 1 0]

-- Cycle fingerprint 57c626e17d69830d6ebfed200412f1fa1f3d2224e8319141260f8b78f6622a32.
def localCycle00091 : Cycle where
  length := 11
  data := {
    node := ![.distance 2 3, .distance 3 4, .distance 3 6, .distance 3 5, .distance 1 3, .distance 1 2, .distance 0 1, .theta 1, .theta 0, .zero, .theta 3, .distance 2 3]
    constant := ![-1, 0, 0, -1, 0, -1, -3, 0, 0, 0, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1]
    strict := ![false, true, true, false, false, false, false, true, false, false, false] }
  origin := ![.triangle 25 0, .triangle 32 2, .triangle 33 1, .triangle 20 0, .gapLower 1 2, .triangle 0 0, .gapLower 1 0, .thetaNext 0, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3]

-- Cycle fingerprint 57f86b2559540d901a543e316036e853392ddc23843042b32e4c6b2b5e015e3e.
def localCycle00092 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .theta 1, .zero, .theta 3, .distance 2 3, .distance 3 4, .distance 3 6, .distance 3 5, .distance 1 3, .distance 1 2, .distance 0 1]
    constant := ![-2, 0, 0, 3, -1, 0, 0, -1, -2, -1]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, false, false, false] }
  origin := ![.gapLower 1 0, .thetaLower 1, .thetaUpper 3, .corridorUpper 2 3, .triangle 25 0, .triangle 32 2, .triangle 33 1, .triangle 20 0, .gapLower 1 2, .triangle 0 0]

-- Cycle fingerprint 58e8020f4e3da555e6e05be147f17dab9714d86ddbe513601b725acc2eed1f0a.
def localCycle00093 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 2 4, .distance 2 5, .distance 5 6, .distance 1 5, .distance 1 3, .distance 0 1]
    constant := ![-1, 0, 0, 3, 0, 0, -1, -1, -3, -1]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, false, false, false, false] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 28 2, .triangle 30 0, .triangle 24 0, .gapLower 1 3, .triangle 1 0]

-- Cycle fingerprint 594cac141869ba876b6989be92431070cb4bbc290429d086d91016b92422bf7d.
def localCycle00094 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 3, .distance 2 3, .distance 3 4, .distance 3 5, .distance 5 6, .distance 4 5, .distance 1 4, .distance 1 3, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, -1, 0, -1, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 3, .corridorUpper 2 3, .triangle 25 0, .triangle 31 2, .triangle 33 0, .triangle 34 0, .triangle 22 0, .gapLower 1 3, .triangle 1 0, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint 5dffe3bc07caf9d6c890e42ce767689e7d067e5b43794f0c23b0aa7662567b74.
def localCycle00095 : Cycle where
  length := 9
  data := {
    node := ![.distance 2 3, .distance 3 6, .distance 1 3, .distance 1 2, .distance 0 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 2 3]
    constant := ![-1, -1, 0, -1, -1, 0, 0, 3, -1]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![false, false, false, false, false, false, false, false, false] }
  origin := ![.triangle 27 0, .triangle 21 0, .gapLower 1 2, .triangle 0 0, .corridorLower 0 1, .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 25 0]

-- Cycle fingerprint 5e2a5009708adbda57eb7df4340497d5665a895fed1920d9544fd0eae715f5fa.
def localCycle00096 : Cycle where
  length := 7
  data := {
    node := ![.theta 1, .distance 1 4, .distance 4 5, .distance 5 6, .distance 0 5, .distance 0 4, .distance 0 1, .theta 1]
    constant := ![2, -1, -1, -1, 0, 0, -2]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false] }
  origin := ![.gapLower 1 6, .triangle 22 0, .triangle 34 0, .triangle 14 0, .gapLower 0 4, .triangle 2 1, .gapLower 1 0]

-- Cycle fingerprint 5e760f9e6662264d7c376dea3bfb881ac9f73b1a80bf375603649b0c20cf8a6b.
def localCycle00097 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 2 4, .distance 1 4, .distance 1 5, .distance 1 6, .distance 1 3, .distance 1 2, .distance 0 1, .theta 1, .zero]
    constant := ![0, 3, 0, 0, 0, 0, -2, 0, -1, -2, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, true, true, false, true, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 16 2, .triangle 22 2, .triangle 24 2, .gapLower 1 3, .triangle 15 1, .triangle 0 0, .gapLower 1 0, .thetaLower 1]

-- Cycle fingerprint 5ee8408e32516f9e3dc55a5d64633e5763c3aebca92f41f2f512d3ac028735d3.
def localCycle00098 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 3 5, .distance 5 6, .distance 2 5, .distance 2 3, .distance 1 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, -1, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, false, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 31 2, .triangle 33 0, .triangle 30 0, .triangle 26 1, .triangle 15 0, .triangle 0 0, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint 5f264e8ba9ebe05cab22cb80246bb7f9a32742e8906ec4c9a719566073cd5fd3.
def localCycle00099 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 5, .distance 1 6, .distance 5 6, .distance 4 5, .distance 0 4, .distance 0 3, .theta 0, .zero, .theta 1, .distance 1 4, .distance 1 5]
    constant := ![-2, 0, -1, -1, 0, -1, 0, 0, 2, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![false, true, false, false, false, false, false, false, false, true] }
  origin := ![.gapLower 1 4, .triangle 24 1, .triangle 34 0, .triangle 12 0, .gapLower 0 3, .corridorLower 0 3, .thetaLower 0, .thetaUpper 1, .gapLower 1 6, .triangle 22 2]

-- Cycle fingerprint 5f3a509c5c5b39848989c474eb6ee0779e5eb0111b0f6b8652f9df1f0a56d781.
def localCycle00100 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 2 4, .distance 2 5, .distance 5 6, .distance 1 6, .distance 1 5, .distance 1 3, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, 0, -1, 0, -2, -2, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 28 2, .triangle 30 0, .gapLower 6 3, .gapLower 1 4, .gapLower 1 3, .triangle 1 0, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint 6033d1c2f4668a6dcb63286ad63b19c950abb3565800d1696c0f4e6faae30527.
def localCycle00101 : Cycle where
  length := 7
  data := {
    node := ![.theta 1, .distance 1 6, .distance 1 4, .distance 4 5, .distance 0 4, .distance 0 3, .distance 0 1, .theta 1]
    constant := ![2, 0, -1, -1, 0, 0, -2]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, true, false] }
  origin := ![.gapLower 1 6, .triangle 23 1, .triangle 22 0, .triangle 12 0, .gapLower 0 3, .triangle 1 1, .gapLower 1 0]

-- Cycle fingerprint 60c795158d42d7c14810f64c2c6813b23a55f1329cd4ce8ecd367977e2299ea4.
def localCycle00102 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 2 3, .distance 3 6, .distance 4 6, .distance 1 4, .distance 1 3, .distance 1 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, -1, -1, 0, -1, 0, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, true, true, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 25 0, .triangle 27 0, .triangle 32 1, .triangle 23 0, .triangle 19 1, .triangle 15 1, .triangle 0 0, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint 60f6db3d36c77d1518055e47d6227eb73c0cc97e1ee2aaa4b3ee123ff10d7a37.
def localCycle00103 : Cycle where
  length := 12
  data := {
    node := ![.distance 5 6, .distance 4 5, .distance 0 4, .distance 0 3, .distance 0 1, .theta 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 2 4, .distance 2 5, .distance 5 6]
    constant := ![-1, -1, 0, 0, -3, 0, 0, 0, 3, 0, 0, -1]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, true, false, true, false, false, false, true, true, false] }
  origin := ![.triangle 34 0, .triangle 12 0, .gapLower 0 3, .triangle 1 1, .gapLower 1 0, .thetaNext 0, .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 28 2, .triangle 30 0]

-- Cycle fingerprint 633a621d61789a8ac4038a47b875a84726317e4b891db140b512bdb07ee7d54b.
def localCycle00104 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 3, .distance 2 3, .distance 3 6, .distance 3 4, .distance 1 4, .distance 1 5, .distance 1 3, .distance 1 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, -1, 0, 0, 0, -2, 0, -2, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true, false, true, false, false, false] }
  origin := ![.thetaUpper 3, .corridorUpper 2 3, .triangle 27 0, .triangle 32 1, .gapLower 4 3, .triangle 22 2, .gapLower 1 3, .triangle 15 1, .gapLower 1 1, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint 653b7aad068d56f91a568f7934d3f4c7cc1a412cf54466239062cf5dcaae46dc.
def localCycle00105 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 4, .distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 3 5, .distance 3 6, .distance 1 6, .distance 1 4]
    constant := ![-1, -1, 0, 0, 3, -1, 0, 0, -2]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, true, false] }
  origin := ![.triangle 2 0, .corridorLower 0 1, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 26 0, .triangle 33 2, .triangle 21 2, .gapLower 1 4]

-- Cycle fingerprint 66a3ae3ba9c6a68d890ae4132309d8d5ce3d6cc1f916db99a1864f320685e031.
def localCycle00106 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 3, .distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 3 6, .distance 3 4, .distance 1 4, .distance 1 5, .distance 1 3]
    constant := ![-1, -1, 0, 0, 3, -1, 0, 0, -2, -2]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, false, false, false] }
  origin := ![.triangle 1 0, .corridorLower 0 1, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 27 0, .triangle 32 1, .gapLower 4 3, .gapLower 1 4, .gapLower 1 3]

-- Cycle fingerprint 673872824e29394f4d4a1e2474c7ff8718dae1c26ac8c060f11cbf3e7f2692e2.
def localCycle00107 : Cycle where
  length := 11
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 3 5, .distance 3 4, .distance 4 6, .distance 5 6, .distance 1 5, .distance 1 4, .distance 0 1]
    constant := ![-1, 0, 0, 3, -1, 0, -1, 0, -1, 0, -1]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, true, false, false, false] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 26 0, .triangle 31 1, .triangle 32 0, .triangle 34 1, .triangle 24 0, .gapLower 1 4, .triangle 2 0]

-- Cycle fingerprint 674cbad420381e00166e82251de0a4fd7488cf4d1ed712d6cc15c77bf89cd168.
def localCycle00108 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 2 4, .distance 2 5, .distance 5 6, .distance 4 5, .distance 1 4, .distance 1 3, .distance 1 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, 0, -1, -1, -1, 0, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, true, true, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 28 2, .triangle 30 0, .triangle 34 0, .triangle 22 0, .triangle 19 1, .triangle 15 1, .triangle 0 0, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint 67cdaec86441069a6a1d7e402136ddd7c523b8214acf7b63435c2e63dd427cd6.
def localCycle00109 : Cycle where
  length := 11
  data := {
    node := ![.theta 0, .zero, .theta 4, .distance 3 4, .distance 2 4, .distance 1 4, .distance 1 5, .distance 1 6, .distance 1 3, .distance 1 2, .distance 0 1, .theta 0]
    constant := ![0, 0, 3, 0, 0, 0, -2, -2, 0, -1, -1]
    coefficient := ![0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, true, false, false, true, false, false] }
  origin := ![.thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 16 2, .triangle 22 2, .gapLower 1 4, .gapLower 1 3, .triangle 15 1, .triangle 0 0, .corridorLower 0 1]

-- Cycle fingerprint 6966293e8a11a6785ff0758160a9b78cb3dcddca905f1b02850d97acf99c3b90.
def localCycle00110 : Cycle where
  length := 3
  data := {
    node := ![.distance 1 6, .theta 1, .distance 1 5, .distance 1 6]
    constant := ![-1, 2, -2]
    coefficient := ![0, 1, 0]
    strict := ![false, false, false] }
  origin := ![.corridorLower 1 6, .gapLower 1 6, .gapLower 1 5]

-- Cycle fingerprint 698313b21102abb9b46619179b695f1337ac7eb024b88d958452c247c326ad27.
def localCycle00111 : Cycle where
  length := 6
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 4, .distance 2 3, .distance 2 6, .theta 6, .theta 5]
    constant := ![3, -1, -1, 0, -2, 0]
    coefficient := ![1, 0, 0, 0, -1, 0]
    strict := ![false, false, false, true, true, true] }
  origin := ![.corridorUpper 4 5, .triangle 31 0, .triangle 25 0, .triangle 27 2, .gapUpper 6 6, .thetaNext 5]

-- Cycle fingerprint 69f53a6c0bb726b925aa6609d91e576bff6d3024822ba5802c11c786d193ac0f.
def localCycle00112 : Cycle where
  length := 11
  data := {
    node := ![.theta 0, .zero, .theta 3, .distance 2 3, .distance 3 4, .distance 3 6, .distance 1 6, .distance 1 5, .distance 1 3, .distance 1 2, .distance 0 1, .theta 0]
    constant := ![0, 0, 3, -1, 0, 0, -2, 0, -2, -1, -1]
    coefficient := ![0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, true, false, false, false] }
  origin := ![.thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 25 0, .triangle 32 2, .gapLower 6 3, .gapLower 1 4, .triangle 20 1, .gapLower 1 2, .triangle 0 0, .corridorLower 0 1]

-- Cycle fingerprint 6c32cda13c2a96463aa1604b0ba404f151c7b2b47881f116d4536f1417b06a98.
def localCycle00113 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 5, .distance 3 5, .distance 2 3, .distance 3 4, .distance 1 3, .distance 1 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, -1, 0, -1, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, true, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 0, .triangle 31 2, .triangle 26 0, .triangle 25 0, .triangle 19 0, .triangle 15 1, .triangle 0 0, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint 6cd3e78d7366b88bcf65149ee7126abc66888e336e6eef56f8127ededdd9282a.
def localCycle00114 : Cycle where
  length := 9
  data := {
    node := ![.distance 3 4, .distance 1 4, .distance 1 3, .distance 0 1, .theta 1, .zero, .theta 3, .distance 2 3, .distance 3 5, .distance 3 4]
    constant := ![0, -2, -1, -2, 0, 0, 3, -1, 0]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, false, false, false, false, false, true] }
  origin := ![.gapLower 4 2, .gapLower 1 3, .triangle 1 0, .gapLower 1 0, .thetaLower 1, .thetaUpper 3, .corridorUpper 2 3, .triangle 26 0, .triangle 31 1]

-- Cycle fingerprint 6e1aefd70e7b361a6656407f47b1bcc94ad06d4641e9c15904f7e22d87448ac9.
def localCycle00115 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 2 3, .distance 3 5, .distance 4 5, .distance 5 6, .distance 0 5, .theta 0, .zero]
    constant := ![0, 3, -1, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 25 0, .triangle 26 0, .triangle 31 1, .triangle 34 0, .triangle 14 0, .corridorLower 0 5, .thetaLower 0]

-- Cycle fingerprint 6efba9388469f247680c1ba18a499507dba1d505511b7f4847c0a6b5f7400449.
def localCycle00116 : Cycle where
  length := 5
  data := {
    node := ![.distance 1 2, .distance 2 5, .distance 3 5, .distance 1 5, .distance 1 3, .distance 1 2]
    constant := ![2, 0, 0, -2, 0]
    coefficient := ![0, 0, 0, 0, 0]
    strict := ![true, false, true, false, true] }
  origin := ![.gapUpper 2 2, .gapLower 5 4, .triangle 20 2, .gapLower 1 3, .triangle 15 1]

-- Cycle fingerprint 6f278d2af93e084f93eaa629dfe049f99fc8728d55cbf58e77dc1f4ffda9542a.
def localCycle00117 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 2 4, .distance 4 5, .distance 4 6, .distance 1 4, .distance 1 3, .distance 1 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, -1, 0, -1, -2, 0, -2, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false, true, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 28 0, .triangle 34 2, .triangle 23 0, .gapLower 1 3, .triangle 15 1, .gapLower 1 1, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint 71ea96193659485efc3c2cddaea6bad28a9bbe3fc41e7471fedc68847fdb0705.
def localCycle00118 : Cycle where
  length := 3
  data := {
    node := ![.distance 2 3, .distance 1 3, .distance 1 2, .distance 2 3]
    constant := ![0, -3, 2]
    coefficient := ![0, 0, 0]
    strict := ![false, false, true] }
  origin := ![.gapLower 3 2, .gapLower 1 2, .gapUpper 2 2]

-- Cycle fingerprint 7208884fc6b5acd7a6dc8a9f3c6a1ea382ce974231ff24fb061f5cb4c51f45fc.
def localCycle00119 : Cycle where
  length := 9
  data := {
    node := ![.distance 3 6, .distance 1 6, .distance 1 4, .distance 1 2, .distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 3 6]
    constant := ![0, -2, 0, -2, -1, 0, 0, 3, -1]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![true, false, true, false, false, false, false, false, false] }
  origin := ![.triangle 21 2, .gapLower 1 5, .triangle 16 1, .gapLower 1 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 27 0]

-- Cycle fingerprint 736bcbc320e5f51a97e3a9d670c24e15979d7bd735e7eceeb2b2c415ac108d51.
def localCycle00120 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 2 4, .distance 4 5, .distance 4 6, .distance 1 6, .distance 1 4, .distance 1 3, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, -1, 0, 0, -2, -2, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false, false, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 28 0, .triangle 34 2, .gapLower 6 3, .gapLower 1 4, .gapLower 1 3, .triangle 1 0, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint 750abb8493db1edfacf33bf4ba058274df1ec54e12249be22a6ca970ec42206b.
def localCycle00121 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 4, .distance 1 5, .distance 1 6, .distance 0 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 2 4, .distance 1 4]
    constant := ![0, -3, -1, -1, 0, 0, 3, 0, 0]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![true, false, false, false, false, false, false, true, true] }
  origin := ![.triangle 22 2, .gapLower 1 4, .triangle 4 0, .corridorLower 0 1, .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 16 2]

-- Cycle fingerprint 75b7cd0080cac80e88a9cebe30b1ab38cdaa67003f15a02e75866d7f9ff0bc37.
def localCycle00122 : Cycle where
  length := 11
  data := {
    node := ![.theta 0, .zero, .theta 4, .distance 3 4, .distance 2 4, .distance 1 4, .distance 1 5, .distance 1 6, .distance 1 3, .distance 1 2, .distance 0 1, .theta 0]
    constant := ![0, 0, 3, 0, 0, 0, -2, 0, -2, -1, -1]
    coefficient := ![0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, true, false, true, false, false, false] }
  origin := ![.thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 16 2, .triangle 22 2, .gapLower 1 4, .triangle 21 1, .gapLower 1 2, .triangle 0 0, .corridorLower 0 1]

-- Cycle fingerprint 7665b2bb915fe81275316499f245bd893ee5489ac793b5b5deca3f0757bae1a2.
def localCycle00123 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 4, .distance 4 6, .distance 5 6, .distance 2 5, .distance 2 4, .distance 2 3, .distance 1 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, -1, -1, 0, -1, 0, 0, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 0, .triangle 32 0, .triangle 34 1, .triangle 30 0, .gapLower 2 4, .gapLower 2 3, .triangle 15 0, .triangle 0 0, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint 76ddc530ab041e69d6687f346e7d2950b4d38753642b41f3c5f028cd56f58ef0.
def localCycle00124 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 3 4, .distance 3 6, .distance 3 5, .distance 1 3, .distance 1 2, .distance 0 1]
    constant := ![-1, 0, 0, 3, -1, 0, 0, -1, -2, -2]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, false, false, false] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 25 0, .triangle 32 2, .triangle 33 1, .triangle 20 0, .gapLower 1 2, .gapLower 1 1]

-- Cycle fingerprint 774c55349f81aec08ea5de3e4defb74a7236b7b253b6616fe412fb6299305c1f.
def localCycle00125 : Cycle where
  length := 3
  data := {
    node := ![.distance 5 6, .distance 1 5, .distance 1 6, .distance 5 6]
    constant := ![2, -3, 0]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.gapUpper 5 2, .gapLower 1 5, .triangle 24 1]

-- Cycle fingerprint 774daed540c3dd393e8c878703781cb94dbbd5063b2a9ef39f9eeccf3e77ef5a.
def localCycle00126 : Cycle where
  length := 11
  data := {
    node := ![.theta 0, .zero, .theta 4, .distance 3 4, .distance 2 4, .distance 4 5, .distance 1 5, .distance 1 6, .distance 1 3, .distance 1 2, .distance 0 1, .theta 0]
    constant := ![0, 0, 3, 0, -1, 0, -2, 0, -2, -1, -1]
    coefficient := ![0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, true, false, false, false] }
  origin := ![.thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 28 0, .gapLower 5 3, .gapLower 1 5, .triangle 21 1, .gapLower 1 2, .triangle 0 0, .corridorLower 0 1]

-- Cycle fingerprint 78771434bd30b2ee7159f616d3dcb16531d38a988cd29a3230e9bf9148be9567.
def localCycle00127 : Cycle where
  length := 9
  data := {
    node := ![.distance 2 4, .distance 1 4, .distance 1 5, .distance 1 6, .distance 0 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 2 4]
    constant := ![0, -2, -2, -1, -1, 0, 0, 3, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![true, false, false, false, false, false, false, false, true] }
  origin := ![.triangle 16 2, .gapLower 1 5, .gapLower 1 4, .triangle 4 0, .corridorLower 0 1, .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 25 2]

-- Cycle fingerprint 78cfbea8f751d67824da84d66b1c98eca7bca84a58324b74651b88128a1c6068.
def localCycle00128 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 5 6, .distance 2 5, .distance 2 4, .distance 2 3, .distance 1 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, -1, -1, 0, 0, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, true, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 33 0, .triangle 30 0, .triangle 28 1, .triangle 25 1, .triangle 15 0, .triangle 0 0, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint 7a7709eb796caf3552a3092315cfb93f80c3bb6368ef62a3ecd2565318ccd6bc.
def localCycle00129 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 3, .distance 2 3, .distance 3 4, .distance 3 6, .distance 3 5, .distance 1 5, .distance 1 3, .distance 1 2, .distance 0 1, .theta 1, .zero]
    constant := ![0, 3, -1, 0, 0, 0, -2, 0, -1, -2, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false, false, true, false, false, false] }
  origin := ![.thetaUpper 3, .corridorUpper 2 3, .triangle 25 0, .triangle 32 2, .triangle 33 1, .gapLower 5 3, .gapLower 1 3, .triangle 15 1, .triangle 0 0, .gapLower 1 0, .thetaLower 1]

-- Cycle fingerprint 7a8e633f3cb304d12bc82b4ebff984812d03ca5093161b26740258df0b2380e0.
def localCycle00130 : Cycle where
  length := 12
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 3, .distance 3 6, .distance 4 6, .distance 4 5, .distance 1 4, .distance 1 3, .distance 1 2, .distance 0 1, .theta 0, .zero, .theta 4]
    constant := ![3, -1, -1, 0, 0, -1, 0, 0, -1, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![false, false, false, true, true, false, true, true, false, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 0, .triangle 27 0, .triangle 32 1, .triangle 34 1, .triangle 22 0, .triangle 19 1, .triangle 15 1, .triangle 0 0, .corridorLower 0 1, .thetaLower 0, .thetaUpper 4]

-- Cycle fingerprint 7b23bd103d500c17f827e1d953853adad4e83668b30b26e5e80c888f93e6a641.
def localCycle00131 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 3, .distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 3 4, .distance 3 6, .distance 1 6, .distance 1 5, .distance 1 3]
    constant := ![-1, -1, 0, 0, 3, -1, 0, 0, -2, -2]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, false, false, false] }
  origin := ![.triangle 1 0, .corridorLower 0 1, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 25 0, .triangle 32 2, .gapLower 6 3, .gapLower 1 4, .gapLower 1 3]

-- Cycle fingerprint 7bf409658f73aed947561214b4dac9c659f13ad2d8040696e13679e64acfab6b.
def localCycle00132 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 5, .distance 4 5, .distance 0 4, .distance 0 3, .theta 3, .distance 2 3, .distance 3 4, .distance 3 6, .distance 1 6, .distance 1 5]
    constant := ![0, -1, 0, 0, 3, -1, 0, 0, -2]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0, 0]
    strict := ![true, false, false, false, false, false, true, true, false] }
  origin := ![.triangle 22 1, .triangle 12 0, .gapLower 0 3, .gapLower 3 0, .corridorUpper 2 3, .triangle 25 0, .triangle 32 2, .triangle 21 2, .gapLower 1 4]

-- Cycle fingerprint 7c44682d38844d59f025a1966b72e4f0df2047c81c92e7f3877200eee3206821.
def localCycle00133 : Cycle where
  length := 5
  data := {
    node := ![.theta 4, .distance 3 4, .distance 4 6, .distance 2 4, .distance 4 5, .theta 4]
    constant := ![3, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 32 0, .triangle 29 0, .triangle 28 0, .corridorLower 4 5]

-- Cycle fingerprint 7c4d14846d041d455eaf4ba04e7f810d28aa85ed91c2eeeb7ea7b854a12c7f25.
def localCycle00134 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 4, .distance 1 3, .distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 3 5, .distance 1 5, .distance 1 6, .distance 1 4]
    constant := ![-2, -1, -1, 0, 0, 3, -1, 0, -2, 0]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false, false, true] }
  origin := ![.gapLower 1 3, .triangle 1 0, .corridorLower 0 1, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 26 0, .gapLower 5 3, .gapLower 1 5, .triangle 23 1]

-- Cycle fingerprint 7e3936559cc58da83f461b3ac017e8e3ecae610a66a0da91b29703f7598e0ce9.
def localCycle00135 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 3, .distance 2 3, .distance 3 5, .distance 3 6, .distance 1 6, .distance 1 4, .distance 1 3, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, -1, 0, 0, 0, -2, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true, false, false, false, false] }
  origin := ![.thetaUpper 3, .corridorUpper 2 3, .triangle 26 0, .triangle 33 2, .gapLower 6 3, .triangle 23 1, .gapLower 1 3, .triangle 1 0, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint 7e73dd93448fcca41069a58b83268061f327783f2deafbfb480db140c8a1fcb1.
def localCycle00136 : Cycle where
  length := 9
  data := {
    node := ![.distance 3 4, .distance 1 4, .distance 1 5, .distance 0 1, .theta 1, .zero, .theta 3, .distance 2 3, .distance 3 6, .distance 3 4]
    constant := ![0, -2, -1, -2, 0, 0, 3, -1, 0]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, false, false, false, false, false, true] }
  origin := ![.gapLower 4 3, .gapLower 1 4, .triangle 3 0, .gapLower 1 0, .thetaLower 1, .thetaUpper 3, .corridorUpper 2 3, .triangle 27 0, .triangle 32 1]

-- Cycle fingerprint 7f8cad7a0c006cd971792e0ae120aa147d786e7a48d2e1cd0f372b0456ba075d.
def localCycle00137 : Cycle where
  length := 4
  data := {
    node := ![.distance 1 3, .distance 1 2, .distance 2 5, .distance 3 5, .distance 1 3]
    constant := ![-3, 2, 0, -1]
    coefficient := ![0, 0, 0, 0]
    strict := ![false, true, false, false] }
  origin := ![.gapLower 1 2, .gapUpper 2 2, .gapLower 5 4, .triangle 20 0]

-- Cycle fingerprint 805f17ae19bab8a7d49f4e2b2d90b9b175f9fb019db870a700caaf64bbc5aa21.
def localCycle00138 : Cycle where
  length := 6
  data := {
    node := ![.distance 4 5, .distance 3 4, .distance 1 3, .distance 1 2, .distance 2 6, .distance 5 6, .distance 4 5]
    constant := ![-1, -1, 0, 2, 0, -1]
    coefficient := ![0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false] }
  origin := ![.triangle 31 0, .triangle 19 0, .gapLower 1 2, .gapUpper 2 2, .gapLower 6 5, .triangle 34 0]

-- Cycle fingerprint 80c054f41a5aab00d08d0f06849060b558b82ea9c5985f4a06536de154c77995.
def localCycle00139 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 2 4, .distance 2 5, .distance 2 6, .distance 1 6, .distance 1 3, .distance 1 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, 0, 0, 0, -2, 0, -2, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, true, true, false, true, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 28 2, .triangle 30 2, .triangle 18 2, .gapLower 1 3, .triangle 15 1, .gapLower 1 1, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint 8220cdb75d80f0b23ea158b7950ab277ecbd4d81a7fd69b8454cef3eadb037cc.
def localCycle00140 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 3, .distance 2 3, .distance 2 4, .distance 4 5, .distance 3 4, .distance 4 6, .distance 1 4, .distance 1 3, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, -1, -1, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 3, .corridorUpper 2 3, .triangle 25 2, .triangle 28 0, .triangle 31 0, .triangle 32 0, .triangle 23 0, .gapLower 1 3, .triangle 1 0, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint 822ddac943a5b952ba8e89f8d826b346b48fb5a0f82835b3ad788bc0f145b9e8.
def localCycle00141 : Cycle where
  length := 9
  data := {
    node := ![.distance 3 4, .distance 1 3, .distance 1 2, .distance 0 1, .theta 1, .zero, .theta 3, .distance 2 3, .distance 3 5, .distance 3 4]
    constant := ![-1, -2, -1, -2, 0, 0, 3, -1, 0]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, false, false, false, false, false, true] }
  origin := ![.triangle 19 0, .gapLower 1 2, .triangle 0 0, .gapLower 1 0, .thetaLower 1, .thetaUpper 3, .corridorUpper 2 3, .triangle 26 0, .triangle 31 1]

-- Cycle fingerprint 824b53c2d9c052377011f27fbd93c9e2612ced050b61ffdd780b6cec73fc77c5.
def localCycle00142 : Cycle where
  length := 4
  data := {
    node := ![.distance 1 4, .distance 1 3, .distance 1 2, .distance 2 4, .distance 1 4]
    constant := ![-2, -2, 2, 0]
    coefficient := ![0, 0, 0, 0]
    strict := ![false, false, true, true] }
  origin := ![.gapLower 1 3, .gapLower 1 2, .gapUpper 2 2, .triangle 16 2]

-- Cycle fingerprint 8967b099be402891c7f84b76b544fba1cf1e5a2f6abc213f92f71c69574bddb5.
def localCycle00143 : Cycle where
  length := 8
  data := {
    node := ![.distance 4 5, .distance 1 4, .distance 1 3, .distance 1 2, .distance 2 6, .distance 5 6, .distance 4 6, .distance 3 4, .distance 4 5]
    constant := ![-1, 0, 0, 2, 0, 0, -1, -1]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, true, false, false] }
  origin := ![.triangle 22 0, .gapLower 1 3, .triangle 15 1, .gapUpper 2 2, .gapLower 6 5, .triangle 34 2, .triangle 32 0, .triangle 31 0]

-- Cycle fingerprint 89ddd2648b082aee0811d4e0180242fc5d30f80628d513d16c936bfc67d55153.
def localCycle00144 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 4 5, .distance 2 4, .distance 4 6, .distance 1 4, .distance 1 3, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, -1, -1, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 31 0, .triangle 28 0, .triangle 29 0, .triangle 23 0, .triangle 19 1, .triangle 1 0, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint 8a90cc1e6e2e38ce331da101c6d5b73a994453868563eeb8b8467b4e6f213d53.
def localCycle00145 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 3, .distance 1 2, .distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 3 4, .distance 1 4, .distance 1 6, .distance 1 3]
    constant := ![-2, -1, -1, 0, 0, 3, -1, 0, -2, 0]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false, false, true] }
  origin := ![.gapLower 1 2, .triangle 0 0, .corridorLower 0 1, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 25 0, .gapLower 4 4, .gapLower 1 5, .triangle 21 1]

-- Cycle fingerprint 8b23ad51d3989fdc86c466e6a0e929420d545336dbdb940a2d76a0686ca12057.
def localCycle00146 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 3, .distance 2 3, .distance 3 5, .distance 1 5, .distance 1 6, .distance 0 1, .theta 1, .zero]
    constant := ![0, 3, -1, 0, -2, -1, -2, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 3, .corridorUpper 2 3, .triangle 26 0, .gapLower 5 3, .gapLower 1 5, .triangle 4 0, .gapLower 1 0, .thetaLower 1]

-- Cycle fingerprint 8bbb0043189a8a353bbb1cfc51e69f68c9cd1e0cfd040bb7c3240609792454dd.
def localCycle00147 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 6, .distance 1 3, .distance 0 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 2 4, .distance 1 4, .distance 1 5, .distance 1 6]
    constant := ![-2, -1, -1, 0, 0, 3, 0, 0, -2, 0]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, true, false, true] }
  origin := ![.gapLower 1 3, .triangle 1 0, .corridorLower 0 1, .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 16 2, .gapLower 1 5, .triangle 24 2]

-- Cycle fingerprint 8c24e1002449cd7c6f8e1cd7a2654e0f0aa0baef8ab4ba2f1e92d9141c4c0ba9.
def localCycle00148 : Cycle where
  length := 11
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 2 3, .distance 3 6, .distance 4 6, .distance 5 6, .distance 1 5, .distance 1 4, .distance 0 1]
    constant := ![-1, 0, 0, 3, -1, -1, 0, 0, -1, 0, -1]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, true, false, false, false] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 25 0, .triangle 27 0, .triangle 32 1, .triangle 34 1, .triangle 24 0, .gapLower 1 4, .triangle 2 0]

-- Cycle fingerprint 8ccdb354866ee0494b71e93ea98708a3e3478d557f0f865c98d8f2870c386290.
def localCycle00149 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 3, .distance 1 2, .distance 0 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 2 4, .distance 1 4, .distance 1 6, .distance 1 3]
    constant := ![-2, -1, -1, 0, 0, 3, 0, 0, -2, 0]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, true, false, true] }
  origin := ![.gapLower 1 2, .triangle 0 0, .corridorLower 0 1, .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 16 2, .gapLower 1 5, .triangle 21 1]

-- Cycle fingerprint 8d1db3f8cb1e725614c432d574ab0e7cbbc13aff64d1ccc74db7ee22f09d9c3c.
def localCycle00150 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 3, .distance 3 5, .distance 4 5, .distance 1 4, .distance 4 6, .theta 4]
    constant := ![3, -1, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 0, .triangle 26 0, .triangle 31 1, .triangle 22 0, .triangle 23 0, .corridorLower 4 6]

-- Cycle fingerprint 8d9c3eb4c95705bb6aaf7bf3d8c95a3c69fca88717ffee73fa3d21d2dca7ffbf.
def localCycle00151 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 3, .distance 3 6, .distance 5 6, .distance 4 6, .distance 1 4, .distance 4 5, .theta 4]
    constant := ![3, -1, -1, 0, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 0, .triangle 27 0, .triangle 33 1, .triangle 34 2, .triangle 23 0, .triangle 22 0, .corridorLower 4 5]

-- Cycle fingerprint 8f6bce13583a6a4401bdd35ae97f5138ba6a3f07748d6dadecf8a7b47ce0ed6d.
def localCycle00152 : Cycle where
  length := 6
  data := {
    node := ![.theta 4, .distance 3 4, .distance 4 6, .distance 2 4, .distance 1 4, .distance 4 5, .theta 4]
    constant := ![3, -1, -1, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 32 0, .triangle 29 0, .triangle 16 2, .triangle 22 0, .corridorLower 4 5]

-- Cycle fingerprint 9135afafdb6f4a3d4f17c4098390a49edf0e1eda846886c839a84de466278477.
def localCycle00153 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 5, .distance 1 3, .distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 3 4, .distance 1 4, .distance 1 6, .distance 1 5]
    constant := ![-2, -1, -1, 0, 0, 3, -1, 0, -2, 0]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false, false, true] }
  origin := ![.gapLower 1 3, .triangle 1 0, .corridorLower 0 1, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 25 0, .gapLower 4 4, .gapLower 1 5, .triangle 24 1]

-- Cycle fingerprint 9263c9d7bac6641604312369369f7efba17f2aaf6733fbbd0ed81ec8bd7e362a.
def localCycle00154 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 2 4, .distance 2 5, .distance 5 6, .distance 1 5, .distance 1 3, .distance 1 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, 0, -1, -1, -2, -2, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 28 2, .triangle 30 0, .triangle 24 0, .gapLower 1 3, .gapLower 1 2, .triangle 0 0, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint 93969f84a1947e986c7e84359200430c2dbec1973a2394d9c454c3f9704ef4d7.
def localCycle00155 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 4 5, .distance 2 4, .distance 2 3, .distance 3 6, .distance 1 3, .distance 1 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, -1, -1, 0, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, true, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 31 0, .triangle 28 0, .gapLower 2 4, .triangle 27 0, .triangle 21 0, .triangle 15 1, .triangle 0 0, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint 939a9f65243e155640b536c64534b5936ba0d858afbe1ffc83afe3a937c98776.
def localCycle00156 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 2 3, .distance 3 6, .distance 1 3, .distance 1 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, -1, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 25 0, .triangle 27 0, .triangle 21 0, .triangle 15 1, .triangle 0 0, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint 94b03597870a7fd1a18ee63700dd9626f063037e4eaf9471a24b3fd4e27bae9b.
def localCycle00157 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 3, .distance 2 3, .distance 3 5, .distance 3 4, .distance 4 6, .distance 1 4, .distance 1 3, .distance 1 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, -1, 0, -1, -1, 0, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, true, true, false, false, false] }
  origin := ![.thetaUpper 3, .corridorUpper 2 3, .triangle 26 0, .triangle 31 1, .triangle 32 0, .triangle 23 0, .triangle 19 1, .triangle 15 1, .triangle 0 0, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint 9970bb168febb6c3dcedaf63b4d4f293620258f63a1f7f40dcd8b7503973fdbf.
def localCycle00158 : Cycle where
  length := 10
  data := {
    node := ![.distance 5 6, .distance 0 5, .distance 0 4, .distance 0 3, .distance 0 2, .distance 0 1, .theta 0, .zero, .theta 1, .distance 1 5, .distance 5 6]
    constant := ![-1, 0, 0, 0, 0, -1, 0, 0, 1, -1]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![false, false, true, true, true, false, false, false, false, false] }
  origin := ![.triangle 14 0, .gapLower 0 4, .triangle 9 1, .triangle 5 1, .triangle 0 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 1, .gapLower 1 6, .triangle 24 0]

-- Cycle fingerprint 9b8e1549750de588d219c00802c86c1fa570ff03aa917f32c2edee539914452b.
def localCycle00159 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 2, .theta 1, .distance 1 4, .distance 1 5, .distance 5 6, .distance 4 5, .distance 0 4, .distance 0 3, .distance 1 3, .distance 1 2]
    constant := ![-1, 2, 0, -1, -1, -1, 0, 2, -2]
    coefficient := ![0, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, true, false] }
  origin := ![.corridorLower 1 2, .gapLower 1 6, .triangle 22 2, .triangle 24 0, .triangle 34 0, .triangle 12 0, .gapLower 0 3, .gapUpper 3 1, .gapLower 1 2]

-- Cycle fingerprint 9f8bb162b6466a2154dac232a716e797a792003ac3882cb57afebddccdb08f89.
def localCycle00160 : Cycle where
  length := 5
  data := {
    node := ![.distance 1 2, .distance 2 4, .distance 3 4, .distance 1 4, .distance 1 3, .distance 1 2]
    constant := ![2, 0, 0, -3, 0]
    coefficient := ![0, 0, 0, 0, 0]
    strict := ![true, false, false, false, true] }
  origin := ![.gapUpper 2 2, .gapLower 4 3, .gapLower 4 2, .gapLower 1 3, .triangle 15 1]

-- Cycle fingerprint 9fa3e8bc11ea7f641f608c7d066d9c6b278523b60c3721e8275c15d7a45da1e6.
def localCycle00161 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 3, .distance 2 3, .distance 3 4, .distance 1 4, .distance 1 6, .distance 0 1, .theta 1, .zero]
    constant := ![0, 3, -1, 0, -2, -1, -2, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 3, .corridorUpper 2 3, .triangle 25 0, .gapLower 4 4, .gapLower 1 5, .triangle 4 0, .gapLower 1 0, .thetaLower 1]

-- Cycle fingerprint 9fa6b3aa385135d43cd22bdb3bb120c54802f95e16a4d9d01016d68b33abf941.
def localCycle00162 : Cycle where
  length := 6
  data := {
    node := ![.distance 5 6, .distance 0 5, .distance 0 4, .distance 0 1, .theta 1, .distance 1 5, .distance 5 6]
    constant := ![-1, 0, 0, -2, 2, -1]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![false, false, true, false, false, false] }
  origin := ![.triangle 14 0, .gapLower 0 4, .triangle 2 1, .gapLower 1 0, .gapLower 1 6, .triangle 24 0]

-- Cycle fingerprint 9feebb43494aed73ead45c913020fd3fc30b7148bb96999054937859ca28370a.
def localCycle00163 : Cycle where
  length := 12
  data := {
    node := ![.distance 3 4, .distance 2 4, .distance 4 5, .distance 4 6, .distance 1 6, .distance 1 4, .distance 1 3, .distance 1 2, .distance 0 1, .theta 0, .zero, .theta 4, .distance 3 4]
    constant := ![0, -1, 0, 0, -2, 0, -2, -1, -1, 0, 0, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1]
    strict := ![true, false, true, false, false, true, false, false, false, false, false, false] }
  origin := ![.triangle 25 2, .triangle 28 0, .triangle 34 2, .gapLower 6 3, .gapLower 1 4, .triangle 19 1, .gapLower 1 2, .triangle 0 0, .corridorLower 0 1, .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4]

-- Cycle fingerprint a0289adce31cf7dec560f66d83f75a0b0a245c4a0ffa9433510667a8728ce86a.
def localCycle00164 : Cycle where
  length := 10
  data := {
    node := ![.theta 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 3 6, .distance 3 4, .distance 1 3, .distance 1 2, .distance 0 1, .theta 1]
    constant := ![0, 0, 0, 3, -1, 0, -1, 0, -2, -2]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![true, false, false, false, false, true, false, false, false, false] }
  origin := ![.thetaNext 0, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 27 0, .triangle 32 1, .triangle 19 0, .gapLower 1 2, .gapLower 1 1, .gapLower 1 0]

-- Cycle fingerprint a0bdd37a5f596ea9fd92bcb1dc414d81e9df06cf59011773b03bffe6fc740bdb.
def localCycle00165 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 2 4, .distance 4 5, .distance 4 6, .distance 1 4, .distance 1 3, .distance 1 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, -1, 0, -1, -2, -2, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false, false, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 28 0, .triangle 34 2, .triangle 23 0, .gapLower 1 3, .gapLower 1 2, .triangle 0 0, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint a171447624e5be71d020eb7b4ee3e49b57849fc5a19a0547b5d19c7b78747ede.
def localCycle00166 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 2 3, .distance 3 6, .distance 3 5, .distance 1 3, .distance 1 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, -1, -1, 0, -1, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, true, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 25 0, .triangle 27 0, .triangle 33 1, .triangle 20 0, .triangle 15 1, .triangle 0 0, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint a17b97e6522872fcd9e25411dcc9481ac452efd3d11cd48ca3581a5e10557ab5.
def localCycle00167 : Cycle where
  length := 9
  data := {
    node := ![.distance 2 4, .distance 1 4, .distance 1 5, .distance 1 2, .distance 0 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 2 4]
    constant := ![0, -2, 0, -2, -1, 0, 0, 3, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![true, false, true, false, false, false, false, false, true] }
  origin := ![.triangle 16 2, .gapLower 1 5, .triangle 17 1, .gapLower 1 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 25 2]

-- Cycle fingerprint a2d6743a20ccab4220c33eb7374521f3e982ff4ca8a7a930684d997de0af8257.
def localCycle00168 : Cycle where
  length := 9
  data := {
    node := ![.distance 3 4, .distance 4 5, .distance 2 4, .distance 4 6, .distance 5 6, .distance 1 5, .distance 0 5, .distance 0 4, .theta 4, .distance 3 4]
    constant := ![-1, -1, -1, 0, -1, 0, 0, 0, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![false, false, false, true, false, true, true, false, false] }
  origin := ![.triangle 31 0, .triangle 28 0, .triangle 29 0, .triangle 34 1, .triangle 24 0, .triangle 3 2, .triangle 12 1, .gapLower 4 0, .corridorUpper 3 4]

-- Cycle fingerprint a3140abd7817e2da4c8f910bec82db01ea786180dccb7cc9962c41d286ce448f.
def localCycle00169 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 3, .distance 2 3, .distance 3 6, .distance 3 4, .distance 1 4, .distance 1 5, .distance 1 3, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, -1, 0, 0, 0, -2, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true, false, false, false, false] }
  origin := ![.thetaUpper 3, .corridorUpper 2 3, .triangle 27 0, .triangle 32 1, .gapLower 4 3, .triangle 22 2, .gapLower 1 3, .triangle 1 0, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint a4e9c272e477153fa4951bb19bb72ccae24f15ee73596c0260fe4978f694d0ea.
def localCycle00170 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 4, .distance 0 3, .theta 0, .zero, .theta 1, .distance 1 6, .distance 1 4, .distance 4 5, .distance 0 4]
    constant := ![0, -1, 0, 0, 1, 0, -1, -1]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![true, false, false, false, false, true, false, false] }
  origin := ![.triangle 9 1, .corridorLower 0 3, .thetaLower 0, .thetaUpper 1, .gapLower 1 6, .triangle 23 1, .triangle 22 0, .triangle 12 0]

-- Cycle fingerprint a533fa77a13e614128c213680052bd1eb8605d0bbbdda6d0419bcc66a17977c0.
def localCycle00171 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .theta 1, .zero, .theta 4, .distance 3 4, .distance 2 4, .distance 2 5, .distance 5 6, .distance 1 5, .distance 1 3, .distance 0 1]
    constant := ![-2, 0, 0, 3, 0, 0, -1, -1, -2, -1]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, false, false, false, false] }
  origin := ![.gapLower 1 0, .thetaLower 1, .thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 28 2, .triangle 30 0, .triangle 24 0, .gapLower 1 3, .triangle 1 0]

-- Cycle fingerprint a61f576ae7648eed3bcd5686244b4580bcbef76cca40873374948a06772f1e17.
def localCycle00172 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 5, .distance 3 4, .distance 2 3, .distance 1 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, -1, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 0, .triangle 31 0, .triangle 25 0, .triangle 15 0, .triangle 0 0, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint a7d8a4eeeaf1c2220c6dd3817115fb986df0876d4e5dc2a50450c8f1ca13e72e.
def localCycle00173 : Cycle where
  length := 3
  data := {
    node := ![.distance 4 6, .distance 1 4, .distance 1 6, .distance 4 6]
    constant := ![2, -3, 0]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.gapUpper 4 3, .gapLower 1 5, .triangle 23 1]

-- Cycle fingerprint a818172455b17eca3ca44a1aa9e81cc23ad0affa75668577cd0b240baa58f869.
def localCycle00174 : Cycle where
  length := 9
  data := {
    node := ![.distance 3 4, .distance 1 4, .distance 1 6, .distance 1 5, .distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 3 4]
    constant := ![0, -2, -2, -1, -1, 0, 0, 3, -1]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![false, false, false, false, false, false, false, false, false] }
  origin := ![.gapLower 4 4, .gapLower 1 5, .gapLower 1 4, .triangle 3 0, .corridorLower 0 1, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 25 0]

-- Cycle fingerprint a851a5dc66ad62f5d561d7470c969387b54a59d7c4f199de9fc56f9d14437cf6.
def localCycle00175 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 5, .distance 2 4, .distance 3 4, .distance 1 3, .distance 1 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, -1, -1, 0, -1, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, true, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 0, .triangle 28 0, .triangle 25 1, .triangle 19 0, .triangle 15 1, .triangle 0 0, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint a85bec72c041b5744d645d715a116c5f602df8d571b546d4ec4448c0c707e751.
def localCycle00176 : Cycle where
  length := 3
  data := {
    node := ![.distance 5 6, .distance 1 5, .distance 1 6, .distance 5 6]
    constant := ![2, -2, 0]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.gapUpper 5 2, .gapLower 1 5, .triangle 24 1]

-- Cycle fingerprint aa5d8fc73799c4f6f43937a126a31f7ed78df362071661fecbbc35838eb60c34.
def localCycle00177 : Cycle where
  length := 3
  data := {
    node := ![.distance 5 6, .distance 1 5, .distance 1 6, .distance 5 6]
    constant := ![2, -3, 0]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.gapUpper 5 3, .gapLower 1 4, .triangle 24 1]

-- Cycle fingerprint aabe3e1cca54ba899d9e1ece80ee15af8a4d7b1d6b54bc212fde0eea9b3ed89d.
def localCycle00178 : Cycle where
  length := 11
  data := {
    node := ![.theta 0, .zero, .theta 4, .distance 3 4, .distance 2 4, .distance 4 5, .distance 1 5, .distance 1 6, .distance 1 4, .distance 1 3, .distance 0 1, .theta 0]
    constant := ![0, 0, 3, 0, -1, 0, -2, 0, -2, -1, -1]
    coefficient := ![0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, true, false, false, false] }
  origin := ![.thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 28 0, .gapLower 5 3, .gapLower 1 5, .triangle 23 1, .gapLower 1 3, .triangle 1 0, .corridorLower 0 1]

-- Cycle fingerprint ab9b3db30ff53487a34bdd68c6a0d0328992dcb7b8571c41a5d066ab2beaa3a8.
def localCycle00179 : Cycle where
  length := 9
  data := {
    node := ![.distance 3 4, .distance 1 3, .distance 1 2, .distance 0 1, .theta 1, .zero, .theta 3, .distance 2 3, .distance 3 6, .distance 3 4]
    constant := ![-1, -2, -1, -2, 0, 0, 3, -1, 0]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, false, false, false, false, false, true] }
  origin := ![.triangle 19 0, .gapLower 1 2, .triangle 0 0, .gapLower 1 0, .thetaLower 1, .thetaUpper 3, .corridorUpper 2 3, .triangle 27 0, .triangle 32 1]

-- Cycle fingerprint ac387c781c9641cbef298220dfc3a640a68b40eddc3127bdb94accb8d1782a4c.
def localCycle00180 : Cycle where
  length := 10
  data := {
    node := ![.theta 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 3 5, .distance 3 4, .distance 1 3, .distance 1 2, .distance 0 1, .theta 1]
    constant := ![0, 0, 0, 3, -1, 0, -1, 0, -2, -2]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![true, false, false, false, false, true, false, false, false, false] }
  origin := ![.thetaNext 0, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 26 0, .triangle 31 1, .triangle 19 0, .gapLower 1 2, .gapLower 1 1, .gapLower 1 0]

-- Cycle fingerprint acb9581f76438ec00588b19926e04f90575d861c5b161b3c4f034cdc4c0cab95.
def localCycle00181 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 2 3, .distance 3 5, .distance 3 4, .distance 1 3, .distance 1 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, 0, -1, -1, 0, -1, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, true, false, true, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 27 0, .triangle 26 0, .triangle 31 1, .triangle 19 0, .triangle 15 1, .triangle 0 0, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint b06bb9431357fe133d320be6f1afcb3803c9155d5fdebfcc689aff58c24542a3.
def localCycle00182 : Cycle where
  length := 7
  data := {
    node := ![.distance 2 6, .theta 6, .theta 5, .theta 4, .distance 3 4, .distance 4 5, .distance 2 4, .distance 2 6]
    constant := ![-2, 0, 0, 3, -1, -1, 0]
    coefficient := ![-1, 0, 0, 1, 0, 0, 0]
    strict := ![true, true, true, false, false, false, true] }
  origin := ![.gapUpper 6 6, .thetaNext 5, .thetaNext 4, .corridorUpper 3 4, .triangle 31 0, .triangle 28 0, .triangle 29 2]

-- Cycle fingerprint b07055bc5b95ab4573d624079d4589696e4b0b17d7769c10c3b5cb9c72074398.
def localCycle00183 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 5, .distance 1 3, .distance 0 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 2 4, .distance 2 5, .distance 5 6, .distance 1 5]
    constant := ![-2, -1, -1, 0, 0, 3, 0, 0, -1, -1]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, true, false, false] }
  origin := ![.gapLower 1 3, .triangle 1 0, .corridorLower 0 1, .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 28 2, .triangle 30 0, .triangle 24 0]

-- Cycle fingerprint b15b72f8189075089648677e021057b43a8e75bb6484be7d3ba2b7b4337bd8a7.
def localCycle00184 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 2, .distance 0 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 2 3, .distance 1 2]
    constant := ![-3, -1, 0, 0, 3, -1, -1]
    coefficient := ![0, 0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 1 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 25 0, .triangle 15 0]

-- Cycle fingerprint b25d11bca8303199b723fcc092e82234f7dc78294a173b949d2c56e15fb658ee.
def localCycle00185 : Cycle where
  length := 10
  data := {
    node := ![.theta 0, .zero, .theta 3, .distance 2 3, .distance 3 4, .distance 3 6, .distance 3 5, .distance 1 3, .distance 1 2, .distance 0 1, .theta 0]
    constant := ![0, 0, 3, -1, 0, 0, -1, 0, -3, -1]
    coefficient := ![0, 1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, false, false, false, false] }
  origin := ![.thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 25 0, .triangle 32 2, .triangle 33 1, .triangle 20 0, .gapLower 1 2, .gapLower 1 1, .corridorLower 0 1]

-- Cycle fingerprint b3c275ff1849aaca64f0d3fa2de6886331ef751de6b78a055f43bf09cd37c5ec.
def localCycle00186 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 5 6, .distance 2 5, .distance 2 4, .distance 1 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, -1, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 34 0, .triangle 30 0, .gapLower 2 3, .triangle 16 0, .triangle 0 0, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint b6ffcf7d4fcea8473a02f8246977d1057764f0ca1ae0657f62e6109be0eed248.
def localCycle00187 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 1, .distance 1 4, .distance 1 5, .distance 1 6, .distance 1 3, .distance 1 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 2, 0, -2, 0, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, true, false, false, false] }
  origin := ![.thetaUpper 1, .gapLower 1 6, .triangle 22 2, .gapLower 1 4, .triangle 21 1, .triangle 15 1, .triangle 0 0, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint b76e15cdbe434c257b9a2a8fdb50cff7ef39daf48721e46305902c40fe303364.
def localCycle00188 : Cycle where
  length := 10
  data := {
    node := ![.theta 0, .zero, .theta 3, .distance 2 3, .distance 3 5, .distance 3 4, .distance 1 3, .distance 1 2, .distance 0 1, .theta 1, .theta 0]
    constant := ![0, 0, 3, -1, 0, -1, 0, -1, -3, 0]
    coefficient := ![0, 1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, false, false, true] }
  origin := ![.thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 26 0, .triangle 31 1, .triangle 19 0, .gapLower 1 2, .triangle 0 0, .gapLower 1 0, .thetaNext 0]

-- Cycle fingerprint b89b1dc65cc43ced18841e295e4e6e1e56e3ce07ef673d00ea7049837e58800d.
def localCycle00189 : Cycle where
  length := 9
  data := {
    node := ![.distance 3 4, .distance 1 3, .distance 1 2, .distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 3 6, .distance 3 4]
    constant := ![-1, -2, -2, -1, 0, 0, 3, -1, 0]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, false, false, false, false, false, true] }
  origin := ![.triangle 19 0, .gapLower 1 2, .gapLower 1 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 27 0, .triangle 32 1]

-- Cycle fingerprint baa160259bd6d107ef904dd740a231ab5ed76a2a125f014fa2e7d391359142ce.
def localCycle00190 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 4, .distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 3 4, .distance 4 5, .distance 5 6, .distance 1 5, .distance 1 4]
    constant := ![-1, -1, 0, 0, 3, -1, -1, -1, -1, 0]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false, false, false] }
  origin := ![.triangle 2 0, .corridorLower 0 1, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 25 0, .triangle 31 0, .triangle 34 0, .triangle 24 0, .gapLower 1 4]

-- Cycle fingerprint badf99e119b98bf2b4c8ae41dce568fd18dee2232f108e0f97286b9f7a0448ce.
def localCycle00191 : Cycle where
  length := 11
  data := {
    node := ![.theta 1, .zero, .theta 3, .distance 2 3, .distance 3 4, .distance 3 6, .distance 1 6, .distance 1 5, .distance 1 3, .distance 1 2, .distance 0 1, .theta 1]
    constant := ![0, 0, 3, -1, 0, 0, -2, 0, 0, -1, -2]
    coefficient := ![0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, true, true, false, false] }
  origin := ![.thetaLower 1, .thetaUpper 3, .corridorUpper 2 3, .triangle 25 0, .triangle 32 2, .gapLower 6 3, .gapLower 1 4, .triangle 20 1, .triangle 15 1, .triangle 0 0, .gapLower 1 0]

-- Cycle fingerprint bae473f0cf77d3643d49a656866b90150b7987d499a69e39ba9821ab8a453bd9.
def localCycle00192 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 3, .distance 2 3, .distance 3 4, .distance 4 5, .distance 5 6, .distance 0 5, .theta 0, .zero]
    constant := ![0, 3, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 3, .corridorUpper 2 3, .triangle 25 0, .triangle 31 0, .triangle 34 0, .triangle 14 0, .corridorLower 0 5, .thetaLower 0]

-- Cycle fingerprint bb0c4604c1ff2f5a6439d7852b0454e86daa3a4f8eba5daefc940b023de28a77.
def localCycle00193 : Cycle where
  length := 6
  data := {
    node := ![.distance 1 6, .distance 0 1, .theta 0, .zero, .theta 1, .distance 1 4, .distance 1 6]
    constant := ![-1, -1, 0, 0, 2, -2]
    coefficient := ![0, 0, 0, 1, 1, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.triangle 4 0, .corridorLower 0 1, .thetaLower 0, .thetaUpper 1, .gapLower 1 6, .gapLower 1 5]

-- Cycle fingerprint bbd39cc5d8f88b8395c699f46c3f7a8f271a2704e5d83ec925e1c8cd3baa3a41.
def localCycle00194 : Cycle where
  length := 4
  data := {
    node := ![.distance 2 5, .distance 3 5, .distance 1 3, .distance 1 2, .distance 2 5]
    constant := ![0, -1, -2, 2]
    coefficient := ![0, 0, 0, 0]
    strict := ![false, false, false, true] }
  origin := ![.gapLower 5 4, .triangle 20 0, .gapLower 1 2, .gapUpper 2 2]

-- Cycle fingerprint bfbfdf4ad55a4b75c2c1974e9abb473c29c33e2974e0755b9b148edb0e660b74.
def localCycle00195 : Cycle where
  length := 4
  data := {
    node := ![.distance 1 3, .distance 1 2, .distance 2 4, .distance 3 4, .distance 1 3]
    constant := ![-3, 2, 0, -1]
    coefficient := ![0, 0, 0, 0]
    strict := ![false, true, false, false] }
  origin := ![.gapLower 1 2, .gapUpper 2 2, .gapLower 4 3, .triangle 19 0]

-- Cycle fingerprint c060cf39826d25f5074069dba6cc984939d4c186d24e9324d877e18f41ab67cc.
def localCycle00196 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 3, .distance 3 6, .distance 1 6, .distance 5 6, .distance 4 5, .theta 4]
    constant := ![3, -1, -1, 0, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 0, .triangle 27 0, .triangle 21 2, .triangle 24 1, .triangle 34 0, .corridorLower 4 5]

-- Cycle fingerprint c3ae41357667c62c5beffdf56fba555c5faf547f45d97a40a2c9c5047ad22574.
def localCycle00197 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 2 3, .distance 3 5, .distance 1 3, .distance 1 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, -1, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 25 0, .triangle 26 0, .triangle 20 0, .triangle 15 1, .triangle 0 0, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint c46ef43eae6d4674bb9e1a6c2f26f8b36287f951850f61adbb092378916c9b57.
def localCycle00198 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 4, .distance 4 5, .distance 1 4, .distance 4 6, .distance 5 6, .distance 0 5, .distance 0 3, .theta 3]
    constant := ![3, -1, -1, -1, -1, 0, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 25 0, .triangle 31 0, .triangle 22 0, .triangle 23 0, .triangle 34 1, .triangle 14 0, .triangle 10 1, .gapLower 3 0]

-- Cycle fingerprint c74371dc20f18eb693a48591b56f699d66fde873f65b78557677c6c4f3e85b6a.
def localCycle00199 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 4, .distance 2 4, .distance 4 5, .distance 1 4, .distance 1 3, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, -1, 0, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false, true, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 0, .triangle 25 2, .triangle 28 0, .triangle 22 0, .triangle 19 1, .triangle 1 0, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint c828d2b9618316f3cc8be78a7d6ee0e35d94070ab19b83cbc8b31234d4752206.
def localCycle00200 : Cycle where
  length := 8
  data := {
    node := ![.distance 4 5, .distance 0 4, .distance 0 3, .distance 0 1, .theta 1, .distance 1 4, .distance 1 5, .distance 5 6, .distance 4 5]
    constant := ![-1, 0, 0, 0, 1, 0, -1, -1]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![false, false, true, false, false, true, false, false] }
  origin := ![.triangle 12 0, .gapLower 0 3, .triangle 1 1, .gapLower 1 0, .gapLower 1 6, .triangle 22 2, .triangle 24 0, .triangle 34 0]

-- Cycle fingerprint c986a308d5f430a49a9f823e70e271477051a2f0473778c4737afc4b1ea96277.
def localCycle00201 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 2 4, .distance 4 5, .distance 1 4, .distance 4 6, .distance 0 4, .distance 0 3, .distance 0 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, -1, -1, -1, -1, 0, 0, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, true, true, true, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 28 0, .triangle 22 0, .triangle 23 0, .triangle 13 0, .triangle 9 1, .triangle 5 1, .triangle 0 1, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint cb0fd1135bc01f7aef997895dccb60ba3c5c6fcbb95ea1452bd8c853ec3365f9.
def localCycle00202 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 3, .distance 2 3, .distance 2 4, .distance 4 6, .distance 4 5, .distance 3 4, .distance 1 3, .distance 1 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, -1, 0, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false, true, false, false, false] }
  origin := ![.thetaUpper 3, .corridorUpper 2 3, .triangle 25 2, .triangle 29 0, .triangle 34 1, .triangle 31 0, .triangle 19 0, .triangle 15 1, .triangle 0 0, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint cd243d7120f52ab2959d12743a54052201efccc8d62da8b91c86d82e83c78750.
def localCycle00203 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 2, .distance 0 1, .theta 1, .zero, .theta 3, .distance 2 3, .distance 3 6, .distance 3 4, .distance 1 3, .distance 1 2]
    constant := ![-1, -3, 0, 0, 3, -1, 0, -1, 0]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, false, false] }
  origin := ![.triangle 0 0, .gapLower 1 0, .thetaLower 1, .thetaUpper 3, .corridorUpper 2 3, .triangle 27 0, .triangle 32 1, .triangle 19 0, .gapLower 1 2]

-- Cycle fingerprint cd5ae6d6c30ee8a95b7539ecfd36ac2cccb3c9ef67c88b517bd3a9813d6a0a37.
def localCycle00204 : Cycle where
  length := 7
  data := {
    node := ![.theta 1, .distance 1 4, .distance 4 6, .distance 4 5, .distance 0 4, .distance 0 3, .distance 0 1, .theta 1]
    constant := ![2, -1, 0, -1, 0, 0, -2]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, false] }
  origin := ![.gapLower 1 6, .triangle 23 0, .triangle 34 1, .triangle 12 0, .gapLower 0 3, .triangle 1 1, .gapLower 1 0]

-- Cycle fingerprint ce7eac70bacb67eec2af6111238ac1c29f8eaabcd027f39a29ac7ed39c135144.
def localCycle00205 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 3, .distance 1 2, .distance 0 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 2 4, .distance 1 4, .distance 1 5, .distance 1 3]
    constant := ![-2, -1, -1, 0, 0, 3, 0, 0, -2, 0]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, true, false, true] }
  origin := ![.gapLower 1 2, .triangle 0 0, .corridorLower 0 1, .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 16 2, .gapLower 1 5, .triangle 20 1]

-- Cycle fingerprint cf9d65205598f494bc3ecb35f4553290cc5f0b7918118c92a0317a47f9b274c6.
def localCycle00206 : Cycle where
  length := 3
  data := {
    node := ![.distance 4 5, .distance 1 4, .distance 1 5, .distance 4 5]
    constant := ![2, -2, 0]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.gapUpper 4 2, .gapLower 1 4, .triangle 22 1]

-- Cycle fingerprint cfa0539ed448bff5c39132ad53889df9463ca5011fc791dca9d309d1449d90e8.
def localCycle00207 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 4, .distance 3 5, .distance 5 6, .distance 4 6, .distance 1 4, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, -1, 0, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false, false, true] }
  origin := ![.corridorUpper 2 3, .triangle 25 0, .triangle 31 2, .triangle 33 0, .triangle 34 2, .triangle 23 0, .triangle 22 0, .corridorLower 4 5, .thetaNext 3]

-- Cycle fingerprint cff5b0f0e0e16694284da45241c2b95c78495e398e3cc1fb5b1c239d35b9a312.
def localCycle00208 : Cycle where
  length := 11
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 3 4, .distance 4 6, .distance 4 5, .distance 1 4, .distance 1 3, .distance 1 2, .distance 0 1]
    constant := ![-1, 0, 0, 3, -1, -1, 0, -1, 0, 0, -1]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, false, true, true, false] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 25 0, .triangle 32 0, .triangle 34 1, .triangle 22 0, .triangle 19 1, .triangle 15 1, .triangle 0 0]

-- Cycle fingerprint d2b52bfb812bab67ba644b3e9f2fb2aed407bd069c76d4eb59c0e1ce6ec6202b.
def localCycle00209 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 5, .distance 1 3, .distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 3 6, .distance 1 6, .distance 1 4, .distance 1 5]
    constant := ![-2, -1, -1, 0, 0, 3, -1, 0, -2, 0]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false, false, true] }
  origin := ![.gapLower 1 3, .triangle 1 0, .corridorLower 0 1, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 27 0, .gapLower 6 2, .gapLower 1 5, .triangle 22 2]

-- Cycle fingerprint d3495387c7f8517c77914a65f4fe62254936423ffa3b3e118f6bc15a9ca16f8e.
def localCycle00210 : Cycle where
  length := 5
  data := {
    node := ![.distance 1 6, .distance 1 5, .distance 1 3, .theta 1, .distance 1 4, .distance 1 6]
    constant := ![0, -2, -1, 2, 0]
    coefficient := ![0, 0, 0, 1, 0]
    strict := ![true, false, false, false, true] }
  origin := ![.triangle 24 1, .gapLower 1 3, .corridorLower 1 3, .gapLower 1 6, .triangle 23 2]

-- Cycle fingerprint da065135bdd6b0066b7a886eb280474fa8c4b15d1fd787bc5b1cf3afb60fec1c.
def localCycle00211 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 3, .distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 3 5, .distance 3 6, .distance 1 6, .distance 1 4, .distance 1 3]
    constant := ![-1, -1, 0, 0, 3, -1, 0, 0, -2, -2]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, false, false, false] }
  origin := ![.triangle 1 0, .corridorLower 0 1, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 26 0, .triangle 33 2, .gapLower 6 3, .gapLower 1 4, .gapLower 1 3]

-- Cycle fingerprint daf37f6d409580d1ab541cbc794b15b20a5d24bd9366b64c79714273bb4c43f8.
def localCycle00212 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 3, .distance 2 3, .distance 2 5, .distance 5 6, .distance 3 5, .distance 3 4, .distance 1 3, .distance 1 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, -1, -1, 0, -1, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, true, false, false, false] }
  origin := ![.thetaUpper 3, .corridorUpper 2 3, .triangle 26 2, .triangle 30 0, .triangle 33 0, .gapLower 3 3, .triangle 19 0, .triangle 15 1, .triangle 0 0, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint dbd544b4eed28e3795f64e026e5dc32ae783ec6805f7124b02a379cfda623c4d.
def localCycle00213 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 2 5, .distance 5 6, .distance 4 6, .distance 1 4, .distance 4 5, .theta 4]
    constant := ![3, 0, 0, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 28 2, .triangle 30 0, .triangle 34 2, .triangle 23 0, .triangle 22 0, .corridorLower 4 5]

-- Cycle fingerprint dc46fca43f2b24c613c73ae3033f2fe5d468857935b12a42ede5c0a5344601ec.
def localCycle00214 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 3, .distance 1 2, .distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 3 5, .distance 3 4, .distance 1 3]
    constant := ![0, -2, -1, 0, 0, 3, -1, 0, -1]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, true, false] }
  origin := ![.gapLower 1 2, .gapLower 1 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 26 0, .triangle 31 1, .triangle 19 0]

-- Cycle fingerprint dd6e9eae4035d02cd2001fd36658a9c57791504f69625de100484ecebc117f3b.
def localCycle00215 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 3, .distance 0 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 2 4, .distance 1 4, .distance 1 5, .distance 1 6, .distance 1 3]
    constant := ![-1, -1, 0, 0, 3, 0, 0, 0, -2, -2]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, true, false, false] }
  origin := ![.triangle 1 0, .corridorLower 0 1, .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 16 2, .triangle 22 2, .gapLower 1 4, .gapLower 1 3]

-- Cycle fingerprint de02403d8fbfc80e01f7e776e0a32c219176b85d5bb6fff8e5f42564ce1b07b7.
def localCycle00216 : Cycle where
  length := 11
  data := {
    node := ![.theta 0, .zero, .theta 3, .distance 2 3, .distance 3 5, .distance 3 6, .distance 1 6, .distance 1 4, .distance 1 3, .distance 1 2, .distance 0 1, .theta 0]
    constant := ![0, 0, 3, -1, 0, 0, -2, 0, -2, -1, -1]
    coefficient := ![0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, true, false, false, false] }
  origin := ![.thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 26 0, .triangle 33 2, .gapLower 6 3, .gapLower 1 4, .triangle 19 1, .gapLower 1 2, .triangle 0 0, .corridorLower 0 1]

-- Cycle fingerprint e1212cba1de0320fd65a6ed62a1bea073ff44624fd3b3b922be11412c8146a45.
def localCycle00217 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 2, .distance 0 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 2 3, .distance 1 2]
    constant := ![-2, -1, 0, 0, 3, -1, -1]
    coefficient := ![0, 0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 1 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 25 0, .triangle 15 0]

-- Cycle fingerprint e30bbf6e26d7fe95291cfe94ea0f7700bc3b18654e38ed415f5ff70ccdfebb8c.
def localCycle00218 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 4, .distance 4 6, .distance 2 4, .distance 2 3, .distance 1 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, -1, -1, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 0, .triangle 32 0, .triangle 29 0, .triangle 25 1, .triangle 15 0, .triangle 0 0, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint e3ace8397b166097bc74160ab13f3ebf203049c9b3025084dae8a7fae5a2f4a2.
def localCycle00219 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 3 4, .distance 3 5, .distance 5 6, .distance 4 6, .distance 1 4, .distance 4 5, .theta 4]
    constant := ![3, 0, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 31 2, .triangle 33 0, .triangle 34 2, .triangle 23 0, .triangle 22 0, .corridorLower 4 5]

-- Cycle fingerprint e3b8bdefc3e6b35b00bc93f2cc5b492776dfdea9b682178a0fa6923ed883b6e3.
def localCycle00220 : Cycle where
  length := 10
  data := {
    node := ![.distance 2 3, .distance 1 2, .distance 0 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 4 5, .distance 4 6, .distance 2 4, .distance 2 3]
    constant := ![-1, -1, -1, 0, 0, 3, -1, 0, -1, 0]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, true, false, true] }
  origin := ![.triangle 15 0, .triangle 0 0, .corridorLower 0 1, .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 31 0, .triangle 34 2, .triangle 29 0, .triangle 25 1]

-- Cycle fingerprint e548f077e858307e81a64454f7c15f6ba221b492de1eee96f26d56c852447f0b.
def localCycle00221 : Cycle where
  length := 3
  data := {
    node := ![.distance 1 6, .theta 1, .distance 1 4, .distance 1 6]
    constant := ![-1, 2, -2]
    coefficient := ![0, 1, 0]
    strict := ![false, false, false] }
  origin := ![.corridorLower 1 6, .gapLower 1 6, .gapLower 1 5]

-- Cycle fingerprint e67bcb6414031ca48194614c1f48500d26af2b2a8da802daffcaac113ea0ef63.
def localCycle00222 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 4, .distance 0 3, .theta 0, .zero, .theta 1, .distance 1 4, .distance 4 6, .distance 4 5, .distance 0 4]
    constant := ![0, -1, 0, 0, 1, -1, 0, -1]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, false] }
  origin := ![.gapLower 0 3, .corridorLower 0 3, .thetaLower 0, .thetaUpper 1, .gapLower 1 6, .triangle 23 0, .triangle 34 1, .triangle 12 0]

-- Cycle fingerprint e7bbf0ca567083c7971af3ae49b5655de6e5792bf0cd032c9dc31503152129f7.
def localCycle00223 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 4, .distance 0 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 2 4, .distance 4 5, .distance 1 5, .distance 1 6, .distance 1 4]
    constant := ![-1, -1, 0, 0, 3, 0, -1, 0, -2, -2]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, false, false, false] }
  origin := ![.triangle 2 0, .corridorLower 0 1, .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 28 0, .gapLower 5 3, .gapLower 1 5, .gapLower 1 4]

-- Cycle fingerprint e828903d6c7060c8c6444c2541408fedb0f7acbda7eb526ff5da503cb6beae21.
def localCycle00224 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 2 4, .distance 4 5, .distance 3 4, .distance 1 3, .distance 1 2, .distance 0 1]
    constant := ![-1, 0, 0, 3, 0, -1, -1, -1, 0, -1]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, false, true, false] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 25 2, .triangle 28 0, .triangle 31 0, .triangle 19 0, .triangle 15 1, .triangle 0 0]

-- Cycle fingerprint e93f3c30fb3b3c1d3380e9b232515382d96e28b0eb98876e7d7281eb25ec0482.
def localCycle00225 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 3, .distance 2 3, .distance 3 5, .distance 3 6, .distance 1 6, .distance 1 4, .distance 1 3, .distance 1 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, -1, 0, 0, 0, -2, 0, -2, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true, false, true, false, false, false] }
  origin := ![.thetaUpper 3, .corridorUpper 2 3, .triangle 26 0, .triangle 33 2, .gapLower 6 3, .triangle 23 1, .gapLower 1 3, .triangle 15 1, .gapLower 1 1, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint ea465190b3de5114e2afbc87cae3b5773bfc603e2689a593fd66c480d72a8f09.
def localCycle00226 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 3, .distance 1 2, .distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 3 5, .distance 1 5, .distance 1 6, .distance 1 3]
    constant := ![-2, -1, -1, 0, 0, 3, -1, 0, -2, 0]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false, false, true] }
  origin := ![.gapLower 1 2, .triangle 0 0, .corridorLower 0 1, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 26 0, .gapLower 5 3, .gapLower 1 5, .triangle 21 1]

-- Cycle fingerprint ea6c83cbbeb2162100c3d747bc32b864ba5e1edabda59a30354cdbe718907a9a.
def localCycle00227 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 3, .distance 1 2, .distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 3 6, .distance 1 6, .distance 1 4, .distance 1 3]
    constant := ![-2, -1, -1, 0, 0, 3, -1, 0, -2, 0]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false, false, true] }
  origin := ![.gapLower 1 2, .triangle 0 0, .corridorLower 0 1, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 27 0, .gapLower 6 2, .gapLower 1 5, .triangle 19 1]

-- Cycle fingerprint ed7a0d3a50389df90869beb76c7632a00d2da12392aaa754f708d20de046f854.
def localCycle00228 : Cycle where
  length := 13
  data := {
    node := ![.distance 2 4, .distance 1 4, .distance 1 5, .distance 1 6, .distance 5 6, .distance 4 5, .distance 0 4, .distance 0 3, .distance 0 1, .theta 1, .zero, .theta 4, .distance 3 4, .distance 2 4]
    constant := ![0, 0, -2, 0, -1, -1, 0, 0, -2, 0, 0, 3, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![true, true, false, true, false, false, false, true, false, false, false, false, true] }
  origin := ![.triangle 16 2, .triangle 22 2, .gapLower 1 4, .triangle 24 1, .triangle 34 0, .triangle 12 0, .gapLower 0 3, .triangle 1 1, .gapLower 1 0, .thetaLower 1, .thetaUpper 4, .corridorUpper 3 4, .triangle 25 2]

-- Cycle fingerprint ee842431375993a76b3d54ab333f7a3eb140d648120d1b83c35b2bc5016340a5.
def localCycle00229 : Cycle where
  length := 11
  data := {
    node := ![.distance 0 1, .theta 1, .zero, .theta 4, .distance 3 4, .distance 2 4, .distance 2 5, .distance 5 6, .distance 4 5, .distance 0 4, .distance 0 3, .distance 0 1]
    constant := ![-2, 0, 0, 3, 0, 0, -1, -1, -1, 0, 0]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, false, false, false, false, true] }
  origin := ![.gapLower 1 0, .thetaLower 1, .thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 28 2, .triangle 30 0, .triangle 34 0, .triangle 12 0, .gapLower 0 3, .triangle 1 1]

-- Cycle fingerprint ee93e6ef96d7c1b6fa0aedda5cf5a356ef43a9938cb3977e8ead3e1beb843091.
def localCycle00230 : Cycle where
  length := 11
  data := {
    node := ![.distance 3 6, .distance 5 6, .distance 4 5, .distance 1 4, .distance 1 3, .distance 0 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 2 3, .distance 3 6]
    constant := ![0, -1, -1, 0, -1, -1, 0, 0, 3, -1, -1]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![true, false, false, false, false, false, false, false, false, false, false] }
  origin := ![.triangle 33 1, .triangle 34 0, .triangle 22 0, .gapLower 1 3, .triangle 1 0, .corridorLower 0 1, .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 25 0, .triangle 27 0]

-- Cycle fingerprint ef245370cb93314d3177a6b37a1ff12011f35e7c34cc3a74ec42cdfadd7d96d5.
def localCycle00231 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 5 6, .distance 3 5, .distance 3 4, .distance 2 3, .distance 1 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, -1, -1, 0, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 34 0, .triangle 33 0, .triangle 31 1, .triangle 25 0, .triangle 15 0, .triangle 0 0, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint ef4cfe4a99231008ef49ba7099b0478f8e7685c127b57242abb814053657bbcf.
def localCycle00232 : Cycle where
  length := 9
  data := {
    node := ![.distance 2 4, .distance 1 4, .distance 1 6, .distance 1 2, .distance 0 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 2 4]
    constant := ![0, -2, 0, -2, -1, 0, 0, 3, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![true, false, true, false, false, false, false, false, true] }
  origin := ![.triangle 16 2, .gapLower 1 5, .triangle 18 1, .gapLower 1 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 25 2]

-- Cycle fingerprint f0521cbfc10c52e81c0844c917259e3b0c74f93d0ef5517207a7c29e98caf805.
def localCycle00233 : Cycle where
  length := 3
  data := {
    node := ![.distance 4 5, .distance 1 4, .distance 1 5, .distance 4 5]
    constant := ![2, -3, 0]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.gapUpper 4 3, .gapLower 1 5, .triangle 22 1]

-- Cycle fingerprint f1666bb182c17661d936fee0c378777be8ef35620c006a577529490ccecfac23.
def localCycle00234 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 1, .distance 1 4, .distance 1 5, .distance 4 5, .distance 5 6, .distance 0 5, .distance 0 4, .theta 0, .zero]
    constant := ![0, 2, -2, 0, -1, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, false, false] }
  origin := ![.thetaUpper 1, .gapLower 1 6, .gapLower 1 5, .triangle 22 1, .triangle 34 0, .triangle 14 0, .gapLower 0 4, .corridorLower 0 4, .thetaLower 0]

-- Cycle fingerprint f2ef6e694badc7a9dfe1b429a6b451939fd1a4faf9942801912cf1af4ce67d8e.
def localCycle00235 : Cycle where
  length := 11
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 4, .distance 3 6, .distance 3 5, .distance 1 3, .distance 1 2, .distance 0 1, .theta 1, .theta 0, .zero, .theta 3]
    constant := ![3, -1, 0, 0, -1, 0, -2, -2, 0, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![false, false, true, true, false, false, false, false, true, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 25 0, .triangle 32 2, .triangle 33 1, .triangle 20 0, .gapLower 1 2, .gapLower 1 1, .gapLower 1 0, .thetaNext 0, .thetaLower 0, .thetaUpper 3]

-- Cycle fingerprint f4773fc25ee25c45d12fdaf4771f45ccc72e155f0324cf8547a7db408e765521.
def localCycle00236 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .theta 1, .zero, .theta 4, .distance 3 4, .distance 2 4, .distance 4 5, .distance 4 6, .distance 1 4, .distance 1 3, .distance 0 1]
    constant := ![-2, 0, 0, 3, 0, -1, 0, -1, -2, -1]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, true, false, false, false] }
  origin := ![.gapLower 1 0, .thetaLower 1, .thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 28 0, .triangle 34 2, .triangle 23 0, .gapLower 1 3, .triangle 1 0]

-- Cycle fingerprint f4aa6c9bf671a1c495c8505cad9536e30ea47b47e142259b72b0c65a698ce8bc.
def localCycle00237 : Cycle where
  length := 11
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 2 5, .distance 5 6, .distance 1 5, .distance 1 3, .distance 1 2, .distance 0 1, .theta 1, .zero, .theta 4]
    constant := ![3, 0, 0, -1, -1, 0, -2, -1, -2, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, true, false, false, false, false, false, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 28 2, .triangle 30 0, .triangle 24 0, .gapLower 1 3, .gapLower 1 2, .triangle 0 0, .gapLower 1 0, .thetaLower 1, .thetaUpper 4]

-- Cycle fingerprint f5d49a280817d08db13e784f24359c90431e6d34c359200854c33e3485bdc64c.
def localCycle00238 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 3, .distance 1 2, .distance 0 1, .theta 1, .zero, .theta 4, .distance 3 4, .distance 1 3]
    constant := ![-2, -1, -2, 0, 0, 3, -1]
    coefficient := ![0, 0, 0, 0, 1, 1, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 1 2, .triangle 0 0, .gapLower 1 0, .thetaLower 1, .thetaUpper 4, .corridorUpper 3 4, .triangle 19 0]

-- Cycle fingerprint f6805526d2e205fd53e4666f8b983282c70aed5007bf3aa5a55f4a12edc51a9c.
def localCycle00239 : Cycle where
  length := 7
  data := {
    node := ![.theta 1, .distance 1 4, .distance 4 5, .distance 5 6, .distance 0 5, .distance 0 4, .distance 0 1, .theta 1]
    constant := ![1, -1, -1, -1, 0, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false] }
  origin := ![.gapLower 1 6, .triangle 22 0, .triangle 34 0, .triangle 14 0, .gapLower 0 4, .triangle 2 1, .gapLower 1 0]

-- Cycle fingerprint f822349d8725ac4e86bf50864f7d7379d2ab70c57165ee1b8dcc8fc14700e52c.
def localCycle00240 : Cycle where
  length := 12
  data := {
    node := ![.distance 3 4, .distance 2 4, .distance 2 5, .distance 5 6, .distance 1 6, .distance 1 5, .distance 1 3, .distance 1 2, .distance 0 1, .theta 1, .zero, .theta 4, .distance 3 4]
    constant := ![0, 0, -1, 0, -2, 0, 0, -1, -2, 0, 0, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1]
    strict := ![true, true, false, false, false, true, true, false, false, false, false, false] }
  origin := ![.triangle 25 2, .triangle 28 2, .triangle 30 0, .gapLower 6 3, .gapLower 1 4, .triangle 20 1, .triangle 15 1, .triangle 0 0, .gapLower 1 0, .thetaLower 1, .thetaUpper 4, .corridorUpper 3 4]

-- Cycle fingerprint f84183ad9de4f4df9de63ba703a80b4baddb01863458b94b810d7889735ce0d0.
def localCycle00241 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 2 4, .distance 2 5, .distance 5 6, .distance 1 5, .distance 1 3, .distance 1 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, 0, -1, -1, -2, 0, -2, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, true, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 28 2, .triangle 30 0, .triangle 24 0, .gapLower 1 3, .triangle 15 1, .gapLower 1 1, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint f8956432bf5bb39f46ca001fc8d2ac149f57409128b6660f15c7c81325008600.
def localCycle00242 : Cycle where
  length := 5
  data := {
    node := ![.theta 5, .distance 4 5, .distance 2 4, .distance 2 6, .theta 6, .theta 5]
    constant := ![3, -1, 0, -2, 0]
    coefficient := ![1, 0, 0, -1, 0]
    strict := ![false, false, true, true, true] }
  origin := ![.corridorUpper 4 5, .triangle 28 0, .triangle 29 2, .gapUpper 6 6, .thetaNext 5]

-- Cycle fingerprint fa562680b29ae375cf4601ea4d55ad10c8f30de874f3a47a23472e15e3a57195.
def localCycle00243 : Cycle where
  length := 12
  data := {
    node := ![.distance 3 4, .distance 2 4, .distance 2 5, .distance 5 6, .distance 1 6, .distance 1 5, .distance 1 3, .distance 1 2, .distance 0 1, .theta 0, .zero, .theta 4, .distance 3 4]
    constant := ![0, 0, -1, 0, -2, 0, -2, -1, -1, 0, 0, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1]
    strict := ![true, true, false, false, false, true, false, false, false, false, false, false] }
  origin := ![.triangle 25 2, .triangle 28 2, .triangle 30 0, .gapLower 6 3, .gapLower 1 4, .triangle 20 1, .gapLower 1 2, .triangle 0 0, .corridorLower 0 1, .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4]

-- Cycle fingerprint fa5f473766429c6ba0a5944f946914ec7294e3225484289b768d564267338c25.
def localCycle00244 : Cycle where
  length := 14
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 3, .distance 3 4, .distance 4 6, .distance 5 6, .distance 0 5, .distance 0 4, .distance 0 3, .distance 0 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, -1, -1, -1, 0, -1, 0, 0, 0, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, true, false, true, true, true, true, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 0, .triangle 25 0, .triangle 32 0, .triangle 34 1, .triangle 14 0, .triangle 12 1, .triangle 9 1, .triangle 5 1, .triangle 0 1, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint fbcf7218606e93168e6d4e488e993c6c5f0ed3a9bcc4da0d5db2907b9f8b0305.
def localCycle00245 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 5 6, .distance 2 5, .distance 2 3, .distance 3 4, .distance 1 3, .distance 1 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, -1, -1, 0, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, false, false, true, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 33 0, .triangle 30 0, .triangle 26 1, .triangle 25 0, .triangle 19 0, .triangle 15 1, .triangle 0 0, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint fbcfddee3b67bbc339d692ae0818064ccc06172fbda5d4c5e3d5885fd6808b09.
def localCycle00246 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 2 4, .distance 1 4, .distance 1 5, .distance 4 5, .distance 5 6, .distance 0 5, .distance 0 4, .distance 0 1, .theta 1, .zero]
    constant := ![0, 3, 0, 0, -2, 0, -1, -1, 0, 0, -2, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, true, false, false, false, true, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 16 2, .gapLower 1 5, .triangle 22 1, .triangle 34 0, .triangle 14 0, .gapLower 0 4, .triangle 2 1, .gapLower 1 0, .thetaLower 1]

-- Cycle fingerprint fca070087854c708a5c8dcbec416ae3c16774cdad29d5d39fa7d7ae5e25d40a0.
def localCycle00247 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 3, .distance 2 3, .distance 3 6, .distance 3 4, .distance 4 5, .distance 1 4, .distance 1 3, .distance 1 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, -1, 0, -1, -1, 0, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, true, true, false, false, false] }
  origin := ![.thetaUpper 3, .corridorUpper 2 3, .triangle 27 0, .triangle 32 1, .triangle 31 0, .triangle 22 0, .triangle 19 1, .triangle 15 1, .triangle 0 0, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint fce112f4457e98f12cabab95cc76242cf15ee66ac0eda16abb11a84b3164777a.
def localCycle00248 : Cycle where
  length := 8
  data := {
    node := ![.distance 2 5, .distance 5 6, .distance 1 6, .distance 1 5, .distance 4 5, .theta 4, .distance 3 4, .distance 2 4, .distance 2 5]
    constant := ![-1, 0, -2, 0, -1, 3, 0, 0]
    coefficient := ![0, 0, 0, 0, 0, 1, 0, 0]
    strict := ![false, true, false, true, false, false, true, true] }
  origin := ![.triangle 30 0, .triangle 24 2, .gapLower 1 4, .triangle 22 1, .corridorLower 4 5, .corridorUpper 3 4, .triangle 25 2, .triangle 28 2]

-- Cycle fingerprint fd76da20dbb10c6148d863f1a665f68139f2e8f186815a75a3047a89d02d6b71.
def localCycle00249 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 2 4, .distance 4 5, .distance 4 6, .distance 1 6, .distance 1 4, .distance 1 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, -1, 0, 0, -2, 0, -2, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, true, false, true, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 28 0, .triangle 34 2, .triangle 23 2, .gapLower 1 4, .triangle 16 1, .gapLower 1 1, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint fd80dc281964c72c058ce0c1b0703ae621a2304cb7d20ddab7838657b65c7746.
def localCycle00250 : Cycle where
  length := 11
  data := {
    node := ![.distance 2 4, .distance 2 5, .distance 5 6, .distance 1 5, .distance 1 3, .distance 1 2, .distance 0 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 2 4]
    constant := ![0, -1, -1, 0, -2, -1, -1, 0, 0, 3, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![true, false, false, false, false, false, false, false, false, false, true] }
  origin := ![.triangle 28 2, .triangle 30 0, .triangle 24 0, .gapLower 1 3, .gapLower 1 2, .triangle 0 0, .corridorLower 0 1, .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 25 2]

-- Cycle fingerprint fe5f31d128574398a3b0e75657c6ecca61f2515987350de9e1dc8c4ac2cc485f.
def localCycle00251 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 2 4, .distance 4 5, .distance 4 6, .distance 1 4, .distance 1 3, .distance 0 1]
    constant := ![-1, 0, 0, 3, 0, -1, 0, -1, -2, -1]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, true, false, false, false] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 28 0, .triangle 34 2, .triangle 23 0, .gapLower 1 3, .triangle 1 0]

-- Cycle fingerprint feabd674f5a6e9569eb0951a95dfba7d0cc1132b876547b22ea142d6154bf770.
def localCycle00252 : Cycle where
  length := 3
  data := {
    node := ![.distance 4 6, .distance 1 4, .distance 1 6, .distance 4 6]
    constant := ![2, -2, 0]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.gapUpper 4 3, .gapLower 1 5, .triangle 23 1]

-- Cycle fingerprint fecd6625ec7f57e80c2a6318520207702a99931e99171f87bfef249857265d69.
def localCycle00253 : Cycle where
  length := 11
  data := {
    node := ![.theta 0, .zero, .theta 3, .distance 2 3, .distance 3 6, .distance 3 4, .distance 1 4, .distance 1 5, .distance 1 3, .distance 1 2, .distance 0 1, .theta 0]
    constant := ![0, 0, 3, -1, 0, 0, -2, 0, -2, -1, -1]
    coefficient := ![0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, true, false, false, false] }
  origin := ![.thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 27 0, .triangle 32 1, .gapLower 4 3, .gapLower 1 4, .triangle 20 1, .gapLower 1 2, .triangle 0 0, .corridorLower 0 1]

def library : Library := fun id => if id < 127 then (if id < 63 then (if id < 31 then (if id < 15 then (if id < 7 then (if id < 3 then (if id < 1 then (if id = 0 then some localCycle00000 else none) else (if id < 2 then (if id = 1 then some localCycle00001 else none) else (if id = 2 then some localCycle00002 else none))) else (if id < 5 then (if id < 4 then (if id = 3 then some localCycle00003 else none) else (if id = 4 then some localCycle00004 else none)) else (if id < 6 then (if id = 5 then some localCycle00005 else none) else (if id = 6 then some localCycle00006 else none)))) else (if id < 11 then (if id < 9 then (if id < 8 then (if id = 7 then some localCycle00007 else none) else (if id = 8 then some localCycle00008 else none)) else (if id < 10 then (if id = 9 then some localCycle00009 else none) else (if id = 10 then some localCycle00010 else none))) else (if id < 13 then (if id < 12 then (if id = 11 then some localCycle00011 else none) else (if id = 12 then some localCycle00012 else none)) else (if id < 14 then (if id = 13 then some localCycle00013 else none) else (if id = 14 then some localCycle00014 else none))))) else (if id < 23 then (if id < 19 then (if id < 17 then (if id < 16 then (if id = 15 then some localCycle00015 else none) else (if id = 16 then some localCycle00016 else none)) else (if id < 18 then (if id = 17 then some localCycle00017 else none) else (if id = 18 then some localCycle00018 else none))) else (if id < 21 then (if id < 20 then (if id = 19 then some localCycle00019 else none) else (if id = 20 then some localCycle00020 else none)) else (if id < 22 then (if id = 21 then some localCycle00021 else none) else (if id = 22 then some localCycle00022 else none)))) else (if id < 27 then (if id < 25 then (if id < 24 then (if id = 23 then some localCycle00023 else none) else (if id = 24 then some localCycle00024 else none)) else (if id < 26 then (if id = 25 then some localCycle00025 else none) else (if id = 26 then some localCycle00026 else none))) else (if id < 29 then (if id < 28 then (if id = 27 then some localCycle00027 else none) else (if id = 28 then some localCycle00028 else none)) else (if id < 30 then (if id = 29 then some localCycle00029 else none) else (if id = 30 then some localCycle00030 else none)))))) else (if id < 47 then (if id < 39 then (if id < 35 then (if id < 33 then (if id < 32 then (if id = 31 then some localCycle00031 else none) else (if id = 32 then some localCycle00032 else none)) else (if id < 34 then (if id = 33 then some localCycle00033 else none) else (if id = 34 then some localCycle00034 else none))) else (if id < 37 then (if id < 36 then (if id = 35 then some localCycle00035 else none) else (if id = 36 then some localCycle00036 else none)) else (if id < 38 then (if id = 37 then some localCycle00037 else none) else (if id = 38 then some localCycle00038 else none)))) else (if id < 43 then (if id < 41 then (if id < 40 then (if id = 39 then some localCycle00039 else none) else (if id = 40 then some localCycle00040 else none)) else (if id < 42 then (if id = 41 then some localCycle00041 else none) else (if id = 42 then some localCycle00042 else none))) else (if id < 45 then (if id < 44 then (if id = 43 then some localCycle00043 else none) else (if id = 44 then some localCycle00044 else none)) else (if id < 46 then (if id = 45 then some localCycle00045 else none) else (if id = 46 then some localCycle00046 else none))))) else (if id < 55 then (if id < 51 then (if id < 49 then (if id < 48 then (if id = 47 then some localCycle00047 else none) else (if id = 48 then some localCycle00048 else none)) else (if id < 50 then (if id = 49 then some localCycle00049 else none) else (if id = 50 then some localCycle00050 else none))) else (if id < 53 then (if id < 52 then (if id = 51 then some localCycle00051 else none) else (if id = 52 then some localCycle00052 else none)) else (if id < 54 then (if id = 53 then some localCycle00053 else none) else (if id = 54 then some localCycle00054 else none)))) else (if id < 59 then (if id < 57 then (if id < 56 then (if id = 55 then some localCycle00055 else none) else (if id = 56 then some localCycle00056 else none)) else (if id < 58 then (if id = 57 then some localCycle00057 else none) else (if id = 58 then some localCycle00058 else none))) else (if id < 61 then (if id < 60 then (if id = 59 then some localCycle00059 else none) else (if id = 60 then some localCycle00060 else none)) else (if id < 62 then (if id = 61 then some localCycle00061 else none) else (if id = 62 then some localCycle00062 else none))))))) else (if id < 95 then (if id < 79 then (if id < 71 then (if id < 67 then (if id < 65 then (if id < 64 then (if id = 63 then some localCycle00063 else none) else (if id = 64 then some localCycle00064 else none)) else (if id < 66 then (if id = 65 then some localCycle00065 else none) else (if id = 66 then some localCycle00066 else none))) else (if id < 69 then (if id < 68 then (if id = 67 then some localCycle00067 else none) else (if id = 68 then some localCycle00068 else none)) else (if id < 70 then (if id = 69 then some localCycle00069 else none) else (if id = 70 then some localCycle00070 else none)))) else (if id < 75 then (if id < 73 then (if id < 72 then (if id = 71 then some localCycle00071 else none) else (if id = 72 then some localCycle00072 else none)) else (if id < 74 then (if id = 73 then some localCycle00073 else none) else (if id = 74 then some localCycle00074 else none))) else (if id < 77 then (if id < 76 then (if id = 75 then some localCycle00075 else none) else (if id = 76 then some localCycle00076 else none)) else (if id < 78 then (if id = 77 then some localCycle00077 else none) else (if id = 78 then some localCycle00078 else none))))) else (if id < 87 then (if id < 83 then (if id < 81 then (if id < 80 then (if id = 79 then some localCycle00079 else none) else (if id = 80 then some localCycle00080 else none)) else (if id < 82 then (if id = 81 then some localCycle00081 else none) else (if id = 82 then some localCycle00082 else none))) else (if id < 85 then (if id < 84 then (if id = 83 then some localCycle00083 else none) else (if id = 84 then some localCycle00084 else none)) else (if id < 86 then (if id = 85 then some localCycle00085 else none) else (if id = 86 then some localCycle00086 else none)))) else (if id < 91 then (if id < 89 then (if id < 88 then (if id = 87 then some localCycle00087 else none) else (if id = 88 then some localCycle00088 else none)) else (if id < 90 then (if id = 89 then some localCycle00089 else none) else (if id = 90 then some localCycle00090 else none))) else (if id < 93 then (if id < 92 then (if id = 91 then some localCycle00091 else none) else (if id = 92 then some localCycle00092 else none)) else (if id < 94 then (if id = 93 then some localCycle00093 else none) else (if id = 94 then some localCycle00094 else none)))))) else (if id < 111 then (if id < 103 then (if id < 99 then (if id < 97 then (if id < 96 then (if id = 95 then some localCycle00095 else none) else (if id = 96 then some localCycle00096 else none)) else (if id < 98 then (if id = 97 then some localCycle00097 else none) else (if id = 98 then some localCycle00098 else none))) else (if id < 101 then (if id < 100 then (if id = 99 then some localCycle00099 else none) else (if id = 100 then some localCycle00100 else none)) else (if id < 102 then (if id = 101 then some localCycle00101 else none) else (if id = 102 then some localCycle00102 else none)))) else (if id < 107 then (if id < 105 then (if id < 104 then (if id = 103 then some localCycle00103 else none) else (if id = 104 then some localCycle00104 else none)) else (if id < 106 then (if id = 105 then some localCycle00105 else none) else (if id = 106 then some localCycle00106 else none))) else (if id < 109 then (if id < 108 then (if id = 107 then some localCycle00107 else none) else (if id = 108 then some localCycle00108 else none)) else (if id < 110 then (if id = 109 then some localCycle00109 else none) else (if id = 110 then some localCycle00110 else none))))) else (if id < 119 then (if id < 115 then (if id < 113 then (if id < 112 then (if id = 111 then some localCycle00111 else none) else (if id = 112 then some localCycle00112 else none)) else (if id < 114 then (if id = 113 then some localCycle00113 else none) else (if id = 114 then some localCycle00114 else none))) else (if id < 117 then (if id < 116 then (if id = 115 then some localCycle00115 else none) else (if id = 116 then some localCycle00116 else none)) else (if id < 118 then (if id = 117 then some localCycle00117 else none) else (if id = 118 then some localCycle00118 else none)))) else (if id < 123 then (if id < 121 then (if id < 120 then (if id = 119 then some localCycle00119 else none) else (if id = 120 then some localCycle00120 else none)) else (if id < 122 then (if id = 121 then some localCycle00121 else none) else (if id = 122 then some localCycle00122 else none))) else (if id < 125 then (if id < 124 then (if id = 123 then some localCycle00123 else none) else (if id = 124 then some localCycle00124 else none)) else (if id < 126 then (if id = 125 then some localCycle00125 else none) else (if id = 126 then some localCycle00126 else none)))))))) else (if id < 190 then (if id < 158 then (if id < 142 then (if id < 134 then (if id < 130 then (if id < 128 then (if id = 127 then some localCycle00127 else none) else (if id < 129 then (if id = 128 then some localCycle00128 else none) else (if id = 129 then some localCycle00129 else none))) else (if id < 132 then (if id < 131 then (if id = 130 then some localCycle00130 else none) else (if id = 131 then some localCycle00131 else none)) else (if id < 133 then (if id = 132 then some localCycle00132 else none) else (if id = 133 then some localCycle00133 else none)))) else (if id < 138 then (if id < 136 then (if id < 135 then (if id = 134 then some localCycle00134 else none) else (if id = 135 then some localCycle00135 else none)) else (if id < 137 then (if id = 136 then some localCycle00136 else none) else (if id = 137 then some localCycle00137 else none))) else (if id < 140 then (if id < 139 then (if id = 138 then some localCycle00138 else none) else (if id = 139 then some localCycle00139 else none)) else (if id < 141 then (if id = 140 then some localCycle00140 else none) else (if id = 141 then some localCycle00141 else none))))) else (if id < 150 then (if id < 146 then (if id < 144 then (if id < 143 then (if id = 142 then some localCycle00142 else none) else (if id = 143 then some localCycle00143 else none)) else (if id < 145 then (if id = 144 then some localCycle00144 else none) else (if id = 145 then some localCycle00145 else none))) else (if id < 148 then (if id < 147 then (if id = 146 then some localCycle00146 else none) else (if id = 147 then some localCycle00147 else none)) else (if id < 149 then (if id = 148 then some localCycle00148 else none) else (if id = 149 then some localCycle00149 else none)))) else (if id < 154 then (if id < 152 then (if id < 151 then (if id = 150 then some localCycle00150 else none) else (if id = 151 then some localCycle00151 else none)) else (if id < 153 then (if id = 152 then some localCycle00152 else none) else (if id = 153 then some localCycle00153 else none))) else (if id < 156 then (if id < 155 then (if id = 154 then some localCycle00154 else none) else (if id = 155 then some localCycle00155 else none)) else (if id < 157 then (if id = 156 then some localCycle00156 else none) else (if id = 157 then some localCycle00157 else none)))))) else (if id < 174 then (if id < 166 then (if id < 162 then (if id < 160 then (if id < 159 then (if id = 158 then some localCycle00158 else none) else (if id = 159 then some localCycle00159 else none)) else (if id < 161 then (if id = 160 then some localCycle00160 else none) else (if id = 161 then some localCycle00161 else none))) else (if id < 164 then (if id < 163 then (if id = 162 then some localCycle00162 else none) else (if id = 163 then some localCycle00163 else none)) else (if id < 165 then (if id = 164 then some localCycle00164 else none) else (if id = 165 then some localCycle00165 else none)))) else (if id < 170 then (if id < 168 then (if id < 167 then (if id = 166 then some localCycle00166 else none) else (if id = 167 then some localCycle00167 else none)) else (if id < 169 then (if id = 168 then some localCycle00168 else none) else (if id = 169 then some localCycle00169 else none))) else (if id < 172 then (if id < 171 then (if id = 170 then some localCycle00170 else none) else (if id = 171 then some localCycle00171 else none)) else (if id < 173 then (if id = 172 then some localCycle00172 else none) else (if id = 173 then some localCycle00173 else none))))) else (if id < 182 then (if id < 178 then (if id < 176 then (if id < 175 then (if id = 174 then some localCycle00174 else none) else (if id = 175 then some localCycle00175 else none)) else (if id < 177 then (if id = 176 then some localCycle00176 else none) else (if id = 177 then some localCycle00177 else none))) else (if id < 180 then (if id < 179 then (if id = 178 then some localCycle00178 else none) else (if id = 179 then some localCycle00179 else none)) else (if id < 181 then (if id = 180 then some localCycle00180 else none) else (if id = 181 then some localCycle00181 else none)))) else (if id < 186 then (if id < 184 then (if id < 183 then (if id = 182 then some localCycle00182 else none) else (if id = 183 then some localCycle00183 else none)) else (if id < 185 then (if id = 184 then some localCycle00184 else none) else (if id = 185 then some localCycle00185 else none))) else (if id < 188 then (if id < 187 then (if id = 186 then some localCycle00186 else none) else (if id = 187 then some localCycle00187 else none)) else (if id < 189 then (if id = 188 then some localCycle00188 else none) else (if id = 189 then some localCycle00189 else none))))))) else (if id < 222 then (if id < 206 then (if id < 198 then (if id < 194 then (if id < 192 then (if id < 191 then (if id = 190 then some localCycle00190 else none) else (if id = 191 then some localCycle00191 else none)) else (if id < 193 then (if id = 192 then some localCycle00192 else none) else (if id = 193 then some localCycle00193 else none))) else (if id < 196 then (if id < 195 then (if id = 194 then some localCycle00194 else none) else (if id = 195 then some localCycle00195 else none)) else (if id < 197 then (if id = 196 then some localCycle00196 else none) else (if id = 197 then some localCycle00197 else none)))) else (if id < 202 then (if id < 200 then (if id < 199 then (if id = 198 then some localCycle00198 else none) else (if id = 199 then some localCycle00199 else none)) else (if id < 201 then (if id = 200 then some localCycle00200 else none) else (if id = 201 then some localCycle00201 else none))) else (if id < 204 then (if id < 203 then (if id = 202 then some localCycle00202 else none) else (if id = 203 then some localCycle00203 else none)) else (if id < 205 then (if id = 204 then some localCycle00204 else none) else (if id = 205 then some localCycle00205 else none))))) else (if id < 214 then (if id < 210 then (if id < 208 then (if id < 207 then (if id = 206 then some localCycle00206 else none) else (if id = 207 then some localCycle00207 else none)) else (if id < 209 then (if id = 208 then some localCycle00208 else none) else (if id = 209 then some localCycle00209 else none))) else (if id < 212 then (if id < 211 then (if id = 210 then some localCycle00210 else none) else (if id = 211 then some localCycle00211 else none)) else (if id < 213 then (if id = 212 then some localCycle00212 else none) else (if id = 213 then some localCycle00213 else none)))) else (if id < 218 then (if id < 216 then (if id < 215 then (if id = 214 then some localCycle00214 else none) else (if id = 215 then some localCycle00215 else none)) else (if id < 217 then (if id = 216 then some localCycle00216 else none) else (if id = 217 then some localCycle00217 else none))) else (if id < 220 then (if id < 219 then (if id = 218 then some localCycle00218 else none) else (if id = 219 then some localCycle00219 else none)) else (if id < 221 then (if id = 220 then some localCycle00220 else none) else (if id = 221 then some localCycle00221 else none)))))) else (if id < 238 then (if id < 230 then (if id < 226 then (if id < 224 then (if id < 223 then (if id = 222 then some localCycle00222 else none) else (if id = 223 then some localCycle00223 else none)) else (if id < 225 then (if id = 224 then some localCycle00224 else none) else (if id = 225 then some localCycle00225 else none))) else (if id < 228 then (if id < 227 then (if id = 226 then some localCycle00226 else none) else (if id = 227 then some localCycle00227 else none)) else (if id < 229 then (if id = 228 then some localCycle00228 else none) else (if id = 229 then some localCycle00229 else none)))) else (if id < 234 then (if id < 232 then (if id < 231 then (if id = 230 then some localCycle00230 else none) else (if id = 231 then some localCycle00231 else none)) else (if id < 233 then (if id = 232 then some localCycle00232 else none) else (if id = 233 then some localCycle00233 else none))) else (if id < 236 then (if id < 235 then (if id = 234 then some localCycle00234 else none) else (if id = 235 then some localCycle00235 else none)) else (if id < 237 then (if id = 236 then some localCycle00236 else none) else (if id = 237 then some localCycle00237 else none))))) else (if id < 246 then (if id < 242 then (if id < 240 then (if id < 239 then (if id = 238 then some localCycle00238 else none) else (if id = 239 then some localCycle00239 else none)) else (if id < 241 then (if id = 240 then some localCycle00240 else none) else (if id = 241 then some localCycle00241 else none))) else (if id < 244 then (if id < 243 then (if id = 242 then some localCycle00242 else none) else (if id = 243 then some localCycle00243 else none)) else (if id < 245 then (if id = 244 then some localCycle00244 else none) else (if id = 245 then some localCycle00245 else none)))) else (if id < 250 then (if id < 248 then (if id < 247 then (if id = 246 then some localCycle00246 else none) else (if id = 247 then some localCycle00247 else none)) else (if id < 249 then (if id = 248 then some localCycle00248 else none) else (if id = 249 then some localCycle00249 else none))) else (if id < 252 then (if id < 251 then (if id = 250 then some localCycle00250 else none) else (if id = 251 then some localCycle00251 else none)) else (if id < 253 then (if id = 252 then some localCycle00252 else none) else (if id = 253 then some localCycle00253 else none))))))))

def namedLeaf000 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 2, 3, 4, 5, 6], ![0, 1, 3, 4, 5, 6], ![0, 1, 2, 4, 5, 6], ![0, 1, 2, 3, 5, 6], ![0, 1, 2, 3, 4, 6], ![0, 1, 2, 3, 4, 5]], proof := .tail 172 }

theorem namedLeaf000_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 0)) namedLeaf000 = true :=
  by decide +kernel

def namedLeaf001 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 2, 3, 4, 5, 6], ![0, 1, 3, 4, 5, 6], ![0, 1, 2, 4, 5, 6], ![0, 1, 2, 3, 6, 5], ![0, 1, 2, 3, 6, 4], ![0, 1, 2, 3, 5, 4]], proof := .tail 231 }

theorem namedLeaf001_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1)) namedLeaf001 = true :=
  by decide +kernel

def namedLeaf002 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 2, 3, 4, 5, 6], ![0, 1, 3, 4, 5, 6], ![0, 1, 2, 4, 6, 5], ![0, 1, 2, 3, 6, 5], ![0, 1, 2, 6, 3, 4], ![0, 1, 2, 5, 3, 4]], proof := .tail 128 }

theorem namedLeaf002_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2)) namedLeaf002 = true :=
  by decide +kernel

def namedLeaf003 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 2, 3, 4, 5, 6], ![0, 1, 3, 4, 5, 6], ![0, 1, 2, 6, 4, 5], ![0, 1, 2, 6, 3, 5], ![0, 1, 2, 6, 3, 4], ![0, 1, 2, 5, 4, 3]], proof := .tail 123 }

theorem namedLeaf003_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3)) namedLeaf003 = true :=
  by decide +kernel

def namedLeaf004 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 2, 3, 4, 5, 6], ![0, 1, 3, 4, 5, 6], ![0, 1, 2, 5, 4, 6], ![0, 1, 2, 5, 3, 6], ![0, 1, 2, 4, 3, 6], ![0, 1, 2, 3, 4, 5]], proof := .tail 2 }

theorem namedLeaf004_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4)) namedLeaf004 = true :=
  by decide +kernel

def namedLeaf005 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 2, 3, 4, 5, 6], ![0, 1, 3, 4, 5, 6], ![0, 1, 2, 5, 6, 4], ![0, 1, 2, 5, 6, 3], ![0, 1, 2, 4, 3, 6], ![0, 1, 2, 4, 3, 5]], proof := .tail 39 }

theorem namedLeaf005_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5)) namedLeaf005 = true :=
  by decide +kernel

def namedLeaf006 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 2, 3, 4, 5, 6], ![0, 1, 3, 4, 5, 6], ![0, 1, 2, 6, 5, 4], ![0, 1, 2, 5, 6, 3], ![0, 1, 2, 4, 6, 3], ![0, 1, 2, 4, 5, 3]], proof := .tail 76 }

theorem namedLeaf006_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6)) namedLeaf006 = true :=
  by decide +kernel

def namedLeaf007 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 2, 3, 4, 5, 6], ![0, 1, 3, 4, 5, 6], ![0, 1, 2, 6, 5, 4], ![0, 1, 2, 6, 5, 3], ![0, 1, 2, 6, 4, 3], ![0, 1, 2, 5, 4, 3]], proof := .tail 58 }

theorem namedLeaf007_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 7)) namedLeaf007 = true :=
  by decide +kernel

def namedLeaf008 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 2, 3, 4, 5, 6], ![0, 1, 3, 4, 6, 5], ![0, 1, 2, 4, 6, 5], ![0, 1, 2, 3, 6, 5], ![0, 1, 6, 2, 3, 4], ![0, 1, 5, 2, 3, 4]], proof := .tail 71 }

theorem namedLeaf008_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 8)) namedLeaf008 = true :=
  by decide +kernel

def namedLeaf009 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 2, 3, 4, 5, 6], ![0, 1, 3, 4, 6, 5], ![0, 1, 2, 6, 4, 5], ![0, 1, 2, 6, 3, 5], ![0, 1, 6, 2, 3, 4], ![0, 1, 5, 2, 4, 3]], proof := .tail 9 }

theorem namedLeaf009_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 9)) namedLeaf009 = true :=
  by decide +kernel

def namedLeaf010 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 2, 3, 4, 5, 6], ![0, 1, 3, 4, 6, 5], ![0, 1, 2, 6, 5, 4], ![0, 1, 2, 6, 5, 3], ![0, 1, 6, 2, 4, 3], ![0, 1, 5, 2, 4, 3]], proof := .tail 220 }

theorem namedLeaf010_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 10)) namedLeaf010 = true :=
  by decide +kernel

def namedLeaf011 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 2, 3, 4, 5, 6], ![0, 1, 3, 6, 4, 5], ![0, 1, 2, 6, 4, 5], ![0, 1, 6, 2, 3, 5], ![0, 1, 6, 2, 3, 4], ![0, 1, 5, 4, 2, 3]], proof := .tail 61 }

theorem namedLeaf011_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 11)) namedLeaf011 = true :=
  by decide +kernel

def namedLeaf012 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 2, 3, 4, 5, 6], ![0, 1, 3, 6, 4, 5], ![0, 1, 2, 6, 5, 4], ![0, 1, 6, 2, 5, 3], ![0, 1, 6, 2, 4, 3], ![0, 1, 5, 4, 2, 3]], proof := .tail 168 }

theorem namedLeaf012_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12)) namedLeaf012 = true :=
  by decide +kernel

def namedLeaf013 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 2, 3, 4, 5, 6], ![0, 1, 3, 5, 4, 6], ![0, 1, 2, 5, 4, 6], ![0, 1, 5, 2, 3, 6], ![0, 1, 4, 2, 3, 6], ![0, 1, 2, 3, 4, 5]], proof := .tail 199 }

theorem namedLeaf013_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13)) namedLeaf013 = true :=
  by decide +kernel

def namedLeaf014 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 2, 3, 4, 5, 6], ![0, 1, 3, 5, 4, 6], ![0, 1, 2, 5, 6, 4], ![0, 1, 5, 2, 6, 3], ![0, 1, 4, 2, 3, 6], ![0, 1, 2, 4, 3, 5]], proof := .tail 133 }

theorem namedLeaf014_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 14)) namedLeaf014 = true :=
  by decide +kernel

def namedLeaf015 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 2, 3, 4, 5, 6], ![0, 1, 3, 5, 4, 6], ![0, 1, 2, 6, 5, 4], ![0, 1, 5, 2, 6, 3], ![0, 1, 4, 2, 6, 3], ![0, 1, 2, 4, 5, 3]], proof := .tail 70 }

theorem namedLeaf015_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 15)) namedLeaf015 = true :=
  by decide +kernel

def namedLeaf016 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 2, 3, 4, 5, 6], ![0, 1, 3, 5, 6, 4], ![0, 1, 2, 5, 6, 4], ![0, 1, 5, 6, 2, 3], ![0, 1, 4, 2, 3, 6], ![0, 1, 4, 2, 3, 5]], proof := .tail 46 }

theorem namedLeaf016_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16)) namedLeaf016 = true :=
  by decide +kernel

def namedLeaf017 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 2, 3, 4, 5, 6], ![0, 1, 3, 5, 6, 4], ![0, 1, 2, 6, 5, 4], ![0, 1, 5, 6, 2, 3], ![0, 1, 4, 2, 6, 3], ![0, 1, 4, 2, 5, 3]], proof := .tail 52 }

theorem namedLeaf017_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 17)) namedLeaf017 = true :=
  by decide +kernel

def namedLeaf018 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 2, 3, 4, 5, 6], ![0, 1, 3, 6, 5, 4], ![0, 1, 2, 6, 5, 4], ![0, 1, 5, 6, 2, 3], ![0, 1, 4, 6, 2, 3], ![0, 1, 4, 5, 2, 3]], proof := .tail 108 }

theorem namedLeaf018_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18)) namedLeaf018 = true :=
  by decide +kernel

def namedLeaf019 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 2, 3, 4, 5, 6], ![0, 1, 3, 6, 5, 4], ![0, 1, 2, 6, 5, 4], ![0, 1, 6, 5, 2, 3], ![0, 1, 6, 4, 2, 3], ![0, 1, 5, 4, 2, 3]], proof := .tail 55 }

theorem namedLeaf019_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 19)) namedLeaf019 = true :=
  by decide +kernel

def namedLeaf020 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 2, 3, 4, 5, 6], ![0, 1, 6, 3, 4, 5], ![0, 1, 6, 2, 4, 5], ![0, 1, 6, 2, 3, 5], ![0, 1, 6, 2, 3, 4], ![0, 1, 5, 4, 3, 2]], proof := .tail 111 }

theorem namedLeaf020_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20)) namedLeaf020 = true :=
  by decide +kernel

def namedLeaf021 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 2, 3, 4, 5, 6], ![0, 1, 6, 3, 4, 5], ![0, 1, 6, 2, 5, 4], ![0, 1, 6, 2, 5, 3], ![0, 1, 6, 2, 4, 3], ![0, 1, 5, 4, 3, 2]], proof := .tail 182 }

theorem namedLeaf021_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21)) namedLeaf021 = true :=
  by decide +kernel

def namedLeaf022 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 2, 3, 4, 5, 6], ![0, 1, 6, 3, 5, 4], ![0, 1, 6, 2, 5, 4], ![0, 1, 5, 6, 2, 3], ![0, 1, 4, 6, 2, 3], ![0, 1, 4, 5, 3, 2]], proof := .tail 230 }

theorem namedLeaf022_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22)) namedLeaf022 = true :=
  by decide +kernel

def namedLeaf023 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 2, 3, 4, 5, 6], ![0, 1, 6, 3, 5, 4], ![0, 1, 6, 2, 5, 4], ![0, 1, 6, 5, 2, 3], ![0, 1, 6, 4, 2, 3], ![0, 1, 5, 4, 3, 2]], proof := .tail 148 }

theorem namedLeaf023_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23)) namedLeaf023 = true :=
  by decide +kernel

def namedLeaf024 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 2, 3, 4, 5, 6], ![0, 1, 5, 3, 4, 6], ![0, 1, 5, 2, 4, 6], ![0, 1, 5, 2, 3, 6], ![0, 1, 4, 3, 2, 6], ![0, 1, 2, 3, 4, 5]], proof := .tail 62 }

theorem namedLeaf024_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 24)) namedLeaf024 = true :=
  by decide +kernel

def namedLeaf025 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 2, 3, 4, 5, 6], ![0, 1, 5, 3, 4, 6], ![0, 1, 5, 2, 6, 4], ![0, 1, 5, 2, 6, 3], ![0, 1, 4, 3, 2, 6], ![0, 1, 2, 4, 3, 5]], proof := .tail 27 }

theorem namedLeaf025_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 25)) namedLeaf025 = true :=
  by decide +kernel

def namedLeaf026 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 2, 3, 4, 5, 6], ![0, 1, 5, 3, 6, 4], ![0, 1, 5, 2, 6, 4], ![0, 1, 5, 6, 2, 3], ![0, 1, 4, 3, 2, 6], ![0, 1, 4, 2, 3, 5]], proof := .tail 47 }

theorem namedLeaf026_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 26)) namedLeaf026 = true :=
  by decide +kernel

def namedLeaf027 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 2, 3, 4, 5, 6], ![0, 1, 5, 6, 3, 4], ![0, 1, 5, 6, 2, 4], ![0, 1, 5, 6, 2, 3], ![0, 1, 4, 3, 2, 6], ![0, 1, 4, 3, 2, 5]], proof := .tail 130 }

theorem namedLeaf027_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 27)) namedLeaf027 = true :=
  by decide +kernel

def namedLeaf028 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 2, 3, 4, 5, 6], ![0, 1, 6, 5, 3, 4], ![0, 1, 5, 6, 2, 4], ![0, 1, 5, 6, 2, 3], ![0, 1, 4, 3, 6, 2], ![0, 1, 4, 3, 5, 2]], proof := .tail 33 }

theorem namedLeaf028_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 28)) namedLeaf028 = true :=
  by decide +kernel

def namedLeaf029 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 2, 3, 4, 5, 6], ![0, 1, 6, 5, 3, 4], ![0, 1, 6, 5, 2, 4], ![0, 1, 5, 6, 2, 3], ![0, 1, 4, 6, 3, 2], ![0, 1, 4, 5, 3, 2]], proof := .tail 51 }

theorem namedLeaf029_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 29)) namedLeaf029 = true :=
  by decide +kernel

def namedLeaf030 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 2, 3, 4, 5, 6], ![0, 1, 6, 5, 3, 4], ![0, 1, 6, 5, 2, 4], ![0, 1, 6, 5, 2, 3], ![0, 1, 6, 4, 3, 2], ![0, 1, 5, 4, 3, 2]], proof := .tail 14 }

theorem namedLeaf030_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 30)) namedLeaf030 = true :=
  by decide +kernel

def namedLeaf031 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 2, 3, 4, 5, 6], ![0, 1, 4, 3, 5, 6], ![0, 1, 4, 2, 5, 6], ![0, 1, 3, 2, 5, 6], ![0, 1, 2, 3, 4, 6], ![0, 1, 2, 3, 4, 5]], proof := .tail 113 }

theorem namedLeaf031_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 31)) namedLeaf031 = true :=
  by decide +kernel

def namedLeaf032 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 2, 3, 4, 5, 6], ![0, 1, 4, 3, 5, 6], ![0, 1, 4, 2, 5, 6], ![0, 1, 3, 2, 6, 5], ![0, 1, 2, 3, 6, 4], ![0, 1, 2, 3, 5, 4]], proof := .tail 63 }

theorem namedLeaf032_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 32)) namedLeaf032 = true :=
  by decide +kernel

def namedLeaf033 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 2, 3, 4, 5, 6], ![0, 1, 4, 3, 5, 6], ![0, 1, 4, 2, 6, 5], ![0, 1, 3, 2, 6, 5], ![0, 1, 2, 6, 3, 4], ![0, 1, 2, 5, 3, 4]], proof := .tail 245 }

theorem namedLeaf033_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 33)) namedLeaf033 = true :=
  by decide +kernel

def namedLeaf034 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 2, 3, 4, 5, 6], ![0, 1, 4, 3, 6, 5], ![0, 1, 4, 2, 6, 5], ![0, 1, 3, 2, 6, 5], ![0, 1, 6, 2, 3, 4], ![0, 1, 5, 2, 3, 4]], proof := .tail 22 }

theorem namedLeaf034_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 34)) namedLeaf034 = true :=
  by decide +kernel

def namedLeaf035 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 2, 3, 4, 5, 6], ![0, 1, 4, 6, 3, 5], ![0, 1, 4, 6, 2, 5], ![0, 1, 3, 2, 6, 5], ![0, 1, 6, 2, 3, 4], ![0, 1, 5, 3, 2, 4]], proof := .tail 29 }

theorem namedLeaf035_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 35)) namedLeaf035 = true :=
  by decide +kernel

def namedLeaf036 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 2, 3, 4, 5, 6], ![0, 1, 6, 4, 3, 5], ![0, 1, 4, 6, 2, 5], ![0, 1, 3, 6, 2, 5], ![0, 1, 6, 2, 3, 4], ![0, 1, 5, 3, 4, 2]], proof := .tail 49 }

theorem namedLeaf036_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 36)) namedLeaf036 = true :=
  by decide +kernel

def namedLeaf037 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 2, 3, 4, 5, 6], ![0, 1, 6, 4, 3, 5], ![0, 1, 6, 4, 2, 5], ![0, 1, 6, 3, 2, 5], ![0, 1, 6, 2, 3, 4], ![0, 1, 5, 4, 3, 2]], proof := .tail 60 }

theorem namedLeaf037_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 37)) namedLeaf037 = true :=
  by decide +kernel

def namedLeaf038 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 2, 3, 4, 5, 6], ![0, 1, 4, 5, 3, 6], ![0, 1, 4, 5, 2, 6], ![0, 1, 3, 2, 5, 6], ![0, 1, 3, 2, 4, 6], ![0, 1, 2, 3, 4, 5]], proof := .tail 181 }

theorem namedLeaf038_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 38)) namedLeaf038 = true :=
  by decide +kernel

def namedLeaf039 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 2, 3, 4, 5, 6], ![0, 1, 4, 5, 3, 6], ![0, 1, 4, 5, 2, 6], ![0, 1, 3, 2, 6, 5], ![0, 1, 3, 2, 6, 4], ![0, 1, 2, 3, 5, 4]], proof := .tail 41 }

theorem namedLeaf039_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 39)) namedLeaf039 = true :=
  by decide +kernel

def namedLeaf040 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 2, 3, 4, 5, 6], ![0, 1, 5, 4, 3, 6], ![0, 1, 4, 5, 2, 6], ![0, 1, 3, 5, 2, 6], ![0, 1, 3, 4, 2, 6], ![0, 1, 2, 3, 4, 5]], proof := .tail 86 }

theorem namedLeaf040_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 40)) namedLeaf040 = true :=
  by decide +kernel

def namedLeaf041 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 2, 3, 4, 5, 6], ![0, 1, 5, 4, 3, 6], ![0, 1, 5, 4, 2, 6], ![0, 1, 5, 3, 2, 6], ![0, 1, 4, 3, 2, 6], ![0, 1, 2, 3, 4, 5]], proof := .tail 4 }

theorem namedLeaf041_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 41)) namedLeaf041 = true :=
  by decide +kernel

def namedLeaf042 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 2, 3, 4, 5, 6], ![0, 1, 4, 5, 6, 3], ![0, 1, 4, 5, 6, 2], ![0, 1, 3, 2, 5, 6], ![0, 1, 3, 2, 4, 6], ![0, 1, 3, 2, 4, 5]], proof := .tail 175 }

theorem namedLeaf042_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 42)) namedLeaf042 = true :=
  by decide +kernel

def namedLeaf043 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 2, 3, 4, 5, 6], ![0, 1, 4, 5, 6, 3], ![0, 1, 4, 5, 6, 2], ![0, 1, 3, 2, 6, 5], ![0, 1, 3, 2, 6, 4], ![0, 1, 3, 2, 5, 4]], proof := .tail 186 }

theorem namedLeaf043_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 43)) namedLeaf043 = true :=
  by decide +kernel

def namedLeaf044 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 2, 3, 4, 5, 6], ![0, 1, 4, 6, 5, 3], ![0, 1, 4, 5, 6, 2], ![0, 1, 3, 2, 6, 5], ![0, 1, 3, 6, 2, 4], ![0, 1, 3, 5, 2, 4]], proof := .tail 212 }

theorem namedLeaf044_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 44)) namedLeaf044 = true :=
  by decide +kernel

def namedLeaf045 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 2, 3, 4, 5, 6], ![0, 1, 4, 6, 5, 3], ![0, 1, 4, 6, 5, 2], ![0, 1, 3, 2, 6, 5], ![0, 1, 6, 3, 2, 4], ![0, 1, 5, 3, 2, 4]], proof := .tail 8 }

theorem namedLeaf045_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 45)) namedLeaf045 = true :=
  by decide +kernel

def namedLeaf046 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 2, 3, 4, 5, 6], ![0, 1, 6, 4, 5, 3], ![0, 1, 4, 5, 6, 2], ![0, 1, 3, 6, 2, 5], ![0, 1, 3, 6, 2, 4], ![0, 1, 3, 5, 4, 2]], proof := .tail 242 }

theorem namedLeaf046_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 46)) namedLeaf046 = true :=
  by decide +kernel

def namedLeaf047 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 2, 3, 4, 5, 6], ![0, 1, 6, 4, 5, 3], ![0, 1, 4, 6, 5, 2], ![0, 1, 3, 6, 2, 5], ![0, 1, 6, 3, 2, 4], ![0, 1, 5, 3, 4, 2]], proof := .tail 242 }

theorem namedLeaf047_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 47)) namedLeaf047 = true :=
  by decide +kernel

def namedLeaf048 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 2, 3, 4, 5, 6], ![0, 1, 6, 4, 5, 3], ![0, 1, 6, 4, 5, 2], ![0, 1, 6, 3, 2, 5], ![0, 1, 6, 3, 2, 4], ![0, 1, 5, 4, 3, 2]], proof := .tail 107 }

theorem namedLeaf048_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 48)) namedLeaf048 = true :=
  by decide +kernel

def namedLeaf049 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 2, 3, 4, 5, 6], ![0, 1, 5, 4, 6, 3], ![0, 1, 4, 5, 6, 2], ![0, 1, 3, 5, 2, 6], ![0, 1, 3, 4, 2, 6], ![0, 1, 3, 2, 4, 5]], proof := .tail 43 }

theorem namedLeaf049_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 49)) namedLeaf049 = true :=
  by decide +kernel

def namedLeaf050 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 2, 3, 4, 5, 6], ![0, 1, 5, 4, 6, 3], ![0, 1, 5, 4, 6, 2], ![0, 1, 5, 3, 2, 6], ![0, 1, 4, 3, 2, 6], ![0, 1, 3, 2, 4, 5]], proof := .tail 247 }

theorem namedLeaf050_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 50)) namedLeaf050 = true :=
  by decide +kernel

def namedLeaf051 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 2, 3, 4, 5, 6], ![0, 1, 5, 6, 4, 3], ![0, 1, 4, 5, 6, 2], ![0, 1, 3, 5, 6, 2], ![0, 1, 3, 4, 2, 6], ![0, 1, 3, 4, 2, 5]], proof := .tail 202 }

theorem namedLeaf051_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 51)) namedLeaf051 = true :=
  by decide +kernel

def namedLeaf052 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 2, 3, 4, 5, 6], ![0, 1, 5, 6, 4, 3], ![0, 1, 5, 4, 6, 2], ![0, 1, 5, 3, 6, 2], ![0, 1, 4, 3, 2, 6], ![0, 1, 3, 4, 2, 5]], proof := .tail 13 }

theorem namedLeaf052_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 52)) namedLeaf052 = true :=
  by decide +kernel

def namedLeaf053 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 2, 3, 4, 5, 6], ![0, 1, 5, 6, 4, 3], ![0, 1, 5, 6, 4, 2], ![0, 1, 5, 6, 3, 2], ![0, 1, 4, 3, 2, 6], ![0, 1, 4, 3, 2, 5]], proof := .tail 208 }

theorem namedLeaf053_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 53)) namedLeaf053 = true :=
  by decide +kernel

def namedLeaf054 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 2, 3, 4, 5, 6], ![0, 1, 6, 5, 4, 3], ![0, 1, 4, 5, 6, 2], ![0, 1, 3, 5, 6, 2], ![0, 1, 3, 4, 6, 2], ![0, 1, 3, 4, 5, 2]], proof := .tail 138 }

theorem namedLeaf054_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 54)) namedLeaf054 = true :=
  by decide +kernel

def namedLeaf055 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 2, 3, 4, 5, 6], ![0, 1, 6, 5, 4, 3], ![0, 1, 4, 5, 6, 2], ![0, 1, 3, 6, 5, 2], ![0, 1, 3, 6, 4, 2], ![0, 1, 3, 5, 4, 2]], proof := .tail 42 }

theorem namedLeaf055_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 55)) namedLeaf055 = true :=
  by decide +kernel

def namedLeaf056 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 2, 3, 4, 5, 6], ![0, 1, 6, 5, 4, 3], ![0, 1, 4, 6, 5, 2], ![0, 1, 3, 6, 5, 2], ![0, 1, 6, 3, 4, 2], ![0, 1, 5, 3, 4, 2]], proof := .tail 224 }

theorem namedLeaf056_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 56)) namedLeaf056 = true :=
  by decide +kernel

def namedLeaf057 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 2, 3, 4, 5, 6], ![0, 1, 6, 5, 4, 3], ![0, 1, 6, 4, 5, 2], ![0, 1, 6, 3, 5, 2], ![0, 1, 6, 3, 4, 2], ![0, 1, 5, 4, 3, 2]], proof := .tail 57 }

theorem namedLeaf057_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 57)) namedLeaf057 = true :=
  by decide +kernel

def namedLeaf058 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 2, 3, 4, 5, 6], ![0, 1, 6, 5, 4, 3], ![0, 1, 5, 4, 6, 2], ![0, 1, 5, 3, 6, 2], ![0, 1, 4, 3, 6, 2], ![0, 1, 3, 4, 5, 2]], proof := .tail 143 }

theorem namedLeaf058_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 58)) namedLeaf058 = true :=
  by decide +kernel

def namedLeaf059 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 2, 3, 4, 5, 6], ![0, 1, 6, 5, 4, 3], ![0, 1, 5, 6, 4, 2], ![0, 1, 5, 6, 3, 2], ![0, 1, 4, 3, 6, 2], ![0, 1, 4, 3, 5, 2]], proof := .tail 7 }

theorem namedLeaf059_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 59)) namedLeaf059 = true :=
  by decide +kernel

def namedLeaf060 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 2, 3, 4, 5, 6], ![0, 1, 6, 5, 4, 3], ![0, 1, 6, 5, 4, 2], ![0, 1, 5, 6, 3, 2], ![0, 1, 4, 6, 3, 2], ![0, 1, 4, 5, 3, 2]], proof := .tail 94 }

theorem namedLeaf060_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 60)) namedLeaf060 = true :=
  by decide +kernel

def namedLeaf061 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 2, 3, 4, 5, 6], ![0, 1, 6, 5, 4, 3], ![0, 1, 6, 5, 4, 2], ![0, 1, 6, 5, 3, 2], ![0, 1, 6, 4, 3, 2], ![0, 1, 5, 4, 3, 2]], proof := .tail 190 }

theorem namedLeaf061_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 61)) namedLeaf061 = true :=
  by decide +kernel

def namedLeaf062 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 2, 3, 4, 6, 5], ![0, 1, 3, 4, 6, 5], ![0, 1, 2, 4, 6, 5], ![0, 1, 2, 3, 6, 5], ![0, 6, 1, 2, 3, 4], ![0, 5, 1, 2, 3, 4]], proof := .tail 71 }

theorem namedLeaf062_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 62)) namedLeaf062 = true :=
  by decide +kernel

def namedLeaf063 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 2, 3, 4, 6, 5], ![0, 1, 3, 4, 6, 5], ![0, 1, 2, 6, 4, 5], ![0, 1, 2, 6, 3, 5], ![0, 6, 1, 2, 3, 4], ![0, 5, 1, 2, 4, 3]], proof := .tail 218 }

theorem namedLeaf063_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 63)) namedLeaf063 = true :=
  by decide +kernel

def namedLeaf064 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 2, 3, 4, 6, 5], ![0, 1, 3, 4, 6, 5], ![0, 1, 2, 6, 5, 4], ![0, 1, 2, 6, 5, 3], ![0, 6, 1, 2, 4, 3], ![0, 5, 1, 2, 4, 3]], proof := .tail 220 }

theorem namedLeaf064_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 64)) namedLeaf064 = true :=
  by decide +kernel

def namedLeaf065 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 2, 3, 4, 6, 5], ![0, 1, 4, 3, 6, 5], ![0, 1, 4, 2, 6, 5], ![0, 1, 3, 2, 6, 5], ![0, 6, 1, 2, 3, 4], ![0, 5, 1, 2, 3, 4]], proof := .tail 22 }

theorem namedLeaf065_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 65)) namedLeaf065 = true :=
  by decide +kernel

def namedLeaf066 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 2, 3, 4, 6, 5], ![0, 1, 3, 6, 4, 5], ![0, 1, 2, 6, 4, 5], ![0, 1, 6, 2, 3, 5], ![0, 6, 1, 2, 3, 4], ![0, 5, 1, 4, 2, 3]], proof := .tail 48 }

theorem namedLeaf066_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 66)) namedLeaf066 = true :=
  by decide +kernel

def namedLeaf067 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 2, 3, 4, 6, 5], ![0, 1, 3, 6, 4, 5], ![0, 1, 2, 6, 5, 4], ![0, 1, 6, 2, 5, 3], ![0, 6, 1, 2, 4, 3], ![0, 5, 1, 4, 2, 3]], proof := .tail 144 }

theorem namedLeaf067_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 67)) namedLeaf067 = true :=
  by decide +kernel

def namedLeaf068 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 2, 3, 4, 6, 5], ![0, 1, 3, 6, 5, 4], ![0, 1, 2, 6, 5, 4], ![0, 1, 6, 5, 2, 3], ![0, 6, 1, 4, 2, 3], ![0, 5, 1, 4, 2, 3]], proof := .low (![77, 184, 118, 45, 37, 125, 158, 36, 19, 236, 79, 89, 162, 17, 117, 249, 176, 217, 165, 163, 126, 69, 120, 178, 251, 223, 25, 110]) }

theorem namedLeaf068_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 68)) namedLeaf068 = true :=
  by decide +kernel

def namedLeaf069 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 2, 3, 4, 6, 5], ![0, 1, 4, 6, 3, 5], ![0, 1, 4, 6, 2, 5], ![0, 1, 3, 2, 6, 5], ![0, 6, 1, 2, 3, 4], ![0, 5, 1, 3, 2, 4]], proof := .tail 29 }

theorem namedLeaf069_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 69)) namedLeaf069 = true :=
  by decide +kernel

def namedLeaf070 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 2, 3, 4, 6, 5], ![0, 1, 6, 3, 4, 5], ![0, 1, 6, 2, 4, 5], ![0, 1, 6, 2, 3, 5], ![0, 6, 1, 2, 3, 4], ![0, 5, 1, 4, 3, 2]], proof := .tail 16 }

theorem namedLeaf070_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 70)) namedLeaf070 = true :=
  by decide +kernel

def namedLeaf071 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 2, 3, 4, 6, 5], ![0, 1, 6, 3, 4, 5], ![0, 1, 6, 2, 5, 4], ![0, 1, 6, 2, 5, 3], ![0, 6, 1, 2, 4, 3], ![0, 5, 1, 4, 3, 2]], proof := .tail 182 }

theorem namedLeaf071_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 71)) namedLeaf071 = true :=
  by decide +kernel

def namedLeaf072 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 2, 3, 4, 6, 5], ![0, 1, 6, 4, 3, 5], ![0, 1, 4, 6, 2, 5], ![0, 1, 3, 6, 2, 5], ![0, 6, 1, 2, 3, 4], ![0, 5, 1, 3, 4, 2]], proof := .tail 49 }

theorem namedLeaf072_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 72)) namedLeaf072 = true :=
  by decide +kernel

def namedLeaf073 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 2, 3, 4, 6, 5], ![0, 1, 6, 4, 3, 5], ![0, 1, 6, 4, 2, 5], ![0, 1, 6, 3, 2, 5], ![0, 6, 1, 2, 3, 4], ![0, 5, 1, 4, 3, 2]], proof := .tail 88 }

theorem namedLeaf073_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 73)) namedLeaf073 = true :=
  by decide +kernel

def namedLeaf074 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 2, 3, 4, 6, 5], ![0, 1, 6, 3, 5, 4], ![0, 1, 6, 2, 5, 4], ![0, 1, 6, 5, 2, 3], ![0, 6, 1, 4, 2, 3], ![0, 5, 1, 4, 3, 2]], proof := .tail 102 }

theorem namedLeaf074_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 74)) namedLeaf074 = true :=
  by decide +kernel

def namedLeaf075 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 2, 3, 4, 6, 5], ![0, 1, 4, 6, 5, 3], ![0, 1, 4, 6, 5, 2], ![0, 1, 3, 2, 6, 5], ![0, 6, 1, 3, 2, 4], ![0, 5, 1, 3, 2, 4]], proof := .low (![188, 35, 195, 160, 72, 125, 158, 180, 141, 114, 1, 146, 162, 38, 225, 3, 176, 214, 142, 216, 226, 31, 211, 134, 135, 32, 105, 110]) }

theorem namedLeaf075_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 75)) namedLeaf075 = true :=
  by decide +kernel

def namedLeaf076 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 2, 3, 4, 6, 5], ![0, 1, 6, 4, 5, 3], ![0, 1, 4, 6, 5, 2], ![0, 1, 3, 6, 2, 5], ![0, 6, 1, 3, 2, 4], ![0, 5, 1, 3, 4, 2]], proof := .tail 242 }

theorem namedLeaf076_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 76)) namedLeaf076 = true :=
  by decide +kernel

def namedLeaf077 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 2, 3, 4, 6, 5], ![0, 1, 6, 4, 5, 3], ![0, 1, 6, 4, 5, 2], ![0, 1, 6, 3, 2, 5], ![0, 6, 1, 3, 2, 4], ![0, 5, 1, 4, 3, 2]], proof := .tail 157 }

theorem namedLeaf077_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 77)) namedLeaf077 = true :=
  by decide +kernel

def namedLeaf078 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 2, 3, 4, 6, 5], ![0, 1, 6, 5, 3, 4], ![0, 1, 6, 5, 2, 4], ![0, 1, 6, 5, 2, 3], ![0, 6, 1, 4, 3, 2], ![0, 5, 1, 4, 3, 2]], proof := .tail 115 }

theorem namedLeaf078_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 78)) namedLeaf078 = true :=
  by decide +kernel

def namedLeaf079 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 2, 3, 4, 6, 5], ![0, 1, 6, 5, 4, 3], ![0, 1, 4, 6, 5, 2], ![0, 1, 3, 6, 5, 2], ![0, 6, 1, 3, 4, 2], ![0, 5, 1, 3, 4, 2]], proof := .tail 224 }

theorem namedLeaf079_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 79)) namedLeaf079 = true :=
  by decide +kernel

def namedLeaf080 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 2, 3, 4, 6, 5], ![0, 1, 6, 5, 4, 3], ![0, 1, 6, 4, 5, 2], ![0, 1, 6, 3, 5, 2], ![0, 6, 1, 3, 4, 2], ![0, 5, 1, 4, 3, 2]], proof := .tail 140 }

theorem namedLeaf080_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 80)) namedLeaf080 = true :=
  by decide +kernel

def namedLeaf081 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 2, 3, 4, 6, 5], ![0, 1, 6, 5, 4, 3], ![0, 1, 6, 5, 4, 2], ![0, 1, 6, 5, 3, 2], ![0, 6, 1, 4, 3, 2], ![0, 5, 1, 4, 3, 2]], proof := .tail 192 }

theorem namedLeaf081_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 81)) namedLeaf081 = true :=
  by decide +kernel

def namedLeaf082 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 2, 3, 6, 4, 5], ![0, 1, 3, 6, 4, 5], ![0, 1, 2, 6, 4, 5], ![0, 6, 1, 2, 3, 5], ![0, 6, 1, 2, 3, 4], ![0, 5, 4, 1, 2, 3]], proof := .tail 48 }

theorem namedLeaf082_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 82)) namedLeaf082 = true :=
  by decide +kernel

def namedLeaf083 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 2, 3, 6, 4, 5], ![0, 1, 3, 6, 4, 5], ![0, 1, 2, 6, 5, 4], ![0, 6, 1, 2, 5, 3], ![0, 6, 1, 2, 4, 3], ![0, 5, 4, 1, 2, 3]], proof := .tail 73 }

theorem namedLeaf083_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 83)) namedLeaf083 = true :=
  by decide +kernel

def namedLeaf084 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 2, 3, 6, 4, 5], ![0, 1, 3, 6, 5, 4], ![0, 1, 2, 6, 5, 4], ![0, 6, 1, 5, 2, 3], ![0, 6, 1, 4, 2, 3], ![0, 5, 4, 1, 2, 3]], proof := .tail 201 }

theorem namedLeaf084_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 84)) namedLeaf084 = true :=
  by decide +kernel

def namedLeaf085 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 2, 3, 6, 4, 5], ![0, 1, 6, 3, 4, 5], ![0, 1, 6, 2, 4, 5], ![0, 6, 1, 2, 3, 5], ![0, 6, 1, 2, 3, 4], ![0, 5, 4, 1, 3, 2]], proof := .tail 87 }

theorem namedLeaf085_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 85)) namedLeaf085 = true :=
  by decide +kernel

def namedLeaf086 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 2, 3, 6, 4, 5], ![0, 1, 6, 3, 4, 5], ![0, 1, 6, 2, 5, 4], ![0, 6, 1, 2, 5, 3], ![0, 6, 1, 2, 4, 3], ![0, 5, 4, 1, 3, 2]], proof := .tail 155 }

theorem namedLeaf086_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 86)) namedLeaf086 = true :=
  by decide +kernel

def namedLeaf087 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 2, 3, 6, 4, 5], ![0, 1, 6, 3, 5, 4], ![0, 1, 6, 2, 5, 4], ![0, 6, 1, 5, 2, 3], ![0, 6, 1, 4, 2, 3], ![0, 5, 4, 1, 3, 2]], proof := .tail 95 }

theorem namedLeaf087_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 87)) namedLeaf087 = true :=
  by decide +kernel

def namedLeaf088 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 2, 3, 6, 4, 5], ![0, 1, 6, 5, 3, 4], ![0, 1, 6, 5, 2, 4], ![0, 6, 1, 5, 2, 3], ![0, 6, 1, 4, 3, 2], ![0, 5, 4, 1, 3, 2]], proof := .tail 150 }

theorem namedLeaf088_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 88)) namedLeaf088 = true :=
  by decide +kernel

def namedLeaf089 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 2, 3, 6, 4, 5], ![0, 1, 6, 4, 3, 5], ![0, 1, 6, 4, 2, 5], ![0, 6, 1, 3, 2, 5], ![0, 6, 1, 2, 3, 4], ![0, 5, 4, 1, 3, 2]], proof := .tail 244 }

theorem namedLeaf089_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 89)) namedLeaf089 = true :=
  by decide +kernel

def namedLeaf090 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 2, 3, 6, 4, 5], ![0, 1, 6, 4, 5, 3], ![0, 1, 6, 4, 5, 2], ![0, 6, 1, 3, 2, 5], ![0, 6, 1, 3, 2, 4], ![0, 5, 4, 1, 3, 2]], proof := .tail 242 }

theorem namedLeaf090_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 90)) namedLeaf090 = true :=
  by decide +kernel

def namedLeaf091 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 2, 3, 6, 4, 5], ![0, 1, 6, 5, 4, 3], ![0, 1, 6, 4, 5, 2], ![0, 6, 1, 3, 5, 2], ![0, 6, 1, 3, 4, 2], ![0, 5, 4, 1, 3, 2]], proof := .tail 67 }

theorem namedLeaf091_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 91)) namedLeaf091 = true :=
  by decide +kernel

def namedLeaf092 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 2, 3, 6, 4, 5], ![0, 1, 6, 5, 4, 3], ![0, 1, 6, 5, 4, 2], ![0, 6, 1, 5, 3, 2], ![0, 6, 1, 4, 3, 2], ![0, 5, 4, 1, 3, 2]], proof := .tail 198 }

theorem namedLeaf092_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 92)) namedLeaf092 = true :=
  by decide +kernel

def namedLeaf093 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 2, 3, 5, 4, 6], ![0, 1, 3, 5, 4, 6], ![0, 1, 2, 5, 4, 6], ![0, 5, 1, 2, 3, 6], ![0, 4, 1, 2, 3, 6], ![0, 1, 2, 3, 4, 5]], proof := .tail 64 }

theorem namedLeaf093_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 93)) namedLeaf093 = true :=
  by decide +kernel

def namedLeaf094 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 2, 3, 5, 4, 6], ![0, 1, 3, 5, 4, 6], ![0, 1, 2, 5, 6, 4], ![0, 5, 1, 2, 6, 3], ![0, 4, 1, 2, 3, 6], ![0, 1, 2, 4, 3, 5]], proof := .tail 152 }

theorem namedLeaf094_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 94)) namedLeaf094 = true :=
  by decide +kernel

def namedLeaf095 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 2, 3, 5, 4, 6], ![0, 1, 3, 5, 4, 6], ![0, 1, 2, 6, 5, 4], ![0, 5, 1, 2, 6, 3], ![0, 4, 1, 2, 6, 3], ![0, 1, 2, 4, 5, 3]], proof := .tail 84 }

theorem namedLeaf095_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 95)) namedLeaf095 = true :=
  by decide +kernel

def namedLeaf096 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 2, 3, 5, 4, 6], ![0, 1, 3, 5, 6, 4], ![0, 1, 2, 5, 6, 4], ![0, 5, 1, 6, 2, 3], ![0, 4, 1, 2, 3, 6], ![0, 1, 4, 2, 3, 5]], proof := .tail 30 }

theorem namedLeaf096_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 96)) namedLeaf096 = true :=
  by decide +kernel

def namedLeaf097 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 2, 3, 5, 4, 6], ![0, 1, 3, 5, 6, 4], ![0, 1, 2, 6, 5, 4], ![0, 5, 1, 6, 2, 3], ![0, 4, 1, 2, 6, 3], ![0, 1, 4, 2, 5, 3]], proof := .tail 219 }

theorem namedLeaf097_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 97)) namedLeaf097 = true :=
  by decide +kernel

def namedLeaf098 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 2, 3, 5, 4, 6], ![0, 1, 3, 6, 5, 4], ![0, 1, 2, 6, 5, 4], ![0, 5, 1, 6, 2, 3], ![0, 4, 1, 6, 2, 3], ![0, 1, 4, 5, 2, 3]], proof := .tail 213 }

theorem namedLeaf098_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 98)) namedLeaf098 = true :=
  by decide +kernel

def namedLeaf099 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 2, 3, 5, 4, 6], ![0, 1, 6, 3, 5, 4], ![0, 1, 6, 2, 5, 4], ![0, 5, 1, 6, 2, 3], ![0, 4, 1, 6, 2, 3], ![0, 1, 4, 5, 3, 2]], proof := .tail 151 }

theorem namedLeaf099_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 99)) namedLeaf099 = true :=
  by decide +kernel

def namedLeaf100 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 2, 3, 5, 4, 6], ![0, 1, 5, 3, 4, 6], ![0, 1, 5, 2, 4, 6], ![0, 5, 1, 2, 3, 6], ![0, 4, 1, 3, 2, 6], ![0, 1, 2, 3, 4, 5]], proof := .tail 62 }

theorem namedLeaf100_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 100)) namedLeaf100 = true :=
  by decide +kernel

def namedLeaf101 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 2, 3, 5, 4, 6], ![0, 1, 5, 3, 4, 6], ![0, 1, 5, 2, 6, 4], ![0, 5, 1, 2, 6, 3], ![0, 4, 1, 3, 2, 6], ![0, 1, 2, 4, 3, 5]], proof := .tail 66 }

theorem namedLeaf101_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 101)) namedLeaf101 = true :=
  by decide +kernel

def namedLeaf102 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 2, 3, 5, 4, 6], ![0, 1, 5, 3, 6, 4], ![0, 1, 5, 2, 6, 4], ![0, 5, 1, 6, 2, 3], ![0, 4, 1, 3, 2, 6], ![0, 1, 4, 2, 3, 5]], proof := .tail 197 }

theorem namedLeaf102_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 102)) namedLeaf102 = true :=
  by decide +kernel

def namedLeaf103 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 2, 3, 5, 4, 6], ![0, 1, 5, 6, 3, 4], ![0, 1, 5, 6, 2, 4], ![0, 5, 1, 6, 2, 3], ![0, 4, 1, 3, 2, 6], ![0, 1, 4, 3, 2, 5]], proof := .tail 24 }

theorem namedLeaf103_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 103)) namedLeaf103 = true :=
  by decide +kernel

def namedLeaf104 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 2, 3, 5, 4, 6], ![0, 1, 6, 5, 3, 4], ![0, 1, 5, 6, 2, 4], ![0, 5, 1, 6, 2, 3], ![0, 4, 1, 3, 6, 2], ![0, 1, 4, 3, 5, 2]], proof := .tail 33 }

theorem namedLeaf104_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 104)) namedLeaf104 = true :=
  by decide +kernel

def namedLeaf105 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 2, 3, 5, 4, 6], ![0, 1, 6, 5, 3, 4], ![0, 1, 6, 5, 2, 4], ![0, 5, 1, 6, 2, 3], ![0, 4, 1, 6, 3, 2], ![0, 1, 4, 5, 3, 2]], proof := .tail 51 }

theorem namedLeaf105_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 105)) namedLeaf105 = true :=
  by decide +kernel

def namedLeaf106 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 2, 3, 5, 4, 6], ![0, 1, 5, 4, 3, 6], ![0, 1, 5, 4, 2, 6], ![0, 5, 1, 3, 2, 6], ![0, 4, 1, 3, 2, 6], ![0, 1, 2, 3, 4, 5]], proof := .tail 75 }

theorem namedLeaf106_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 106)) namedLeaf106 = true :=
  by decide +kernel

def namedLeaf107 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 2, 3, 5, 4, 6], ![0, 1, 5, 4, 6, 3], ![0, 1, 5, 4, 6, 2], ![0, 5, 1, 3, 2, 6], ![0, 4, 1, 3, 2, 6], ![0, 1, 3, 2, 4, 5]], proof := .low (![203, 20, 137, 10, 80, 74, 170, 164, 179, 90, 136, 0, 101, 189, 104, 206, 119, 54, 11, 253, 227, 194, 106, 209, 169, 28, 206, 78]) }

theorem namedLeaf107_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 107)) namedLeaf107 = true :=
  by decide +kernel

def namedLeaf108 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 2, 3, 5, 4, 6], ![0, 1, 5, 6, 4, 3], ![0, 1, 5, 4, 6, 2], ![0, 5, 1, 3, 6, 2], ![0, 4, 1, 3, 2, 6], ![0, 1, 3, 4, 2, 5]], proof := .tail 65 }

theorem namedLeaf108_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 108)) namedLeaf108 = true :=
  by decide +kernel

def namedLeaf109 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 2, 3, 5, 4, 6], ![0, 1, 5, 6, 4, 3], ![0, 1, 5, 6, 4, 2], ![0, 5, 1, 6, 3, 2], ![0, 4, 1, 3, 2, 6], ![0, 1, 4, 3, 2, 5]], proof := .tail 21 }

theorem namedLeaf109_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 109)) namedLeaf109 = true :=
  by decide +kernel

def namedLeaf110 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 2, 3, 5, 4, 6], ![0, 1, 6, 5, 4, 3], ![0, 1, 5, 4, 6, 2], ![0, 5, 1, 3, 6, 2], ![0, 4, 1, 3, 6, 2], ![0, 1, 3, 4, 5, 2]], proof := .tail 7 }

theorem namedLeaf110_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 110)) namedLeaf110 = true :=
  by decide +kernel

def namedLeaf111 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 2, 3, 5, 4, 6], ![0, 1, 6, 5, 4, 3], ![0, 1, 5, 6, 4, 2], ![0, 5, 1, 6, 3, 2], ![0, 4, 1, 3, 6, 2], ![0, 1, 4, 3, 5, 2]], proof := .tail 21 }

theorem namedLeaf111_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 111)) namedLeaf111 = true :=
  by decide +kernel

def namedLeaf112 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 2, 3, 5, 4, 6], ![0, 1, 6, 5, 4, 3], ![0, 1, 6, 5, 4, 2], ![0, 5, 1, 6, 3, 2], ![0, 4, 1, 6, 3, 2], ![0, 1, 4, 5, 3, 2]], proof := .tail 207 }

theorem namedLeaf112_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 112)) namedLeaf112 = true :=
  by decide +kernel

def namedLeaf113 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 2, 3, 5, 6, 4], ![0, 1, 3, 5, 6, 4], ![0, 1, 2, 5, 6, 4], ![0, 5, 6, 1, 2, 3], ![0, 4, 1, 2, 3, 6], ![0, 4, 1, 2, 3, 5]], proof := .tail 46 }

theorem namedLeaf113_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 113)) namedLeaf113 = true :=
  by decide +kernel

def namedLeaf114 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 2, 3, 5, 6, 4], ![0, 1, 3, 5, 6, 4], ![0, 1, 2, 6, 5, 4], ![0, 5, 6, 1, 2, 3], ![0, 4, 1, 2, 6, 3], ![0, 4, 1, 2, 5, 3]], proof := .tail 98 }

theorem namedLeaf114_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 114)) namedLeaf114 = true :=
  by decide +kernel

def namedLeaf115 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 2, 3, 5, 6, 4], ![0, 1, 3, 6, 5, 4], ![0, 1, 2, 6, 5, 4], ![0, 5, 6, 1, 2, 3], ![0, 4, 1, 6, 2, 3], ![0, 4, 1, 5, 2, 3]], proof := .low (![103, 184, 118, 93, 44, 173, 222, 36, 237, 171, 240, 229, 204, 17, 241, 82, 232, 217, 154, 243, 149, 250, 100, 183, 183, 34, 248, 193]) }

theorem namedLeaf115_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 115)) namedLeaf115 = true :=
  by decide +kernel

def namedLeaf116 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 2, 3, 5, 6, 4], ![0, 1, 6, 3, 5, 4], ![0, 1, 6, 2, 5, 4], ![0, 5, 6, 1, 2, 3], ![0, 4, 1, 6, 2, 3], ![0, 4, 1, 5, 3, 2]], proof := .tail 81 }

theorem namedLeaf116_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 116)) namedLeaf116 = true :=
  by decide +kernel

def namedLeaf117 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 2, 3, 5, 6, 4], ![0, 1, 5, 3, 6, 4], ![0, 1, 5, 2, 6, 4], ![0, 5, 6, 1, 2, 3], ![0, 4, 1, 3, 2, 6], ![0, 4, 1, 2, 3, 5]], proof := .tail 197 }

theorem namedLeaf117_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 117)) namedLeaf117 = true :=
  by decide +kernel

def namedLeaf118 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 2, 3, 5, 6, 4], ![0, 1, 5, 6, 3, 4], ![0, 1, 5, 6, 2, 4], ![0, 5, 6, 1, 2, 3], ![0, 4, 1, 3, 2, 6], ![0, 4, 1, 3, 2, 5]], proof := .tail 166 }

theorem namedLeaf118_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 118)) namedLeaf118 = true :=
  by decide +kernel

def namedLeaf119 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 2, 3, 5, 6, 4], ![0, 1, 6, 5, 3, 4], ![0, 1, 5, 6, 2, 4], ![0, 5, 6, 1, 2, 3], ![0, 4, 1, 3, 6, 2], ![0, 4, 1, 3, 5, 2]], proof := .tail 33 }

theorem namedLeaf119_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 119)) namedLeaf119 = true :=
  by decide +kernel

def namedLeaf120 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 2, 3, 5, 6, 4], ![0, 1, 6, 5, 3, 4], ![0, 1, 6, 5, 2, 4], ![0, 5, 6, 1, 2, 3], ![0, 4, 1, 6, 3, 2], ![0, 4, 1, 5, 3, 2]], proof := .tail 51 }

theorem namedLeaf120_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 120)) namedLeaf120 = true :=
  by decide +kernel

def namedLeaf121 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 2, 3, 6, 5, 4], ![0, 1, 3, 6, 5, 4], ![0, 1, 2, 6, 5, 4], ![0, 5, 6, 1, 2, 3], ![0, 4, 6, 1, 2, 3], ![0, 4, 5, 1, 2, 3]], proof := .low (![59, 184, 118, 50, 177, 5, 200, 36, 238, 97, 228, 85, 83, 17, 139, 18, 85, 217, 6, 122, 85, 159, 215, 85, 23, 85, 99, 85]) }

theorem namedLeaf121_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 121)) namedLeaf121 = true :=
  by decide +kernel

def namedLeaf122 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 2, 3, 6, 5, 4], ![0, 1, 6, 3, 5, 4], ![0, 1, 6, 2, 5, 4], ![0, 5, 6, 1, 2, 3], ![0, 4, 6, 1, 2, 3], ![0, 4, 5, 1, 3, 2]], proof := .tail 196 }

theorem namedLeaf122_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 122)) namedLeaf122 = true :=
  by decide +kernel

def namedLeaf123 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 2, 3, 6, 5, 4], ![0, 1, 6, 5, 3, 4], ![0, 1, 6, 5, 2, 4], ![0, 5, 6, 1, 2, 3], ![0, 4, 6, 1, 3, 2], ![0, 4, 5, 1, 3, 2]], proof := .tail 51 }

theorem namedLeaf123_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 123)) namedLeaf123 = true :=
  by decide +kernel

def namedLeaf124 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 2, 3, 6, 5, 4], ![0, 1, 3, 6, 5, 4], ![0, 1, 2, 6, 5, 4], ![0, 6, 5, 1, 2, 3], ![0, 6, 4, 1, 2, 3], ![0, 5, 4, 1, 2, 3]], proof := .low (![12, 184, 118, 50, 121, 233, 239, 36, 238, 97, 68, 246, 96, 17, 139, 15, 167, 217, 6, 122, 205, 53, 109, 147, 23, 127, 187, 234]) }

theorem namedLeaf124_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 124)) namedLeaf124 = true :=
  by decide +kernel

def namedLeaf125 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 2, 3, 6, 5, 4], ![0, 1, 6, 3, 5, 4], ![0, 1, 6, 2, 5, 4], ![0, 6, 5, 1, 2, 3], ![0, 6, 4, 1, 2, 3], ![0, 5, 4, 1, 3, 2]], proof := .tail 156 }

theorem namedLeaf125_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 125)) namedLeaf125 = true :=
  by decide +kernel

def namedLeaf126 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 2, 3, 6, 5, 4], ![0, 1, 6, 5, 3, 4], ![0, 1, 6, 5, 2, 4], ![0, 6, 5, 1, 2, 3], ![0, 6, 4, 1, 3, 2], ![0, 5, 4, 1, 3, 2]], proof := .tail 115 }

theorem namedLeaf126_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 126)) namedLeaf126 = true :=
  by decide +kernel

def namedLeaf127 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 2, 3, 5, 6, 4], ![0, 1, 5, 6, 4, 3], ![0, 1, 5, 6, 4, 2], ![0, 5, 6, 1, 3, 2], ![0, 4, 1, 3, 2, 6], ![0, 4, 1, 3, 2, 5]], proof := .low (![91, 185, 137, 10, 26, 173, 222, 235, 92, 129, 191, 161, 204, 124, 116, 40, 252, 56, 11, 112, 145, 194, 131, 153, 210, 174, 132, 221]) }

theorem namedLeaf127_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 127)) namedLeaf127 = true :=
  by decide +kernel

def fallback : LeafData := { rows := fun _ _ => 0, proof := .tail 0 }
def lookup (offset : ℕ) : LeafData :=
  if offset < 128 then (if offset < 64 then (if offset < 32 then (if offset < 16 then (if offset < 8 then (if offset < 4 then (if offset < 2 then (if offset < 1 then (namedLeaf000) else (namedLeaf001)) else (if offset < 3 then (namedLeaf002) else (namedLeaf003))) else (if offset < 6 then (if offset < 5 then (namedLeaf004) else (namedLeaf005)) else (if offset < 7 then (namedLeaf006) else (namedLeaf007)))) else (if offset < 12 then (if offset < 10 then (if offset < 9 then (namedLeaf008) else (namedLeaf009)) else (if offset < 11 then (namedLeaf010) else (namedLeaf011))) else (if offset < 14 then (if offset < 13 then (namedLeaf012) else (namedLeaf013)) else (if offset < 15 then (namedLeaf014) else (namedLeaf015))))) else (if offset < 24 then (if offset < 20 then (if offset < 18 then (if offset < 17 then (namedLeaf016) else (namedLeaf017)) else (if offset < 19 then (namedLeaf018) else (namedLeaf019))) else (if offset < 22 then (if offset < 21 then (namedLeaf020) else (namedLeaf021)) else (if offset < 23 then (namedLeaf022) else (namedLeaf023)))) else (if offset < 28 then (if offset < 26 then (if offset < 25 then (namedLeaf024) else (namedLeaf025)) else (if offset < 27 then (namedLeaf026) else (namedLeaf027))) else (if offset < 30 then (if offset < 29 then (namedLeaf028) else (namedLeaf029)) else (if offset < 31 then (namedLeaf030) else (namedLeaf031)))))) else (if offset < 48 then (if offset < 40 then (if offset < 36 then (if offset < 34 then (if offset < 33 then (namedLeaf032) else (namedLeaf033)) else (if offset < 35 then (namedLeaf034) else (namedLeaf035))) else (if offset < 38 then (if offset < 37 then (namedLeaf036) else (namedLeaf037)) else (if offset < 39 then (namedLeaf038) else (namedLeaf039)))) else (if offset < 44 then (if offset < 42 then (if offset < 41 then (namedLeaf040) else (namedLeaf041)) else (if offset < 43 then (namedLeaf042) else (namedLeaf043))) else (if offset < 46 then (if offset < 45 then (namedLeaf044) else (namedLeaf045)) else (if offset < 47 then (namedLeaf046) else (namedLeaf047))))) else (if offset < 56 then (if offset < 52 then (if offset < 50 then (if offset < 49 then (namedLeaf048) else (namedLeaf049)) else (if offset < 51 then (namedLeaf050) else (namedLeaf051))) else (if offset < 54 then (if offset < 53 then (namedLeaf052) else (namedLeaf053)) else (if offset < 55 then (namedLeaf054) else (namedLeaf055)))) else (if offset < 60 then (if offset < 58 then (if offset < 57 then (namedLeaf056) else (namedLeaf057)) else (if offset < 59 then (namedLeaf058) else (namedLeaf059))) else (if offset < 62 then (if offset < 61 then (namedLeaf060) else (namedLeaf061)) else (if offset < 63 then (namedLeaf062) else (namedLeaf063))))))) else (if offset < 96 then (if offset < 80 then (if offset < 72 then (if offset < 68 then (if offset < 66 then (if offset < 65 then (namedLeaf064) else (namedLeaf065)) else (if offset < 67 then (namedLeaf066) else (namedLeaf067))) else (if offset < 70 then (if offset < 69 then (namedLeaf068) else (namedLeaf069)) else (if offset < 71 then (namedLeaf070) else (namedLeaf071)))) else (if offset < 76 then (if offset < 74 then (if offset < 73 then (namedLeaf072) else (namedLeaf073)) else (if offset < 75 then (namedLeaf074) else (namedLeaf075))) else (if offset < 78 then (if offset < 77 then (namedLeaf076) else (namedLeaf077)) else (if offset < 79 then (namedLeaf078) else (namedLeaf079))))) else (if offset < 88 then (if offset < 84 then (if offset < 82 then (if offset < 81 then (namedLeaf080) else (namedLeaf081)) else (if offset < 83 then (namedLeaf082) else (namedLeaf083))) else (if offset < 86 then (if offset < 85 then (namedLeaf084) else (namedLeaf085)) else (if offset < 87 then (namedLeaf086) else (namedLeaf087)))) else (if offset < 92 then (if offset < 90 then (if offset < 89 then (namedLeaf088) else (namedLeaf089)) else (if offset < 91 then (namedLeaf090) else (namedLeaf091))) else (if offset < 94 then (if offset < 93 then (namedLeaf092) else (namedLeaf093)) else (if offset < 95 then (namedLeaf094) else (namedLeaf095)))))) else (if offset < 112 then (if offset < 104 then (if offset < 100 then (if offset < 98 then (if offset < 97 then (namedLeaf096) else (namedLeaf097)) else (if offset < 99 then (namedLeaf098) else (namedLeaf099))) else (if offset < 102 then (if offset < 101 then (namedLeaf100) else (namedLeaf101)) else (if offset < 103 then (namedLeaf102) else (namedLeaf103)))) else (if offset < 108 then (if offset < 106 then (if offset < 105 then (namedLeaf104) else (namedLeaf105)) else (if offset < 107 then (namedLeaf106) else (namedLeaf107))) else (if offset < 110 then (if offset < 109 then (namedLeaf108) else (namedLeaf109)) else (if offset < 111 then (namedLeaf110) else (namedLeaf111))))) else (if offset < 120 then (if offset < 116 then (if offset < 114 then (if offset < 113 then (namedLeaf112) else (namedLeaf113)) else (if offset < 115 then (namedLeaf114) else (namedLeaf115))) else (if offset < 118 then (if offset < 117 then (namedLeaf116) else (namedLeaf117)) else (if offset < 119 then (namedLeaf118) else (namedLeaf119)))) else (if offset < 124 then (if offset < 122 then (if offset < 121 then (namedLeaf120) else (namedLeaf121)) else (if offset < 123 then (namedLeaf122) else (namedLeaf123))) else (if offset < 126 then (if offset < 125 then (namedLeaf124) else (namedLeaf125)) else (if offset < 127 then (namedLeaf126) else (namedLeaf127)))))))) else fallback

theorem point_checked (j : Fin 128) :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 (0 + j.val))) (lookup j.val) = true := by
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

theorem correct (id : Fin 24698) (hlow : 0 ≤ id.val) (hhigh : id.val < 128) :
    leafCheck library (N4R2WordTree.catalog id) (lookup (id.val - 0)) = true := by
  let j : Fin 128 := ⟨id.val - 0, by omega⟩
  have hsum : 0 + j.val = id.val := by dsimp [j]; omega
  have hindex : Fin.ofNat 24698 (0 + j.val) = id := by
    apply Fin.ext
    simp only [Fin.ofNat, hsum, Nat.mod_eq_of_lt id.isLt]
  have hh := point_checked j
  rw [hindex] at hh
  exact hh

#print axioms point_checked
#print axioms correct
end Jsp404.N4R2OuterLeftData.LeafShard000
