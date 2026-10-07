import Jsp000404.N4R2OuterLeftReplay
import Jsp000404.N4R2WordCatalog

set_option autoImplicit false
set_option pp.fullNames true
set_option maxRecDepth 8192
set_option maxHeartbeats 0
set_option Elab.async false

namespace Jsp404.N4R2OuterLeftData.LeafShard186
open N4R2OuterLeftReplay

-- Cycle fingerprint 00de8a554709d3ef1a7206d6a359aab90826baac262e63027941739814e04c47.
def localCycle00000 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 0 3, .distance 3 4, .distance 3 5, .distance 5 6, .distance 4 6, .distance 1 4, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, -1, 0, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false, false, true] }
  origin := ![.corridorUpper 0 3, .triangle 9 0, .triangle 31 2, .triangle 33 0, .triangle 34 2, .triangle 23 0, .triangle 22 0, .corridorLower 4 5, .thetaNext 3]

-- Cycle fingerprint 05648305a7010558b41941684fbde95d55e2fc8410e859368755bc69077d8f7f.
def localCycle00001 : Cycle where
  length := 10
  data := {
    node := ![.theta 3, .distance 0 3, .distance 0 4, .distance 0 5, .distance 5 6, .distance 3 6, .distance 2 3, .distance 3 4, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, 0, 0, -1, 0, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, false, false, false, true] }
  origin := ![.corridorUpper 0 3, .triangle 9 2, .triangle 12 2, .triangle 14 0, .triangle 33 2, .triangle 27 0, .triangle 25 0, .triangle 31 0, .corridorLower 4 5, .thetaNext 3]

-- Cycle fingerprint 060376ecca95d95191bd5ebfa85034d0796a7decef346037269afa1e0f708dc5.
def localCycle00002 : Cycle where
  length := 11
  data := {
    node := ![.distance 2 4, .distance 4 6, .distance 3 4, .distance 1 3, .distance 1 2, .theta 1, .distance 0 1, .distance 0 2, .distance 0 3, .distance 0 4, .distance 4 5, .distance 2 4]
    constant := ![-1, -1, -1, 0, -1, 3, 0, 0, 0, -1, -1]
    coefficient := ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, true, true, false, false] }
  origin := ![.triangle 29 0, .triangle 32 0, .triangle 19 0, .gapLower 1 1, .corridorLower 1 2, .corridorUpper 0 1, .triangle 0 2, .triangle 5 2, .triangle 9 2, .triangle 12 0, .triangle 28 0]

-- Cycle fingerprint 063412903cd71dba7d289272dd23e3211f0a32400ac43b82468262cbc6caaa20.
def localCycle00003 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 3, .distance 3 6, .theta 3, .distance 0 3, .distance 3 4, .distance 2 3, .distance 3 5, .distance 4 5, .distance 1 4, .distance 1 3]
    constant := ![-1, -1, 3, -1, -1, -1, 0, -1, 0]
    coefficient := ![0, 0, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, false, false] }
  origin := ![.triangle 21 0, .corridorLower 3 6, .corridorUpper 0 3, .triangle 9 0, .triangle 25 0, .triangle 26 0, .triangle 31 1, .triangle 22 0, .gapLower 1 3]

-- Cycle fingerprint 08f3f5f23ace6aa9b71dfd3beb753cf6b168dabcd279fac7b6fc3dd518347228.
def localCycle00004 : Cycle where
  length := 13
  data := {
    node := ![.distance 3 4, .distance 2 3, .distance 3 5, .distance 1 3, .distance 1 2, .theta 1, .distance 0 1, .distance 0 2, .distance 0 3, .distance 0 4, .distance 0 5, .distance 5 6, .distance 4 6, .distance 3 4]
    constant := ![-1, -1, -1, 0, -1, 3, 0, 0, 0, 0, -1, 0, -1]
    coefficient := ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, true, true, true, false, true, false] }
  origin := ![.triangle 25 0, .triangle 26 0, .triangle 20 0, .gapLower 1 1, .corridorLower 1 2, .corridorUpper 0 1, .triangle 0 2, .triangle 5 2, .triangle 9 2, .triangle 12 2, .triangle 14 0, .triangle 34 2, .triangle 32 0]

-- Cycle fingerprint 0a5b2cede02d6afcfe95abc1649661ec45052caf6e46d86cfd791b50586784d8.
def localCycle00005 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 3, .distance 1 2, .theta 2, .distance 0 2, .distance 2 3, .distance 2 4, .distance 2 5, .distance 5 6, .distance 3 5, .distance 1 3]
    constant := ![0, 0, 3, -1, 0, 0, -1, -1, -1]
    coefficient := ![0, 0, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, false, false, false] }
  origin := ![.gapLower 1 1, .gapLower 2 0, .corridorUpper 0 2, .triangle 5 0, .triangle 25 2, .triangle 28 2, .triangle 30 0, .triangle 33 0, .triangle 20 0]

-- Cycle fingerprint 0d6425e84089f1a76e5bbe8c5cfd97ec2e43449d1f8ef62c32aba7c3b5593118.
def localCycle00006 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 0 3, .distance 3 4, .distance 2 4, .distance 2 5, .distance 5 6, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, -1, 0, 0, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, true] }
  origin := ![.corridorUpper 0 3, .triangle 9 0, .triangle 25 2, .triangle 28 2, .triangle 30 0, .triangle 34 0, .corridorLower 4 5, .thetaNext 3]

-- Cycle fingerprint 0dddbec493c75b8a544842a36495b4165f4394027ee44227d5adfbff054cdacd.
def localCycle00007 : Cycle where
  length := 13
  data := {
    node := ![.distance 4 5, .distance 3 5, .distance 5 6, .distance 2 5, .distance 2 3, .distance 3 4, .distance 1 3, .distance 1 2, .theta 1, .distance 0 1, .distance 0 2, .distance 0 3, .distance 0 4, .distance 4 5]
    constant := ![0, -1, -1, 0, -1, -1, 0, -1, 3, 0, 0, 0, -1]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0]
    strict := ![true, false, false, false, false, false, false, false, false, true, true, true, false] }
  origin := ![.triangle 31 2, .triangle 33 0, .triangle 30 0, .gapLower 2 3, .triangle 25 0, .triangle 19 0, .gapLower 1 1, .corridorLower 1 2, .corridorUpper 0 1, .triangle 0 2, .triangle 5 2, .triangle 9 2, .triangle 12 0]

-- Cycle fingerprint 147d0c3f27391c13852eb9732cb7dfd5a668563786fb0afbfd20db38d13edde5.
def localCycle00008 : Cycle where
  length := 9
  data := {
    node := ![.distance 3 4, .distance 4 6, .distance 1 4, .distance 4 5, .theta 4, .theta 3, .theta 2, .distance 0 2, .distance 2 3, .distance 3 4]
    constant := ![-1, -1, -1, -1, 0, 0, 3, -1, -1]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 0, 0]
    strict := ![false, false, false, false, true, true, false, false, false] }
  origin := ![.triangle 32 0, .triangle 23 0, .triangle 22 0, .corridorLower 4 5, .thetaNext 3, .thetaNext 2, .corridorUpper 0 2, .triangle 5 0, .triangle 25 0]

-- Cycle fingerprint 147e33c8cf1a86876d8d30c898cdd254b25e9c30a49ecc92f7b564a18e7bea2d.
def localCycle00009 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 0 4, .distance 4 5, .distance 1 4, .distance 4 6, .distance 5 6, .theta 5, .theta 4]
    constant := ![3, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, true] }
  origin := ![.corridorUpper 0 4, .triangle 12 0, .triangle 22 0, .triangle 23 0, .triangle 34 1, .corridorLower 5 6, .thetaNext 4]

-- Cycle fingerprint 15622436c1a65d49ee3da16e7e2dc7e15b00bff2f539c17bac90127698d1ffeb.
def localCycle00010 : Cycle where
  length := 11
  data := {
    node := ![.distance 0 3, .distance 3 4, .distance 2 4, .distance 2 5, .distance 5 6, .distance 4 5, .distance 1 4, .distance 1 3, .theta 1, .distance 0 1, .distance 0 2, .distance 0 3]
    constant := ![-1, 0, 0, -1, -1, -1, 0, -1, 3, 0, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0]
    strict := ![false, true, true, false, false, false, false, false, false, true, true] }
  origin := ![.triangle 9 0, .triangle 25 2, .triangle 28 2, .triangle 30 0, .triangle 34 0, .triangle 22 0, .gapLower 1 2, .corridorLower 1 3, .corridorUpper 0 1, .triangle 0 2, .triangle 5 2]

-- Cycle fingerprint 16693e94dbced3e408c3ffce8e83a318ae04fc877301a8c275d46ad538893276.
def localCycle00011 : Cycle where
  length := 11
  data := {
    node := ![.distance 0 3, .distance 3 4, .distance 2 3, .distance 3 5, .distance 4 5, .distance 4 6, .distance 1 4, .distance 1 3, .distance 1 2, .theta 2, .distance 0 2, .distance 0 3]
    constant := ![-1, -1, -1, 0, 0, -1, 0, 0, 0, 3, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0]
    strict := ![false, false, false, true, true, false, false, false, false, false, true] }
  origin := ![.triangle 9 0, .triangle 25 0, .triangle 26 0, .triangle 31 1, .triangle 34 2, .triangle 23 0, .gapLower 1 2, .gapLower 1 1, .gapLower 2 0, .corridorUpper 0 2, .triangle 5 2]

-- Cycle fingerprint 1a68841d92128cda547a832f2bbd9c55f7bcd474a44782ab74279f22b48778e3.
def localCycle00012 : Cycle where
  length := 12
  data := {
    node := ![.distance 0 5, .distance 5 6, .distance 4 6, .distance 3 4, .distance 4 5, .distance 1 4, .distance 1 3, .theta 1, .distance 0 1, .distance 0 2, .distance 0 3, .distance 0 4, .distance 0 5]
    constant := ![-1, 0, -1, -1, -1, 0, -1, 3, 0, 0, 0, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false, false, true, true, true, true] }
  origin := ![.triangle 14 0, .triangle 34 2, .triangle 32 0, .triangle 31 0, .triangle 22 0, .gapLower 1 2, .corridorLower 1 3, .corridorUpper 0 1, .triangle 0 2, .triangle 5 2, .triangle 9 2, .triangle 12 2]

-- Cycle fingerprint 1db0dde44d9bb5f1c724443944a659974791d5736d3bb6e3fb37c3fb8817ab90.
def localCycle00013 : Cycle where
  length := 11
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 2, .distance 0 3, .distance 0 4, .distance 0 5, .distance 5 6, .distance 4 5, .distance 3 4, .distance 1 3, .distance 1 2, .theta 1]
    constant := ![3, 0, 0, 0, 0, -1, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, true, false, false, false, false, false, false] }
  origin := ![.corridorUpper 0 1, .triangle 0 2, .triangle 5 2, .triangle 9 2, .triangle 12 2, .triangle 14 0, .triangle 34 0, .triangle 31 0, .triangle 19 0, .gapLower 1 1, .corridorLower 1 2]

-- Cycle fingerprint 1f9af05d90c4d2dad20a30589a8de11e43274f8446f33a013ebac644a7a6c011.
def localCycle00014 : Cycle where
  length := 12
  data := {
    node := ![.distance 4 5, .distance 3 5, .distance 2 3, .distance 3 6, .distance 3 4, .distance 1 3, .distance 1 2, .theta 1, .distance 0 1, .distance 0 2, .distance 0 3, .distance 0 4, .distance 4 5]
    constant := ![0, -1, -1, 0, -1, 0, -1, 3, 0, 0, 0, -1]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0]
    strict := ![true, false, false, true, false, false, false, false, true, true, true, false] }
  origin := ![.triangle 31 2, .triangle 26 0, .triangle 27 0, .triangle 32 1, .triangle 19 0, .gapLower 1 1, .corridorLower 1 2, .corridorUpper 0 1, .triangle 0 2, .triangle 5 2, .triangle 9 2, .triangle 12 0]

-- Cycle fingerprint 216861f9f90746406ab86e8e951f67823a6d4d07f46712a34060de4fbab21aa7.
def localCycle00015 : Cycle where
  length := 10
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 2, .distance 0 3, .distance 3 4, .distance 2 4, .distance 4 5, .distance 5 6, .distance 1 5, .distance 1 4, .theta 1]
    constant := ![3, 0, 0, -1, 0, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, false, false, false, false] }
  origin := ![.corridorUpper 0 1, .triangle 0 2, .triangle 5 2, .triangle 9 0, .triangle 25 2, .triangle 28 0, .triangle 34 0, .triangle 24 0, .gapLower 1 3, .corridorLower 1 4]

-- Cycle fingerprint 255df5c7427d4f9aa878e70d8b137837181641921b35b6e2451b725de6bff85a.
def localCycle00016 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 0 3, .distance 3 4, .distance 2 3, .distance 3 6, .distance 4 6, .distance 1 4, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, -1, -1, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, false, true] }
  origin := ![.corridorUpper 0 3, .triangle 9 0, .triangle 25 0, .triangle 27 0, .triangle 32 1, .triangle 23 0, .triangle 22 0, .corridorLower 4 5, .thetaNext 3]

-- Cycle fingerprint 28546d2775fb107c303d08e6583e55980fb01d9492bd0ff11d91df4fddc91c97.
def localCycle00017 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 0 3, .distance 3 4, .distance 2 3, .distance 3 5, .distance 5 6, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, -1, -1, -1, -1, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, true] }
  origin := ![.corridorUpper 0 3, .triangle 9 0, .triangle 25 0, .triangle 26 0, .triangle 33 0, .triangle 34 0, .gapLower 4 0, .thetaNext 3]

-- Cycle fingerprint 286c3523cd1ce39af263e7c453558be5569ea14c10eda0cd6f00639ee7439d21.
def localCycle00018 : Cycle where
  length := 11
  data := {
    node := ![.distance 0 2, .distance 0 3, .distance 3 4, .distance 2 3, .distance 3 5, .distance 5 6, .distance 4 5, .distance 1 4, .distance 1 3, .theta 3, .theta 2, .distance 0 2]
    constant := ![0, -1, -1, -1, -1, -1, 0, 0, 0, 0, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![true, false, false, false, false, false, false, false, false, true, false] }
  origin := ![.triangle 5 2, .triangle 9 0, .triangle 25 0, .triangle 26 0, .triangle 33 0, .triangle 34 0, .gapLower 4 1, .gapLower 1 2, .gapLower 3 0, .thetaNext 2, .corridorUpper 0 2]

-- Cycle fingerprint 28eac4ff83e4b3861a1c304c1b484074d51ef5b5f086f4d7bfffc96f84c91c0a.
def localCycle00019 : Cycle where
  length := 11
  data := {
    node := ![.distance 0 3, .distance 3 4, .distance 2 3, .distance 3 6, .distance 4 6, .distance 5 6, .distance 1 5, .distance 1 4, .theta 1, .distance 0 1, .distance 0 2, .distance 0 3]
    constant := ![-1, -1, -1, 0, 0, -1, 0, -1, 3, 0, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0]
    strict := ![false, false, false, true, true, false, false, false, false, true, true] }
  origin := ![.triangle 9 0, .triangle 25 0, .triangle 27 0, .triangle 32 1, .triangle 34 1, .triangle 24 0, .gapLower 1 3, .corridorLower 1 4, .corridorUpper 0 1, .triangle 0 2, .triangle 5 2]

-- Cycle fingerprint 2c3ce5d3cd0b2c8923dc0d9da8ff3944c40d3df36ae443343cdc152a586bd84f.
def localCycle00020 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 0 3, .distance 3 4, .distance 2 3, .distance 3 6, .distance 4 6, .distance 1 4, .distance 1 3, .theta 1, .distance 0 1]
    constant := ![0, 0, -1, -1, -1, 0, -1, 0, -1, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![true, true, false, false, false, true, false, false, false, false] }
  origin := ![.triangle 0 2, .triangle 5 2, .triangle 9 0, .triangle 25 0, .triangle 27 0, .triangle 32 1, .triangle 23 0, .gapLower 1 2, .corridorLower 1 3, .corridorUpper 0 1]

-- Cycle fingerprint 2c3e94a505dcff6f6110b5c339b768e0ebc33072d78ab327fda4f2ff6885b76b.
def localCycle00021 : Cycle where
  length := 10
  data := {
    node := ![.theta 2, .distance 0 2, .distance 2 3, .distance 3 4, .distance 1 3, .distance 3 6, .distance 5 6, .distance 4 5, .theta 4, .theta 3, .theta 2]
    constant := ![3, -1, -1, -1, -1, 0, -1, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, false, true, true] }
  origin := ![.corridorUpper 0 2, .triangle 5 0, .triangle 25 0, .triangle 19 0, .triangle 21 0, .triangle 33 1, .triangle 34 0, .corridorLower 4 5, .thetaNext 3, .thetaNext 2]

-- Cycle fingerprint 33fc96528c0e000d6eeeebcc16e5811fa9a0aa53ce6f68595c44d0a2c13258bc.
def localCycle00022 : Cycle where
  length := 10
  data := {
    node := ![.theta 3, .distance 0 3, .distance 3 4, .distance 2 4, .distance 2 5, .distance 5 6, .distance 4 6, .distance 1 4, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, -1, 0, 0, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, true, false, false, false, true] }
  origin := ![.corridorUpper 0 3, .triangle 9 0, .triangle 25 2, .triangle 28 2, .triangle 30 0, .triangle 34 2, .triangle 23 0, .triangle 22 0, .corridorLower 4 5, .thetaNext 3]

-- Cycle fingerprint 35062fb4f8441ec810e650d51e825631aed1c1fc29457fbf207a79330b6cf9c7.
def localCycle00023 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 3, .distance 3 6, .theta 3, .distance 0 3, .distance 3 4, .distance 4 5, .distance 1 4, .distance 1 3]
    constant := ![-1, -1, 3, -1, -1, -1, 0]
    coefficient := ![0, 0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.triangle 21 0, .corridorLower 3 6, .corridorUpper 0 3, .triangle 9 0, .triangle 31 0, .triangle 22 0, .gapLower 1 3]

-- Cycle fingerprint 35f6c37b7516ea24af15cdb90c0586e877fbc0669289a36c457f4e43c037069b.
def localCycle00024 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 3, .theta 1, .distance 0 1, .distance 0 2, .distance 0 3, .distance 3 4, .distance 4 5, .distance 2 4, .distance 4 6, .distance 1 4, .distance 1 3]
    constant := ![-1, 3, 0, 0, -1, -1, -1, -1, -1, 0]
    coefficient := ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, false, false, false] }
  origin := ![.corridorLower 1 3, .corridorUpper 0 1, .triangle 0 2, .triangle 5 2, .triangle 9 0, .triangle 31 0, .triangle 28 0, .triangle 29 0, .triangle 23 0, .gapLower 1 2]

-- Cycle fingerprint 3ad3e40667b28c5b0b5022ee580c870bc46f4edb6e2c0abec40169b3f4bb0644.
def localCycle00025 : Cycle where
  length := 11
  data := {
    node := ![.distance 0 2, .distance 0 3, .distance 3 4, .distance 2 3, .distance 3 6, .distance 4 6, .distance 4 5, .distance 1 4, .distance 1 3, .theta 1, .distance 0 1, .distance 0 2]
    constant := ![0, -1, -1, -1, 0, 0, -1, 0, -1, 3, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0]
    strict := ![true, false, false, false, true, true, false, false, false, false, true] }
  origin := ![.triangle 5 2, .triangle 9 0, .triangle 25 0, .triangle 27 0, .triangle 32 1, .triangle 34 1, .triangle 22 0, .gapLower 1 2, .corridorLower 1 3, .corridorUpper 0 1, .triangle 0 2]

-- Cycle fingerprint 4183c4f9f3119ec9c9afadd15346022f6103c59e7ceb356da78ccae6a7d1c5f8.
def localCycle00026 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 0 3, .distance 3 4, .distance 2 3, .distance 3 5, .distance 1 3, .distance 3 6, .theta 3]
    constant := ![3, -1, -1, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.corridorUpper 0 3, .triangle 9 0, .triangle 25 0, .triangle 26 0, .triangle 20 0, .triangle 21 0, .corridorLower 3 6]

-- Cycle fingerprint 42c5d6d99524cb6bae03bb76c954d4473fd16370823f85ca7dbc660a3d5c493b.
def localCycle00027 : Cycle where
  length := 11
  data := {
    node := ![.distance 0 2, .distance 0 3, .distance 3 4, .distance 2 3, .distance 3 5, .distance 4 5, .distance 5 6, .distance 1 5, .distance 1 4, .theta 1, .distance 0 1, .distance 0 2]
    constant := ![0, -1, -1, -1, 0, -1, -1, 0, -1, 3, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0]
    strict := ![true, false, false, false, true, false, false, false, false, false, true] }
  origin := ![.triangle 5 2, .triangle 9 0, .triangle 25 0, .triangle 26 0, .triangle 31 1, .triangle 34 0, .triangle 24 0, .gapLower 1 3, .corridorLower 1 4, .corridorUpper 0 1, .triangle 0 2]

-- Cycle fingerprint 43c32e4016996a422693da5f948ec270be69b0bf697922292a9fcfc323d0742b.
def localCycle00028 : Cycle where
  length := 9
  data := {
    node := ![.distance 4 5, .distance 5 6, .distance 1 5, .distance 1 4, .theta 1, .distance 0 1, .distance 0 2, .distance 2 3, .distance 3 4, .distance 4 5]
    constant := ![-1, -1, 0, -1, 3, 0, -1, -1, -1]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, false, false] }
  origin := ![.triangle 34 0, .triangle 24 0, .gapLower 1 3, .corridorLower 1 4, .corridorUpper 0 1, .triangle 0 2, .triangle 5 0, .triangle 25 0, .triangle 31 0]

-- Cycle fingerprint 4480d4812637bf390f8e81d1a4ff689bf3975d68f4ab9c2d0bc36a98f98a6592.
def localCycle00029 : Cycle where
  length := 10
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 2, .distance 0 3, .distance 3 4, .distance 4 5, .distance 4 6, .distance 2 4, .distance 2 3, .distance 1 2, .theta 1]
    constant := ![3, 0, 0, -1, -1, 0, -1, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, true, false, false, false, false] }
  origin := ![.corridorUpper 0 1, .triangle 0 2, .triangle 5 2, .triangle 9 0, .triangle 31 0, .triangle 34 2, .triangle 29 0, .gapLower 2 2, .triangle 15 0, .corridorLower 1 2]

-- Cycle fingerprint 459b324a563cecc62f9d6c1b56db00bfb5f01cf95fb88f0f4eef91729798b1db.
def localCycle00030 : Cycle where
  length := 11
  data := {
    node := ![.distance 1 2, .theta 1, .distance 0 1, .distance 0 2, .distance 0 3, .distance 3 4, .distance 4 6, .distance 2 4, .distance 2 3, .distance 3 5, .distance 1 3, .distance 1 2]
    constant := ![-1, 3, 0, 0, -1, -1, -1, 0, -1, -1, 0]
    coefficient := ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, false, false, false, false] }
  origin := ![.corridorLower 1 2, .corridorUpper 0 1, .triangle 0 2, .triangle 5 2, .triangle 9 0, .triangle 32 0, .triangle 29 0, .gapLower 2 3, .triangle 26 0, .triangle 20 0, .gapLower 1 1]

-- Cycle fingerprint 47b52f77bf4504ad1fa0354f69af2b2cb5be2f2f1069b2f619cb9742c14082ff.
def localCycle00031 : Cycle where
  length := 13
  data := {
    node := ![.distance 2 4, .distance 4 5, .distance 3 4, .distance 1 3, .distance 1 2, .theta 1, .distance 0 1, .distance 0 2, .distance 0 3, .distance 0 4, .distance 0 5, .distance 5 6, .distance 4 6, .distance 2 4]
    constant := ![-1, -1, -1, 0, -1, 3, 0, 0, 0, 0, -1, 0, -1]
    coefficient := ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, true, true, true, false, true, false] }
  origin := ![.triangle 28 0, .triangle 31 0, .triangle 19 0, .gapLower 1 1, .corridorLower 1 2, .corridorUpper 0 1, .triangle 0 2, .triangle 5 2, .triangle 9 2, .triangle 12 2, .triangle 14 0, .triangle 34 2, .triangle 29 0]

-- Cycle fingerprint 506ce8a412ec2ee2f12fb8f808f23c032ce5920f90cb8c6539763a7721272f09.
def localCycle00032 : Cycle where
  length := 11
  data := {
    node := ![.distance 0 2, .distance 2 3, .distance 2 4, .distance 4 5, .distance 3 4, .distance 4 6, .distance 5 6, .distance 1 5, .distance 1 4, .theta 1, .distance 0 1, .distance 0 2]
    constant := ![-1, 0, -1, -1, -1, 0, -1, 0, -1, 3, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0]
    strict := ![false, true, false, false, false, true, false, false, false, false, true] }
  origin := ![.triangle 5 0, .triangle 25 2, .triangle 28 0, .triangle 31 0, .triangle 32 0, .triangle 34 1, .triangle 24 0, .gapLower 1 3, .corridorLower 1 4, .corridorUpper 0 1, .triangle 0 2]

-- Cycle fingerprint 51df9fbeea88858acdc35e30f5566117e603b8bab562e8a0f5386b16fcd062cc.
def localCycle00033 : Cycle where
  length := 15
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 2, .distance 2 3, .distance 3 4, .distance 4 6, .distance 4 5, .theta 4, .theta 3, .distance 0 3, .distance 0 4, .distance 0 5, .distance 5 6, .distance 2 5, .distance 1 2, .theta 1]
    constant := ![3, 0, -1, -1, -1, 0, -1, 0, 3, 0, 0, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, true, false, true, false, true, true, false, false, false, false] }
  origin := ![.corridorUpper 0 1, .triangle 0 2, .triangle 5 0, .triangle 25 0, .triangle 32 0, .triangle 34 1, .corridorLower 4 5, .thetaNext 3, .corridorUpper 0 3, .triangle 9 2, .triangle 12 2, .triangle 14 0, .triangle 30 0, .triangle 17 0, .corridorLower 1 2]

-- Cycle fingerprint 53d2855dad0bb910c1eb783d6d37079c77830abe912869da0b0c1a0eef688d56.
def localCycle00034 : Cycle where
  length := 11
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 2, .distance 2 3, .distance 2 4, .distance 4 6, .distance 3 4, .distance 4 5, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1]
    constant := ![3, 0, -1, 0, -1, -1, -1, -1, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, false, false, false, false, false] }
  origin := ![.corridorUpper 0 1, .triangle 0 2, .triangle 5 0, .triangle 25 2, .triangle 29 0, .triangle 32 0, .triangle 31 0, .triangle 22 0, .gapLower 1 2, .gapLower 1 1, .corridorLower 1 2]

-- Cycle fingerprint 5483021e158628af5817c1b9447f78089bab45ba37720b826792bdb04d353670.
def localCycle00035 : Cycle where
  length := 6
  data := {
    node := ![.theta 3, .distance 0 3, .distance 3 4, .distance 2 3, .distance 3 5, .distance 3 6, .theta 3]
    constant := ![3, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false] }
  origin := ![.corridorUpper 0 3, .triangle 9 0, .triangle 25 0, .triangle 26 0, .triangle 33 2, .corridorLower 3 6]

-- Cycle fingerprint 55089b3fb6a5147b90ab43729dd26b0b747b1b4d5d4766df27c6d63132cc7c31.
def localCycle00036 : Cycle where
  length := 11
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 0 3, .distance 0 4, .distance 4 5, .distance 3 4, .distance 4 6, .distance 2 4, .distance 2 3, .distance 1 2, .theta 1, .distance 0 1]
    constant := ![0, 0, 0, -1, -1, -1, -1, 0, -1, -1, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![true, true, true, false, false, false, false, false, false, false, false] }
  origin := ![.triangle 0 2, .triangle 5 2, .triangle 9 2, .triangle 12 0, .triangle 31 0, .triangle 32 0, .triangle 29 0, .gapLower 2 2, .triangle 15 0, .corridorLower 1 2, .corridorUpper 0 1]

-- Cycle fingerprint 55efcdcafe8fae20887c0b6cdda0b237abd1ced60847539ac4aabcea1694e530.
def localCycle00037 : Cycle where
  length := 11
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 0 3, .distance 0 4, .distance 4 5, .distance 3 5, .distance 2 3, .distance 3 4, .distance 1 3, .distance 1 2, .theta 1, .distance 0 1]
    constant := ![0, 0, 0, -1, 0, -1, -1, -1, 0, -1, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![true, true, true, false, true, false, false, false, false, false, false] }
  origin := ![.triangle 0 2, .triangle 5 2, .triangle 9 2, .triangle 12 0, .triangle 31 2, .triangle 26 0, .triangle 25 0, .triangle 19 0, .gapLower 1 1, .corridorLower 1 2, .corridorUpper 0 1]

-- Cycle fingerprint 56c7e10702e5a760868d9862006ff7f2e8c41050dc6fc02e825fbfce05ff2d45.
def localCycle00038 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 0 3, .distance 0 4, .distance 0 5, .distance 5 6, .distance 4 6, .distance 3 4, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, 0, 0, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, false, false, true] }
  origin := ![.corridorUpper 0 3, .triangle 9 2, .triangle 12 2, .triangle 14 0, .triangle 34 2, .triangle 32 0, .triangle 31 0, .corridorLower 4 5, .thetaNext 3]

-- Cycle fingerprint 68ef1b73df3a2563ff78a56783ccd469c66891d4f33c5719e4da0a6df341d2c7.
def localCycle00039 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 0 3, .distance 3 4, .distance 2 4, .distance 4 5, .distance 1 4, .distance 4 6, .theta 4, .theta 3]
    constant := ![3, -1, 0, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, true] }
  origin := ![.corridorUpper 0 3, .triangle 9 0, .triangle 25 2, .triangle 28 0, .triangle 22 0, .triangle 23 0, .corridorLower 4 6, .thetaNext 3]

-- Cycle fingerprint 729b5478e31c1301e1b9b7e8d3a3a9d8c5be71471ba1be52c4292b4f2885f5c8.
def localCycle00040 : Cycle where
  length := 12
  data := {
    node := ![.distance 5 6, .distance 3 5, .distance 2 3, .distance 3 4, .distance 1 3, .distance 1 2, .theta 1, .distance 0 1, .distance 0 2, .distance 0 3, .distance 0 4, .distance 0 5, .distance 5 6]
    constant := ![-1, -1, -1, -1, 0, -1, 3, 0, 0, 0, 0, -1]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, true, true, true, true, false] }
  origin := ![.triangle 33 0, .triangle 26 0, .triangle 25 0, .triangle 19 0, .gapLower 1 1, .corridorLower 1 2, .corridorUpper 0 1, .triangle 0 2, .triangle 5 2, .triangle 9 2, .triangle 12 2, .triangle 14 0]

-- Cycle fingerprint 72abfbe907e94f79ac7a6388afd81c3ab481746173b232e809b5afbf3647e3a2.
def localCycle00041 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 0 2, .distance 2 3, .distance 2 4, .distance 4 5, .distance 3 4, .distance 1 3, .distance 3 6, .theta 3, .theta 2]
    constant := ![3, -1, 0, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false, true] }
  origin := ![.corridorUpper 0 2, .triangle 5 0, .triangle 25 2, .triangle 28 0, .triangle 31 0, .triangle 19 0, .triangle 21 0, .corridorLower 3 6, .thetaNext 2]

-- Cycle fingerprint 773351396d744f923e52ddf1f6fadd4bd403686eda7fc6be71dff07afd901be3.
def localCycle00042 : Cycle where
  length := 8
  data := {
    node := ![.theta 2, .distance 0 2, .distance 2 3, .distance 3 4, .distance 3 5, .distance 1 3, .distance 3 6, .theta 3, .theta 2]
    constant := ![3, -1, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, true] }
  origin := ![.corridorUpper 0 2, .triangle 5 0, .triangle 25 0, .triangle 31 2, .triangle 20 0, .triangle 21 0, .corridorLower 3 6, .thetaNext 2]

-- Cycle fingerprint 7b945f5ecce06249a4e56bf752a89f51312674fd1e7707730cf9c447f653168e.
def localCycle00043 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 0 3, .distance 3 4, .distance 4 5, .distance 1 4, .distance 4 6, .theta 4, .theta 3]
    constant := ![3, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true] }
  origin := ![.corridorUpper 0 3, .triangle 9 0, .triangle 31 0, .triangle 22 0, .triangle 23 0, .corridorLower 4 6, .thetaNext 3]

-- Cycle fingerprint 7bb01afec98b985b09c833155be1b8f9d981b9563ed91c457b5f7eed64a84860.
def localCycle00044 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 3, .theta 3, .theta 2, .distance 0 2, .distance 2 3, .distance 3 4, .distance 3 5, .distance 5 6, .distance 4 5, .distance 1 4, .distance 1 3]
    constant := ![0, 0, 3, -1, -1, 0, -1, -1, -1, 0]
    coefficient := ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, true, false, false, false, false] }
  origin := ![.gapLower 3 0, .thetaNext 2, .corridorUpper 0 2, .triangle 5 0, .triangle 25 0, .triangle 31 2, .triangle 33 0, .triangle 34 0, .triangle 22 0, .gapLower 1 2]

-- Cycle fingerprint 7e6a320eaa07bdb60d94bcd06068d6662d66d9948bd65bccba38342e405ebc85.
def localCycle00045 : Cycle where
  length := 11
  data := {
    node := ![.distance 0 2, .distance 0 3, .distance 0 4, .distance 4 5, .distance 2 4, .distance 4 6, .distance 5 6, .distance 1 5, .distance 1 4, .theta 1, .distance 0 1, .distance 0 2]
    constant := ![0, 0, -1, -1, -1, 0, -1, 0, -1, 3, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0]
    strict := ![true, true, false, false, false, true, false, false, false, false, true] }
  origin := ![.triangle 5 2, .triangle 9 2, .triangle 12 0, .triangle 28 0, .triangle 29 0, .triangle 34 1, .triangle 24 0, .gapLower 1 3, .corridorLower 1 4, .corridorUpper 0 1, .triangle 0 2]

-- Cycle fingerprint 7f99f021d3185e0e5ce8437c90818f8bba44d61fa6fcfd958e4803723757ad25.
def localCycle00046 : Cycle where
  length := 13
  data := {
    node := ![.distance 0 4, .distance 4 5, .distance 5 6, .distance 3 6, .distance 2 3, .distance 3 5, .distance 3 4, .distance 1 3, .distance 1 2, .theta 1, .distance 0 1, .distance 0 2, .distance 0 3, .distance 0 4]
    constant := ![-1, -1, 0, -1, -1, 0, -1, 0, -1, 3, 0, 0, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, false, false, false, true, true, true] }
  origin := ![.triangle 12 0, .triangle 34 0, .gapLower 6 3, .triangle 27 0, .triangle 26 0, .triangle 31 1, .triangle 19 0, .gapLower 1 1, .corridorLower 1 2, .corridorUpper 0 1, .triangle 0 2, .triangle 5 2, .triangle 9 2]

-- Cycle fingerprint 8110bb3bb9b16da8fe6076c8f5c6c7829d94f18edb9e3ac4b984f9125877c0e6.
def localCycle00047 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 0 4, .distance 4 5, .distance 3 4, .distance 1 3, .distance 3 6, .distance 4 6, .theta 4]
    constant := ![3, -1, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false] }
  origin := ![.corridorUpper 0 4, .triangle 12 0, .triangle 31 0, .triangle 19 0, .triangle 21 0, .triangle 32 1, .corridorLower 4 6]

-- Cycle fingerprint 81444cbfbc57b513209198150db5f3527bf493686e622e6311ef502114f072a1.
def localCycle00048 : Cycle where
  length := 10
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 2, .distance 0 3, .distance 0 4, .distance 0 5, .distance 5 6, .distance 4 5, .distance 2 4, .distance 1 2, .theta 1]
    constant := ![3, 0, 0, 0, 0, -1, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, true, false, false, false, false, false] }
  origin := ![.corridorUpper 0 1, .triangle 0 2, .triangle 5 2, .triangle 9 2, .triangle 12 2, .triangle 14 0, .triangle 34 0, .triangle 28 0, .triangle 16 0, .corridorLower 1 2]

-- Cycle fingerprint 819d92127e91f5001d56aa3fd2ce995a4eb3a3dfa0b7d0fe774e1a86d68ecc8b.
def localCycle00049 : Cycle where
  length := 12
  data := {
    node := ![.distance 4 5, .distance 2 5, .distance 5 6, .distance 3 5, .distance 3 4, .distance 1 3, .distance 1 2, .theta 1, .distance 0 1, .distance 0 2, .distance 0 3, .distance 0 4, .distance 4 5]
    constant := ![0, -1, -1, 0, -1, 0, -1, 3, 0, 0, 0, -1]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0]
    strict := ![true, false, false, true, false, false, false, false, true, true, true, false] }
  origin := ![.triangle 28 2, .triangle 30 0, .triangle 33 0, .triangle 31 1, .triangle 19 0, .gapLower 1 1, .corridorLower 1 2, .corridorUpper 0 1, .triangle 0 2, .triangle 5 2, .triangle 9 2, .triangle 12 0]

-- Cycle fingerprint 82b549dfb3cc1e13ffd6fefe945a0f7ebc50d90d47378a2e74b33a4099eafd8c.
def localCycle00050 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 0 3, .distance 3 4, .distance 2 3, .distance 3 5, .distance 4 5, .distance 1 4, .distance 4 6, .theta 4, .theta 3]
    constant := ![3, -1, -1, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, false, true] }
  origin := ![.corridorUpper 0 3, .triangle 9 0, .triangle 25 0, .triangle 26 0, .triangle 31 1, .triangle 22 0, .triangle 23 0, .corridorLower 4 6, .thetaNext 3]

-- Cycle fingerprint 87ed1fb693bf6b78889bbd275c2b0a5e8a20631862df908f3a5b16bb5834ea58.
def localCycle00051 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 0 2, .distance 2 3, .distance 3 4, .distance 4 5, .distance 5 6, .theta 5, .theta 4, .theta 3, .theta 2]
    constant := ![3, -1, -1, -1, -1, -1, 0, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, true, true] }
  origin := ![.corridorUpper 0 2, .triangle 5 0, .triangle 25 0, .triangle 31 0, .triangle 34 0, .corridorLower 5 6, .thetaNext 4, .thetaNext 3, .thetaNext 2]

-- Cycle fingerprint 88789410b5f96aec7753c04897667f6b3a7d473ef8d957d93b1b6a2272bca982.
def localCycle00052 : Cycle where
  length := 9
  data := {
    node := ![.distance 4 6, .distance 1 4, .distance 1 3, .theta 3, .theta 2, .distance 0 2, .distance 2 3, .distance 3 4, .distance 4 5, .distance 4 6]
    constant := ![-1, 0, 0, 0, 3, -1, -1, -1, 0]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, false, true] }
  origin := ![.triangle 23 0, .gapLower 1 2, .gapLower 3 0, .thetaNext 2, .corridorUpper 0 2, .triangle 5 0, .triangle 25 0, .triangle 31 0, .triangle 34 2]

-- Cycle fingerprint 88f7de214ac93e6e70a8b67c591577843f9914d201da5dead8f59d5974fdb4ed.
def localCycle00053 : Cycle where
  length := 13
  data := {
    node := ![.distance 3 5, .distance 4 5, .distance 1 4, .distance 1 3, .theta 1, .distance 0 1, .distance 0 2, .distance 0 3, .distance 0 4, .distance 0 5, .distance 5 6, .distance 3 6, .distance 2 3, .distance 3 5]
    constant := ![0, -1, 0, -1, 3, 0, 0, 0, 0, -1, 0, -1, -1]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![true, false, false, false, false, true, true, true, true, false, true, false, false] }
  origin := ![.triangle 31 1, .triangle 22 0, .gapLower 1 2, .corridorLower 1 3, .corridorUpper 0 1, .triangle 0 2, .triangle 5 2, .triangle 9 2, .triangle 12 2, .triangle 14 0, .triangle 33 2, .triangle 27 0, .triangle 26 0]

-- Cycle fingerprint 8ec4e8fd7901f78adcc2f12ba61979961f35afce9450f075273dc1cc80e0607b.
def localCycle00054 : Cycle where
  length := 10
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 2, .distance 0 3, .distance 0 4, .distance 4 5, .distance 3 4, .distance 3 6, .distance 2 3, .distance 1 2, .theta 1]
    constant := ![3, 0, 0, 0, -1, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, false, true, false, false, false] }
  origin := ![.corridorUpper 0 1, .triangle 0 2, .triangle 5 2, .triangle 9 2, .triangle 12 0, .triangle 31 0, .triangle 32 2, .triangle 27 0, .triangle 15 0, .corridorLower 1 2]

-- Cycle fingerprint 8f12adf87ddc1edf3432d71d4508bb22498b093acf193191856aa85b738cd423.
def localCycle00055 : Cycle where
  length := 12
  data := {
    node := ![.distance 0 4, .distance 0 5, .distance 5 6, .distance 3 6, .distance 2 3, .distance 3 5, .distance 1 3, .distance 1 2, .theta 1, .distance 0 1, .distance 0 2, .distance 0 3, .distance 0 4]
    constant := ![0, -1, 0, -1, -1, -1, 0, -1, 3, 0, 0, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![true, false, true, false, false, false, false, false, false, true, true, true] }
  origin := ![.triangle 12 2, .triangle 14 0, .triangle 33 2, .triangle 27 0, .triangle 26 0, .triangle 20 0, .gapLower 1 1, .corridorLower 1 2, .corridorUpper 0 1, .triangle 0 2, .triangle 5 2, .triangle 9 2]

-- Cycle fingerprint 8fb54b73d40fbb27ea8e06fbf365001f5b038bf7e1477e4653a6a50af213703c.
def localCycle00056 : Cycle where
  length := 11
  data := {
    node := ![.distance 0 2, .distance 0 3, .distance 0 4, .distance 4 5, .distance 3 5, .distance 2 3, .distance 3 6, .distance 1 3, .distance 1 2, .theta 1, .distance 0 1, .distance 0 2]
    constant := ![0, 0, -1, 0, -1, -1, -1, 0, -1, 3, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0]
    strict := ![true, true, false, true, false, false, false, false, false, false, true] }
  origin := ![.triangle 5 2, .triangle 9 2, .triangle 12 0, .triangle 31 2, .triangle 26 0, .triangle 27 0, .triangle 21 0, .gapLower 1 1, .corridorLower 1 2, .corridorUpper 0 1, .triangle 0 2]

-- Cycle fingerprint 9028825a95d1c44a0a45773011cc53d089cc3fe87ed0f965c9fb93e273c8d951.
def localCycle00057 : Cycle where
  length := 10
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 2, .distance 0 3, .distance 0 4, .distance 4 5, .distance 5 6, .distance 2 5, .distance 2 4, .distance 1 2, .theta 1]
    constant := ![3, 0, 0, 0, -1, -1, -1, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, false, false, false, false, false] }
  origin := ![.corridorUpper 0 1, .triangle 0 2, .triangle 5 2, .triangle 9 2, .triangle 12 0, .triangle 34 0, .triangle 30 0, .gapLower 2 2, .triangle 16 0, .corridorLower 1 2]

-- Cycle fingerprint 936a24b954231daae0475427fd0c3cebf74e137702bc7ee8dad2095c881b1a11.
def localCycle00058 : Cycle where
  length := 5
  data := {
    node := ![.theta 3, .distance 0 3, .distance 3 4, .distance 2 3, .distance 3 6, .theta 3]
    constant := ![3, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false] }
  origin := ![.corridorUpper 0 3, .triangle 9 0, .triangle 25 0, .triangle 27 0, .corridorLower 3 6]

-- Cycle fingerprint 9462219eae6ed17ba4ead277d91bdb1fd52108504741505cca154f92c4c786f6.
def localCycle00059 : Cycle where
  length := 8
  data := {
    node := ![.distance 2 4, .distance 4 5, .distance 1 4, .distance 1 3, .distance 3 6, .theta 3, .distance 0 3, .distance 3 4, .distance 2 4]
    constant := ![-1, -1, 0, -1, -1, 3, -1, 0]
    coefficient := ![0, 0, 0, 0, 0, 1, 0, 0]
    strict := ![false, false, false, false, false, false, false, true] }
  origin := ![.triangle 28 0, .triangle 22 0, .gapLower 1 3, .triangle 21 0, .corridorLower 3 6, .corridorUpper 0 3, .triangle 9 0, .triangle 25 2]

-- Cycle fingerprint 957d6e624e82b8e5588db6a161d993cc8605e4d3d8a3c7012b4684806b8088bc.
def localCycle00060 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 0 2, .distance 2 3, .distance 3 4, .distance 4 5, .distance 1 4, .distance 4 6, .theta 4, .theta 3, .theta 2]
    constant := ![3, -1, -1, -1, -1, -1, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, true, true] }
  origin := ![.corridorUpper 0 2, .triangle 5 0, .triangle 25 0, .triangle 31 0, .triangle 22 0, .triangle 23 0, .corridorLower 4 6, .thetaNext 3, .thetaNext 2]

-- Cycle fingerprint a0ce8f1d318cdd049800837a0683948bff4d1fd43dbe6ebb74a63384212487eb.
def localCycle00061 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 2, .theta 1, .distance 0 1, .distance 0 2, .distance 0 3, .distance 3 4, .distance 2 3, .distance 3 6, .distance 1 3, .distance 1 2]
    constant := ![-1, 3, 0, 0, -1, -1, -1, -1, 0]
    coefficient := ![0, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, false, false] }
  origin := ![.corridorLower 1 2, .corridorUpper 0 1, .triangle 0 2, .triangle 5 2, .triangle 9 0, .triangle 25 0, .triangle 27 0, .triangle 21 0, .gapLower 1 1]

-- Cycle fingerprint a1b00f24414f57e56058f12a631af52287e9e6715e2d8c4673a5cd54f55f485f.
def localCycle00062 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 0 3, .distance 3 4, .distance 1 3, .distance 3 6, .distance 5 6, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, -1, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, true] }
  origin := ![.corridorUpper 0 3, .triangle 9 0, .triangle 19 0, .triangle 21 0, .triangle 33 1, .triangle 34 0, .corridorLower 4 5, .thetaNext 3]

-- Cycle fingerprint a32a385b43c03687502eeb92da3db9f5bbef917b29847b5e99cb899f2d5c8daa.
def localCycle00063 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 0 3, .distance 3 4, .distance 2 3, .distance 3 6, .distance 5 6, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, -1, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, true] }
  origin := ![.corridorUpper 0 3, .triangle 9 0, .triangle 25 0, .triangle 27 0, .triangle 33 1, .triangle 34 0, .corridorLower 4 5, .thetaNext 3]

-- Cycle fingerprint a5e1c7bc573b8b38d0e9f8b1bf7fb9cc3ca15bdc69b0f74e5f7f3c856ec6a11a.
def localCycle00064 : Cycle where
  length := 9
  data := {
    node := ![.distance 3 4, .distance 3 6, .distance 1 3, .distance 1 2, .theta 2, .distance 0 2, .distance 2 3, .distance 2 4, .distance 4 5, .distance 3 4]
    constant := ![0, -1, 0, 0, 3, -1, 0, -1, -1]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0, 0]
    strict := ![true, false, false, false, false, false, true, false, false] }
  origin := ![.triangle 32 2, .triangle 21 0, .gapLower 1 1, .gapLower 2 0, .corridorUpper 0 2, .triangle 5 0, .triangle 25 2, .triangle 28 0, .triangle 31 0]

-- Cycle fingerprint a9be010e4fbc44e90671acb727c24bee7973d5e5b51bdb102cca332c46df5055.
def localCycle00065 : Cycle where
  length := 11
  data := {
    node := ![.distance 2 5, .distance 5 6, .distance 3 5, .distance 1 3, .distance 1 2, .theta 1, .distance 0 1, .distance 0 2, .distance 0 3, .distance 3 4, .distance 2 3, .distance 2 5]
    constant := ![-1, -1, -1, 0, -1, 3, 0, 0, -1, -1, 0]
    coefficient := ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, true, false, false, true] }
  origin := ![.triangle 30 0, .triangle 33 0, .triangle 20 0, .gapLower 1 1, .corridorLower 1 2, .corridorUpper 0 1, .triangle 0 2, .triangle 5 2, .triangle 9 0, .triangle 25 0, .triangle 26 2]

-- Cycle fingerprint ad9c13dbc58115b86ce7717326e8bbd9776bfd6c4a64a63b2ba42d6bd638cbfc.
def localCycle00066 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 3, .distance 1 2, .theta 1, .distance 0 1, .distance 0 2, .distance 2 3, .distance 2 4, .distance 4 5, .distance 3 4, .distance 1 3]
    constant := ![0, -1, 3, 0, -1, 0, -1, -1, -1]
    coefficient := ![0, 0, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true, false, false, false] }
  origin := ![.gapLower 1 1, .corridorLower 1 2, .corridorUpper 0 1, .triangle 0 2, .triangle 5 0, .triangle 25 2, .triangle 28 0, .triangle 31 0, .triangle 19 0]

-- Cycle fingerprint b1bf567c9b76b74969fbe4c2ea546e9aa4cadb4786c5e9440409f3130439620f.
def localCycle00067 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 3, .theta 1, .distance 0 1, .distance 0 2, .distance 0 3, .distance 0 4, .distance 4 5, .distance 2 4, .distance 4 6, .distance 1 4, .distance 1 3]
    constant := ![-1, 3, 0, 0, 0, -1, -1, -1, -1, 0]
    coefficient := ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, true, false, false, false, false, false] }
  origin := ![.corridorLower 1 3, .corridorUpper 0 1, .triangle 0 2, .triangle 5 2, .triangle 9 2, .triangle 12 0, .triangle 28 0, .triangle 29 0, .triangle 23 0, .gapLower 1 2]

-- Cycle fingerprint b1e3e4fdfaa344a0aad5b8de866d35597f3fe11aa3c647bdb3bafaf91e2cf094.
def localCycle00068 : Cycle where
  length := 9
  data := {
    node := ![.distance 4 6, .distance 4 5, .distance 1 4, .distance 1 3, .theta 1, .distance 0 1, .distance 0 2, .distance 2 3, .distance 3 4, .distance 4 6]
    constant := ![0, -1, 0, -1, 3, 0, -1, -1, -1]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0, 0]
    strict := ![true, false, false, false, false, true, false, false, false] }
  origin := ![.triangle 34 1, .triangle 22 0, .gapLower 1 2, .corridorLower 1 3, .corridorUpper 0 1, .triangle 0 2, .triangle 5 0, .triangle 25 0, .triangle 32 0]

-- Cycle fingerprint b2d95020557018a075167c3c5f6ec640c8fa401f3821ab58ffaa1f4e2490302e.
def localCycle00069 : Cycle where
  length := 10
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 2, .distance 0 3, .distance 0 4, .distance 0 5, .distance 5 6, .distance 3 5, .distance 2 3, .distance 1 2, .theta 1]
    constant := ![3, 0, 0, 0, 0, -1, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, true, false, false, false, false, false] }
  origin := ![.corridorUpper 0 1, .triangle 0 2, .triangle 5 2, .triangle 9 2, .triangle 12 2, .triangle 14 0, .triangle 33 0, .triangle 26 0, .triangle 15 0, .corridorLower 1 2]

-- Cycle fingerprint b554aecd7a08ace4256ab9aa46ac71445252fc218f4bbb1ef5a019b03d77e424.
def localCycle00070 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 2, .distance 2 3, .distance 2 4, .distance 4 6, .distance 3 4, .distance 1 3, .distance 1 2, .theta 2, .distance 0 2]
    constant := ![-1, 0, -1, -1, -1, 0, 0, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, false, false, false, false, false, false] }
  origin := ![.triangle 5 0, .triangle 25 2, .triangle 29 0, .triangle 32 0, .triangle 19 0, .gapLower 1 1, .gapLower 2 0, .corridorUpper 0 2]

-- Cycle fingerprint b99181bff8a7311ae9fe0e08a8297f3ae7e5199583769464ceda6c935569f8c8.
def localCycle00071 : Cycle where
  length := 12
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 2, .distance 2 3, .distance 3 5, .distance 5 6, .theta 5, .theta 4, .distance 0 4, .distance 4 5, .distance 2 4, .distance 1 2, .theta 1]
    constant := ![3, 0, -1, -1, -1, -1, 0, 3, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, true, false, false, false, false, false] }
  origin := ![.corridorUpper 0 1, .triangle 0 2, .triangle 5 0, .triangle 26 0, .triangle 33 0, .corridorLower 5 6, .thetaNext 4, .corridorUpper 0 4, .triangle 12 0, .triangle 28 0, .triangle 16 0, .corridorLower 1 2]

-- Cycle fingerprint ba87f10757de7df75028ee5f22d9b034d8f9b45da16faa12a074a759c7df631b.
def localCycle00072 : Cycle where
  length := 12
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 0 3, .distance 3 4, .distance 4 6, .distance 2 4, .distance 2 3, .distance 3 5, .distance 4 5, .distance 1 4, .distance 1 3, .theta 1, .distance 0 1]
    constant := ![0, 0, -1, -1, -1, 0, -1, 0, -1, 0, -1, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![true, true, false, false, false, false, false, true, false, false, false, false] }
  origin := ![.triangle 0 2, .triangle 5 2, .triangle 9 0, .triangle 32 0, .triangle 29 0, .gapLower 2 3, .triangle 26 0, .triangle 31 1, .triangle 22 0, .gapLower 1 2, .corridorLower 1 3, .corridorUpper 0 1]

-- Cycle fingerprint bf51b607054b6efc9fd8050939f216c04a42a5a3123e60a974575129bc1d14be.
def localCycle00073 : Cycle where
  length := 11
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 0 3, .distance 3 4, .distance 4 5, .distance 2 4, .distance 4 6, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1, .distance 0 1]
    constant := ![0, 0, -1, -1, -1, -1, -1, 0, 0, -1, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![true, true, false, false, false, false, false, false, true, false, false] }
  origin := ![.triangle 0 2, .triangle 5 2, .triangle 9 0, .triangle 31 0, .triangle 28 0, .triangle 29 0, .triangle 23 0, .gapLower 1 2, .triangle 15 1, .corridorLower 1 2, .corridorUpper 0 1]

-- Cycle fingerprint c34462d74074657767918f220d2b82825ecf35084e5ac7e3f0edf662443fda3d.
def localCycle00074 : Cycle where
  length := 11
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 0 3, .distance 3 4, .distance 4 5, .distance 2 4, .distance 2 3, .distance 3 6, .distance 1 3, .distance 1 2, .theta 1, .distance 0 1]
    constant := ![0, 0, -1, -1, -1, 0, -1, -1, 0, -1, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![true, true, false, false, false, false, false, false, false, false, false] }
  origin := ![.triangle 0 2, .triangle 5 2, .triangle 9 0, .triangle 31 0, .triangle 28 0, .gapLower 2 3, .triangle 27 0, .triangle 21 0, .gapLower 1 1, .corridorLower 1 2, .corridorUpper 0 1]

-- Cycle fingerprint c663f05eff72a67d8cd490d2adb5ee283b2275f4da32c35ddc20d6f4a703ece0.
def localCycle00075 : Cycle where
  length := 11
  data := {
    node := ![.distance 0 2, .distance 0 3, .distance 3 4, .distance 2 3, .distance 3 6, .distance 5 6, .distance 4 5, .distance 1 4, .distance 1 3, .theta 3, .theta 2, .distance 0 2]
    constant := ![0, -1, -1, -1, 0, -1, -1, 0, 0, 0, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![true, false, false, false, true, false, false, false, false, true, false] }
  origin := ![.triangle 5 2, .triangle 9 0, .triangle 25 0, .triangle 27 0, .triangle 33 1, .triangle 34 0, .triangle 22 0, .gapLower 1 2, .gapLower 3 0, .thetaNext 2, .corridorUpper 0 2]

-- Cycle fingerprint cbe20a5769106d153dcc505c2ebc16e06eef8740ae7f7afbab8ecd9889402528.
def localCycle00076 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 3, .distance 1 2, .theta 1, .distance 0 1, .distance 0 2, .distance 2 3, .distance 2 4, .distance 2 5, .distance 5 6, .distance 3 5, .distance 1 3]
    constant := ![0, -1, 3, 0, -1, 0, 0, -1, -1, -1]
    coefficient := ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true, true, false, false, false] }
  origin := ![.gapLower 1 1, .corridorLower 1 2, .corridorUpper 0 1, .triangle 0 2, .triangle 5 0, .triangle 25 2, .triangle 28 2, .triangle 30 0, .triangle 33 0, .triangle 20 0]

-- Cycle fingerprint cf195721ce351962e166dee63e5173e989ad87afc7e6982fc868b953b2efd4ae.
def localCycle00077 : Cycle where
  length := 10
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 2, .distance 0 3, .distance 3 4, .distance 2 3, .distance 3 6, .distance 3 5, .distance 1 3, .distance 1 2, .theta 1]
    constant := ![3, 0, 0, -1, -1, -1, 0, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, false, true, false, false, false] }
  origin := ![.corridorUpper 0 1, .triangle 0 2, .triangle 5 2, .triangle 9 0, .triangle 25 0, .triangle 27 0, .triangle 33 1, .triangle 20 0, .gapLower 1 1, .corridorLower 1 2]

-- Cycle fingerprint cfd39b57c186fae634b476a96663dafab6ade1231a90aacd986929f02b6d57ef.
def localCycle00078 : Cycle where
  length := 11
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 2, .distance 2 3, .distance 2 4, .distance 4 5, .distance 5 6, .distance 3 5, .distance 3 4, .distance 1 3, .distance 1 2, .theta 1]
    constant := ![3, 0, -1, 0, -1, -1, -1, 0, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, false, false, false, false, false] }
  origin := ![.corridorUpper 0 1, .triangle 0 2, .triangle 5 0, .triangle 25 2, .triangle 28 0, .triangle 34 0, .triangle 33 0, .gapLower 3 2, .triangle 19 0, .gapLower 1 1, .corridorLower 1 2]

-- Cycle fingerprint d1a39932bdd1c5bbddc5e3f45eaeca880dedd8fc68bd5fe9242a097ee5e6cfc0.
def localCycle00079 : Cycle where
  length := 11
  data := {
    node := ![.theta 2, .distance 0 2, .distance 0 3, .distance 3 4, .distance 2 4, .distance 4 5, .distance 1 5, .distance 5 6, .theta 5, .theta 4, .theta 3, .theta 2]
    constant := ![3, 0, -1, 0, -1, 0, -1, -1, 0, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, true, false, false, true, true, true] }
  origin := ![.corridorUpper 0 2, .triangle 5 2, .triangle 9 0, .triangle 25 2, .triangle 28 0, .triangle 22 2, .triangle 24 0, .corridorLower 5 6, .thetaNext 4, .thetaNext 3, .thetaNext 2]

-- Cycle fingerprint d92410b3334b99d7dba0afc00c97bb3e3605016b92dc55539ce86be715e8d67d.
def localCycle00080 : Cycle where
  length := 11
  data := {
    node := ![.theta 2, .distance 0 2, .distance 2 3, .distance 3 4, .distance 3 5, .distance 5 6, .distance 4 6, .distance 1 4, .distance 4 5, .theta 4, .theta 3, .theta 2]
    constant := ![3, -1, -1, 0, -1, 0, -1, -1, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true, false, false, false, true, true] }
  origin := ![.corridorUpper 0 2, .triangle 5 0, .triangle 25 0, .triangle 31 2, .triangle 33 0, .triangle 34 2, .triangle 23 0, .triangle 22 0, .corridorLower 4 5, .thetaNext 3, .thetaNext 2]

-- Cycle fingerprint d94d28875616203c94160cf1996b126691ec5454cafb6f6c291d85eee997b504.
def localCycle00081 : Cycle where
  length := 9
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 2, .distance 0 3, .distance 0 4, .distance 4 5, .distance 3 4, .distance 2 3, .distance 1 2, .theta 1]
    constant := ![3, 0, 0, 0, -1, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, false, false, false, false] }
  origin := ![.corridorUpper 0 1, .triangle 0 2, .triangle 5 2, .triangle 9 2, .triangle 12 0, .triangle 31 0, .triangle 25 0, .triangle 15 0, .corridorLower 1 2]

-- Cycle fingerprint dcd86614b1d14e54b54394be470c8c0fa80af9b8716843ec8d8f0752f305e0a8.
def localCycle00082 : Cycle where
  length := 11
  data := {
    node := ![.theta 4, .distance 0 4, .distance 4 5, .distance 3 5, .distance 2 3, .distance 3 4, .distance 1 3, .distance 3 6, .distance 4 6, .distance 5 6, .theta 5, .theta 4]
    constant := ![3, -1, 0, -1, -1, -1, -1, 0, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, true, true, false, true] }
  origin := ![.corridorUpper 0 4, .triangle 12 0, .triangle 31 2, .triangle 26 0, .triangle 25 0, .triangle 19 0, .triangle 21 0, .triangle 32 1, .triangle 34 1, .corridorLower 5 6, .thetaNext 4]

-- Cycle fingerprint de02077c578024675e17a5810e1c4de5eb114602c9016f3a77346bdd5f5c2da9.
def localCycle00083 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 0 2, .distance 2 3, .distance 3 4, .distance 3 5, .distance 5 6, .distance 4 5, .theta 4, .theta 3, .theta 2]
    constant := ![3, -1, -1, 0, -1, -1, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, true, true] }
  origin := ![.corridorUpper 0 2, .triangle 5 0, .triangle 25 0, .triangle 31 2, .triangle 33 0, .triangle 34 0, .corridorLower 4 5, .thetaNext 3, .thetaNext 2]

-- Cycle fingerprint de522d8b99d23f7e7aa75515bd23c3db88aa0b35685706f74fa13d336925ce68.
def localCycle00084 : Cycle where
  length := 11
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 2 3, .distance 2 4, .distance 2 5, .distance 5 6, .distance 4 5, .distance 3 4, .distance 1 3, .distance 1 2, .theta 1, .distance 0 1]
    constant := ![0, -1, 0, 0, -1, -1, -1, -1, 0, -1, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![true, false, true, true, false, false, false, false, false, false, false] }
  origin := ![.triangle 0 2, .triangle 5 0, .triangle 25 2, .triangle 28 2, .triangle 30 0, .triangle 34 0, .triangle 31 0, .triangle 19 0, .gapLower 1 1, .corridorLower 1 2, .corridorUpper 0 1]

-- Cycle fingerprint de6a8d3dde41fb3c242e1d6eb8c7b59d99e07d88bbb37008a55833263962581b.
def localCycle00085 : Cycle where
  length := 10
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 2, .distance 0 3, .distance 3 4, .distance 3 5, .distance 5 6, .distance 2 5, .distance 2 3, .distance 1 2, .theta 1]
    constant := ![3, 0, 0, -1, 0, -1, -1, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, false, false, false, false] }
  origin := ![.corridorUpper 0 1, .triangle 0 2, .triangle 5 2, .triangle 9 0, .triangle 31 2, .triangle 33 0, .triangle 30 0, .gapLower 2 2, .triangle 15 0, .corridorLower 1 2]

-- Cycle fingerprint dfaad23570aebbdead22231a3767603680b31edd85ee5e1fae45133c1bd5d570.
def localCycle00086 : Cycle where
  length := 11
  data := {
    node := ![.distance 0 4, .distance 4 5, .distance 3 4, .distance 2 4, .distance 4 6, .distance 1 4, .distance 1 3, .theta 1, .distance 0 1, .distance 0 2, .distance 0 3, .distance 0 4]
    constant := ![-1, -1, 0, -1, -1, 0, -1, 3, 0, 0, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false, true, true, true] }
  origin := ![.triangle 12 0, .triangle 31 0, .triangle 25 2, .triangle 29 0, .triangle 23 0, .gapLower 1 2, .corridorLower 1 3, .corridorUpper 0 1, .triangle 0 2, .triangle 5 2, .triangle 9 2]

-- Cycle fingerprint e1bbc7b5f2facdf3c627a879944bb9c770ce725b2cf5f4829f41800ec6c78c80.
def localCycle00087 : Cycle where
  length := 14
  data := {
    node := ![.distance 4 5, .distance 1 4, .distance 1 3, .theta 1, .distance 0 1, .distance 0 2, .distance 0 3, .distance 0 4, .distance 0 5, .distance 5 6, .distance 4 6, .distance 3 4, .distance 2 3, .distance 3 5, .distance 4 5]
    constant := ![-1, 0, -1, 3, 0, 0, 0, 0, -1, 0, -1, -1, -1, 0]
    coefficient := ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, true, true, false, true, false, false, false, true] }
  origin := ![.triangle 22 0, .gapLower 1 2, .corridorLower 1 3, .corridorUpper 0 1, .triangle 0 2, .triangle 5 2, .triangle 9 2, .triangle 12 2, .triangle 14 0, .triangle 34 2, .triangle 32 0, .triangle 25 0, .triangle 26 0, .triangle 31 1]

-- Cycle fingerprint e4b2326a0487e9c351986dc7f1ad8e858227e59bcadd76d344cdc185b4d58ba7.
def localCycle00088 : Cycle where
  length := 15
  data := {
    node := ![.distance 1 4, .distance 1 3, .distance 1 2, .theta 1, .distance 0 1, .distance 0 2, .distance 0 3, .distance 0 4, .distance 4 5, .distance 3 4, .distance 2 3, .distance 3 6, .distance 4 6, .distance 5 6, .distance 1 5, .distance 1 4]
    constant := ![0, 0, -1, 3, 0, 0, 0, -1, -1, -1, -1, 0, 0, -1, 0]
    coefficient := ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, true, false, false, false, false, true, true, false, false] }
  origin := ![.gapLower 1 2, .gapLower 1 1, .corridorLower 1 2, .corridorUpper 0 1, .triangle 0 2, .triangle 5 2, .triangle 9 2, .triangle 12 0, .triangle 31 0, .triangle 25 0, .triangle 27 0, .triangle 32 1, .triangle 34 1, .triangle 24 0, .gapLower 1 3]

-- Cycle fingerprint e66d5de1c2672467a85fd99c9a51ba42d1eed2b85f542556a0fcceab36d8a2ef.
def localCycle00089 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 0 3, .distance 3 4, .distance 1 4, .distance 1 5, .distance 5 6, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, -1, 0, 0, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, true] }
  origin := ![.corridorUpper 0 3, .triangle 9 0, .triangle 19 2, .triangle 22 2, .triangle 24 0, .triangle 34 0, .corridorLower 4 5, .thetaNext 3]

-- Cycle fingerprint e86b1a28e313f791dbab201c04b4ce276ea1950234585f5ddb4c0e641d902ab5.
def localCycle00090 : Cycle where
  length := 11
  data := {
    node := ![.distance 0 2, .distance 0 3, .distance 3 4, .distance 4 5, .distance 2 4, .distance 4 6, .distance 5 6, .distance 1 5, .distance 1 4, .theta 1, .distance 0 1, .distance 0 2]
    constant := ![0, -1, -1, -1, -1, 0, -1, 0, -1, 3, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0]
    strict := ![true, false, false, false, false, true, false, false, false, false, true] }
  origin := ![.triangle 5 2, .triangle 9 0, .triangle 31 0, .triangle 28 0, .triangle 29 0, .triangle 34 1, .triangle 24 0, .gapLower 1 3, .corridorLower 1 4, .corridorUpper 0 1, .triangle 0 2]

-- Cycle fingerprint eed1d675936cedbeb1e9cabbaed77dcbab92b830eb4a3a4d2f58aedc478fb309.
def localCycle00091 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 2, .distance 2 3, .distance 3 5, .distance 5 6, .distance 1 5, .distance 1 4, .theta 1, .distance 0 1, .distance 0 2]
    constant := ![-1, -1, -1, -1, 0, -1, 3, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 0]
    strict := ![false, false, false, false, false, false, false, true] }
  origin := ![.triangle 5 0, .triangle 26 0, .triangle 33 0, .triangle 24 0, .gapLower 1 3, .corridorLower 1 4, .corridorUpper 0 1, .triangle 0 2]

-- Cycle fingerprint ef153ec2995bbc3b652fa4598d0edeb12d26537521fc5886396ed27dbf64f2be.
def localCycle00092 : Cycle where
  length := 12
  data := {
    node := ![.distance 0 2, .distance 0 3, .distance 0 4, .distance 4 5, .distance 5 6, .distance 3 5, .distance 2 3, .distance 3 4, .distance 1 3, .distance 1 2, .theta 1, .distance 0 1, .distance 0 2]
    constant := ![0, 0, -1, -1, -1, -1, -1, -1, 0, -1, 3, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0]
    strict := ![true, true, false, false, false, false, false, false, false, false, false, true] }
  origin := ![.triangle 5 2, .triangle 9 2, .triangle 12 0, .triangle 34 0, .triangle 33 0, .triangle 26 0, .triangle 25 0, .triangle 19 0, .gapLower 1 1, .corridorLower 1 2, .corridorUpper 0 1, .triangle 0 2]

-- Cycle fingerprint ef8e740b1bda51a45f0cace9e0a27740962b1cc76cf63f357e4ba1ce40759c61.
def localCycle00093 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 3, .theta 3, .theta 2, .distance 0 2, .distance 2 3, .distance 2 4, .distance 4 5, .distance 3 4, .distance 4 6, .distance 1 4, .distance 1 3]
    constant := ![0, 0, 3, -1, 0, -1, -1, -1, -1, 0]
    coefficient := ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, false, false, false, false, false] }
  origin := ![.gapLower 3 0, .thetaNext 2, .corridorUpper 0 2, .triangle 5 0, .triangle 25 2, .triangle 28 0, .triangle 31 0, .triangle 32 0, .triangle 23 0, .gapLower 1 2]

-- Cycle fingerprint f29e550e5f01e7bd646237c76514337e1d060009ca6bd9302b2c1bd366264ce6.
def localCycle00094 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 0 3, .distance 3 4, .distance 1 4, .distance 4 5, .distance 5 6, .theta 5, .theta 4, .theta 3]
    constant := ![3, -1, 0, -1, -1, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, true, true] }
  origin := ![.corridorUpper 0 3, .triangle 9 0, .triangle 19 2, .triangle 22 0, .triangle 34 0, .corridorLower 5 6, .thetaNext 4, .thetaNext 3]

-- Cycle fingerprint f2e74995b7666293d97e8ac057b098ef62a93da1d4762b73300e6cda93f1c105.
def localCycle00095 : Cycle where
  length := 10
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 2, .distance 2 3, .distance 2 4, .distance 4 5, .distance 3 5, .distance 5 6, .distance 1 5, .distance 1 4, .theta 1]
    constant := ![3, 0, -1, 0, -1, 0, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, true, false, false, false, false] }
  origin := ![.corridorUpper 0 1, .triangle 0 2, .triangle 5 0, .triangle 25 2, .triangle 28 0, .triangle 31 2, .triangle 33 0, .triangle 24 0, .gapLower 1 3, .corridorLower 1 4]

-- Cycle fingerprint f2f0c214a4e2cc7ac800dbcc9759b3f7dd15366ee80e7c216c075c0bbd4ef002.
def localCycle00096 : Cycle where
  length := 11
  data := {
    node := ![.distance 0 2, .distance 0 3, .distance 0 4, .distance 4 5, .distance 3 4, .distance 2 3, .distance 3 6, .distance 1 3, .distance 1 2, .theta 1, .distance 0 1, .distance 0 2]
    constant := ![0, 0, -1, -1, -1, -1, -1, 0, -1, 3, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0]
    strict := ![true, true, false, false, false, false, false, false, false, false, true] }
  origin := ![.triangle 5 2, .triangle 9 2, .triangle 12 0, .triangle 31 0, .triangle 25 0, .triangle 27 0, .triangle 21 0, .gapLower 1 1, .corridorLower 1 2, .corridorUpper 0 1, .triangle 0 2]

-- Cycle fingerprint f461262d6fbff587dbcbf8e95dc4bc23be9af4d38f257d405471d3ad6e372d0e.
def localCycle00097 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 0 3, .distance 3 4, .distance 1 3, .distance 3 6, .distance 4 6, .distance 5 6, .theta 5, .theta 4, .theta 3]
    constant := ![3, -1, -1, -1, 0, 0, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, false, true, true] }
  origin := ![.corridorUpper 0 3, .triangle 9 0, .triangle 19 0, .triangle 21 0, .triangle 32 1, .triangle 34 1, .corridorLower 5 6, .thetaNext 4, .thetaNext 3]

-- Cycle fingerprint f65151e81d431b83f706835a3b5f0ce35819bf427ce4cf3ef2972be0c8bb1b9e.
def localCycle00098 : Cycle where
  length := 13
  data := {
    node := ![.distance 2 3, .distance 3 6, .distance 4 6, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1, .distance 0 1, .distance 0 2, .distance 0 3, .distance 0 4, .distance 4 5, .distance 3 4, .distance 2 3]
    constant := ![-1, 0, -1, 0, 0, -1, 3, 0, 0, 0, -1, -1, -1]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false, true, true, true, false, false, false] }
  origin := ![.triangle 27 0, .triangle 32 1, .triangle 23 0, .gapLower 1 2, .gapLower 1 1, .corridorLower 1 2, .corridorUpper 0 1, .triangle 0 2, .triangle 5 2, .triangle 9 2, .triangle 12 0, .triangle 31 0, .triangle 25 0]

-- Cycle fingerprint fff145f7ba21adb96742fae0c025ce859140fe5b2792876e48f2d4ba8acb43c5.
def localCycle00099 : Cycle where
  length := 9
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 2, .distance 2 3, .distance 2 4, .distance 2 5, .distance 5 6, .distance 3 5, .distance 1 3, .theta 1]
    constant := ![3, 0, -1, 0, 0, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, true, false, false, false, false] }
  origin := ![.corridorUpper 0 1, .triangle 0 2, .triangle 5 0, .triangle 25 2, .triangle 28 2, .triangle 30 0, .triangle 33 0, .triangle 20 0, .corridorLower 1 3]

def library : Library := fun id => if id < 50 then (if id < 25 then (if id < 12 then (if id < 6 then (if id < 3 then (if id < 1 then (if id = 0 then some localCycle00000 else none) else (if id < 2 then (if id = 1 then some localCycle00001 else none) else (if id = 2 then some localCycle00002 else none))) else (if id < 4 then (if id = 3 then some localCycle00003 else none) else (if id < 5 then (if id = 4 then some localCycle00004 else none) else (if id = 5 then some localCycle00005 else none)))) else (if id < 9 then (if id < 7 then (if id = 6 then some localCycle00006 else none) else (if id < 8 then (if id = 7 then some localCycle00007 else none) else (if id = 8 then some localCycle00008 else none))) else (if id < 10 then (if id = 9 then some localCycle00009 else none) else (if id < 11 then (if id = 10 then some localCycle00010 else none) else (if id = 11 then some localCycle00011 else none))))) else (if id < 18 then (if id < 15 then (if id < 13 then (if id = 12 then some localCycle00012 else none) else (if id < 14 then (if id = 13 then some localCycle00013 else none) else (if id = 14 then some localCycle00014 else none))) else (if id < 16 then (if id = 15 then some localCycle00015 else none) else (if id < 17 then (if id = 16 then some localCycle00016 else none) else (if id = 17 then some localCycle00017 else none)))) else (if id < 21 then (if id < 19 then (if id = 18 then some localCycle00018 else none) else (if id < 20 then (if id = 19 then some localCycle00019 else none) else (if id = 20 then some localCycle00020 else none))) else (if id < 23 then (if id < 22 then (if id = 21 then some localCycle00021 else none) else (if id = 22 then some localCycle00022 else none)) else (if id < 24 then (if id = 23 then some localCycle00023 else none) else (if id = 24 then some localCycle00024 else none)))))) else (if id < 37 then (if id < 31 then (if id < 28 then (if id < 26 then (if id = 25 then some localCycle00025 else none) else (if id < 27 then (if id = 26 then some localCycle00026 else none) else (if id = 27 then some localCycle00027 else none))) else (if id < 29 then (if id = 28 then some localCycle00028 else none) else (if id < 30 then (if id = 29 then some localCycle00029 else none) else (if id = 30 then some localCycle00030 else none)))) else (if id < 34 then (if id < 32 then (if id = 31 then some localCycle00031 else none) else (if id < 33 then (if id = 32 then some localCycle00032 else none) else (if id = 33 then some localCycle00033 else none))) else (if id < 35 then (if id = 34 then some localCycle00034 else none) else (if id < 36 then (if id = 35 then some localCycle00035 else none) else (if id = 36 then some localCycle00036 else none))))) else (if id < 43 then (if id < 40 then (if id < 38 then (if id = 37 then some localCycle00037 else none) else (if id < 39 then (if id = 38 then some localCycle00038 else none) else (if id = 39 then some localCycle00039 else none))) else (if id < 41 then (if id = 40 then some localCycle00040 else none) else (if id < 42 then (if id = 41 then some localCycle00041 else none) else (if id = 42 then some localCycle00042 else none)))) else (if id < 46 then (if id < 44 then (if id = 43 then some localCycle00043 else none) else (if id < 45 then (if id = 44 then some localCycle00044 else none) else (if id = 45 then some localCycle00045 else none))) else (if id < 48 then (if id < 47 then (if id = 46 then some localCycle00046 else none) else (if id = 47 then some localCycle00047 else none)) else (if id < 49 then (if id = 48 then some localCycle00048 else none) else (if id = 49 then some localCycle00049 else none))))))) else (if id < 75 then (if id < 62 then (if id < 56 then (if id < 53 then (if id < 51 then (if id = 50 then some localCycle00050 else none) else (if id < 52 then (if id = 51 then some localCycle00051 else none) else (if id = 52 then some localCycle00052 else none))) else (if id < 54 then (if id = 53 then some localCycle00053 else none) else (if id < 55 then (if id = 54 then some localCycle00054 else none) else (if id = 55 then some localCycle00055 else none)))) else (if id < 59 then (if id < 57 then (if id = 56 then some localCycle00056 else none) else (if id < 58 then (if id = 57 then some localCycle00057 else none) else (if id = 58 then some localCycle00058 else none))) else (if id < 60 then (if id = 59 then some localCycle00059 else none) else (if id < 61 then (if id = 60 then some localCycle00060 else none) else (if id = 61 then some localCycle00061 else none))))) else (if id < 68 then (if id < 65 then (if id < 63 then (if id = 62 then some localCycle00062 else none) else (if id < 64 then (if id = 63 then some localCycle00063 else none) else (if id = 64 then some localCycle00064 else none))) else (if id < 66 then (if id = 65 then some localCycle00065 else none) else (if id < 67 then (if id = 66 then some localCycle00066 else none) else (if id = 67 then some localCycle00067 else none)))) else (if id < 71 then (if id < 69 then (if id = 68 then some localCycle00068 else none) else (if id < 70 then (if id = 69 then some localCycle00069 else none) else (if id = 70 then some localCycle00070 else none))) else (if id < 73 then (if id < 72 then (if id = 71 then some localCycle00071 else none) else (if id = 72 then some localCycle00072 else none)) else (if id < 74 then (if id = 73 then some localCycle00073 else none) else (if id = 74 then some localCycle00074 else none)))))) else (if id < 87 then (if id < 81 then (if id < 78 then (if id < 76 then (if id = 75 then some localCycle00075 else none) else (if id < 77 then (if id = 76 then some localCycle00076 else none) else (if id = 77 then some localCycle00077 else none))) else (if id < 79 then (if id = 78 then some localCycle00078 else none) else (if id < 80 then (if id = 79 then some localCycle00079 else none) else (if id = 80 then some localCycle00080 else none)))) else (if id < 84 then (if id < 82 then (if id = 81 then some localCycle00081 else none) else (if id < 83 then (if id = 82 then some localCycle00082 else none) else (if id = 83 then some localCycle00083 else none))) else (if id < 85 then (if id = 84 then some localCycle00084 else none) else (if id < 86 then (if id = 85 then some localCycle00085 else none) else (if id = 86 then some localCycle00086 else none))))) else (if id < 93 then (if id < 90 then (if id < 88 then (if id = 87 then some localCycle00087 else none) else (if id < 89 then (if id = 88 then some localCycle00088 else none) else (if id = 89 then some localCycle00089 else none))) else (if id < 91 then (if id = 90 then some localCycle00090 else none) else (if id < 92 then (if id = 91 then some localCycle00091 else none) else (if id = 92 then some localCycle00092 else none)))) else (if id < 96 then (if id < 94 then (if id = 93 then some localCycle00093 else none) else (if id < 95 then (if id = 94 then some localCycle00094 else none) else (if id = 95 then some localCycle00095 else none))) else (if id < 98 then (if id < 97 then (if id = 96 then some localCycle00096 else none) else (if id = 97 then some localCycle00097 else none)) else (if id < 99 then (if id = 98 then some localCycle00098 else none) else (if id = 99 then some localCycle00099 else none)))))))

def namedLeaf000 : LeafData := { rows := ![![6, 5, 4, 3, 2, 1], ![2, 3, 4, 5, 6, 0], ![1, 3, 6, 5, 4, 0], ![1, 2, 6, 5, 4, 0], ![1, 5, 6, 2, 3, 0], ![1, 4, 6, 2, 3, 0], ![1, 4, 5, 2, 3, 0]], proof := .tail 10 }

theorem namedLeaf000_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23808)) namedLeaf000 = true :=
  by decide +kernel

def namedLeaf001 : LeafData := { rows := ![![6, 5, 4, 3, 2, 1], ![2, 3, 4, 5, 6, 0], ![1, 3, 6, 5, 4, 0], ![1, 2, 6, 5, 4, 0], ![1, 6, 5, 2, 3, 0], ![1, 6, 4, 2, 3, 0], ![1, 5, 4, 2, 3, 0]], proof := .tail 15 }

theorem namedLeaf001_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23809)) namedLeaf001 = true :=
  by decide +kernel

def namedLeaf002 : LeafData := { rows := ![![6, 5, 4, 3, 2, 1], ![2, 3, 4, 5, 6, 0], ![1, 6, 3, 4, 5, 0], ![1, 6, 2, 4, 5, 0], ![1, 6, 2, 3, 5, 0], ![1, 6, 2, 3, 4, 0], ![1, 5, 4, 3, 2, 0]], proof := .tail 88 }

theorem namedLeaf002_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23810)) namedLeaf002 = true :=
  by decide +kernel

def namedLeaf003 : LeafData := { rows := ![![6, 5, 4, 3, 2, 1], ![2, 3, 4, 5, 6, 0], ![1, 6, 3, 4, 5, 0], ![1, 6, 2, 5, 4, 0], ![1, 6, 2, 5, 3, 0], ![1, 6, 2, 4, 3, 0], ![1, 5, 4, 3, 2, 0]], proof := .tail 90 }

theorem namedLeaf003_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23811)) namedLeaf003 = true :=
  by decide +kernel

def namedLeaf004 : LeafData := { rows := ![![6, 5, 4, 3, 2, 1], ![2, 3, 4, 5, 6, 0], ![1, 6, 3, 5, 4, 0], ![1, 6, 2, 5, 4, 0], ![1, 5, 6, 2, 3, 0], ![1, 4, 6, 2, 3, 0], ![1, 4, 5, 3, 2, 0]], proof := .tail 75 }

theorem namedLeaf004_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23812)) namedLeaf004 = true :=
  by decide +kernel

def namedLeaf005 : LeafData := { rows := ![![6, 5, 4, 3, 2, 1], ![2, 3, 4, 5, 6, 0], ![1, 6, 3, 5, 4, 0], ![1, 6, 2, 5, 4, 0], ![1, 6, 5, 2, 3, 0], ![1, 6, 4, 2, 3, 0], ![1, 5, 4, 3, 2, 0]], proof := .tail 19 }

theorem namedLeaf005_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23813)) namedLeaf005 = true :=
  by decide +kernel

def namedLeaf006 : LeafData := { rows := ![![6, 5, 4, 3, 2, 1], ![2, 3, 4, 5, 6, 0], ![1, 5, 3, 4, 6, 0], ![1, 5, 2, 4, 6, 0], ![1, 5, 2, 3, 6, 0], ![1, 4, 3, 2, 6, 0], ![1, 2, 3, 4, 5, 0]], proof := .tail 87 }

theorem namedLeaf006_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23814)) namedLeaf006 = true :=
  by decide +kernel

def namedLeaf007 : LeafData := { rows := ![![6, 5, 4, 3, 2, 1], ![2, 3, 4, 5, 6, 0], ![1, 5, 3, 4, 6, 0], ![1, 5, 2, 6, 4, 0], ![1, 5, 2, 6, 3, 0], ![1, 4, 3, 2, 6, 0], ![1, 2, 4, 3, 5, 0]], proof := .tail 72 }

theorem namedLeaf007_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23815)) namedLeaf007 = true :=
  by decide +kernel

def namedLeaf008 : LeafData := { rows := ![![6, 5, 4, 3, 2, 1], ![2, 3, 4, 5, 6, 0], ![1, 5, 3, 6, 4, 0], ![1, 5, 2, 6, 4, 0], ![1, 5, 6, 2, 3, 0], ![1, 4, 3, 2, 6, 0], ![1, 4, 2, 3, 5, 0]], proof := .tail 53 }

theorem namedLeaf008_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23816)) namedLeaf008 = true :=
  by decide +kernel

def namedLeaf009 : LeafData := { rows := ![![6, 5, 4, 3, 2, 1], ![2, 3, 4, 5, 6, 0], ![1, 5, 6, 3, 4, 0], ![1, 5, 6, 2, 4, 0], ![1, 5, 6, 2, 3, 0], ![1, 4, 3, 2, 6, 0], ![1, 4, 3, 2, 5, 0]], proof := .tail 25 }

theorem namedLeaf009_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23817)) namedLeaf009 = true :=
  by decide +kernel

def namedLeaf010 : LeafData := { rows := ![![6, 5, 4, 3, 2, 1], ![2, 3, 4, 5, 6, 0], ![1, 6, 5, 3, 4, 0], ![1, 5, 6, 2, 4, 0], ![1, 5, 6, 2, 3, 0], ![1, 4, 3, 6, 2, 0], ![1, 4, 3, 5, 2, 0]], proof := .tail 65 }

theorem namedLeaf010_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23818)) namedLeaf010 = true :=
  by decide +kernel

def namedLeaf011 : LeafData := { rows := ![![6, 5, 4, 3, 2, 1], ![2, 3, 4, 5, 6, 0], ![1, 6, 5, 3, 4, 0], ![1, 6, 5, 2, 4, 0], ![1, 5, 6, 2, 3, 0], ![1, 4, 6, 3, 2, 0], ![1, 4, 5, 3, 2, 0]], proof := .tail 18 }

theorem namedLeaf011_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23819)) namedLeaf011 = true :=
  by decide +kernel

def namedLeaf012 : LeafData := { rows := ![![6, 5, 4, 3, 2, 1], ![2, 3, 4, 5, 6, 0], ![1, 6, 5, 3, 4, 0], ![1, 6, 5, 2, 4, 0], ![1, 6, 5, 2, 3, 0], ![1, 6, 4, 3, 2, 0], ![1, 5, 4, 3, 2, 0]], proof := .tail 27 }

theorem namedLeaf012_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23820)) namedLeaf012 = true :=
  by decide +kernel

def namedLeaf013 : LeafData := { rows := ![![6, 5, 4, 3, 2, 1], ![2, 3, 4, 5, 6, 0], ![1, 4, 3, 5, 6, 0], ![1, 4, 2, 5, 6, 0], ![1, 3, 2, 5, 6, 0], ![1, 2, 3, 4, 6, 0], ![1, 2, 3, 4, 5, 0]], proof := .tail 40 }

theorem namedLeaf013_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23821)) namedLeaf013 = true :=
  by decide +kernel

def namedLeaf014 : LeafData := { rows := ![![6, 5, 4, 3, 2, 1], ![2, 3, 4, 5, 6, 0], ![1, 4, 3, 5, 6, 0], ![1, 4, 2, 5, 6, 0], ![1, 3, 2, 6, 5, 0], ![1, 2, 3, 6, 4, 0], ![1, 2, 3, 5, 4, 0]], proof := .tail 92 }

theorem namedLeaf014_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23822)) namedLeaf014 = true :=
  by decide +kernel

def namedLeaf015 : LeafData := { rows := ![![6, 5, 4, 3, 2, 1], ![2, 3, 4, 5, 6, 0], ![1, 4, 3, 5, 6, 0], ![1, 4, 2, 6, 5, 0], ![1, 3, 2, 6, 5, 0], ![1, 2, 6, 3, 4, 0], ![1, 2, 5, 3, 4, 0]], proof := .tail 7 }

theorem namedLeaf015_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23823)) namedLeaf015 = true :=
  by decide +kernel

def namedLeaf016 : LeafData := { rows := ![![6, 5, 4, 3, 2, 1], ![2, 3, 4, 5, 6, 0], ![1, 4, 3, 6, 5, 0], ![1, 4, 2, 6, 5, 0], ![1, 3, 2, 6, 5, 0], ![1, 6, 2, 3, 4, 0], ![1, 5, 2, 3, 4, 0]], proof := .tail 37 }

theorem namedLeaf016_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23824)) namedLeaf016 = true :=
  by decide +kernel

def namedLeaf017 : LeafData := { rows := ![![6, 5, 4, 3, 2, 1], ![2, 3, 4, 5, 6, 0], ![1, 4, 6, 3, 5, 0], ![1, 4, 6, 2, 5, 0], ![1, 3, 2, 6, 5, 0], ![1, 6, 2, 3, 4, 0], ![1, 5, 3, 2, 4, 0]], proof := .tail 14 }

theorem namedLeaf017_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23825)) namedLeaf017 = true :=
  by decide +kernel

def namedLeaf018 : LeafData := { rows := ![![6, 5, 4, 3, 2, 1], ![2, 3, 4, 5, 6, 0], ![1, 6, 4, 3, 5, 0], ![1, 4, 6, 2, 5, 0], ![1, 3, 6, 2, 5, 0], ![1, 6, 2, 3, 4, 0], ![1, 5, 3, 4, 2, 0]], proof := .tail 2 }

theorem namedLeaf018_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23826)) namedLeaf018 = true :=
  by decide +kernel

def namedLeaf019 : LeafData := { rows := ![![6, 5, 4, 3, 2, 1], ![2, 3, 4, 5, 6, 0], ![1, 6, 4, 3, 5, 0], ![1, 6, 4, 2, 5, 0], ![1, 6, 3, 2, 5, 0], ![1, 6, 2, 3, 4, 0], ![1, 5, 4, 3, 2, 0]], proof := .tail 45 }

theorem namedLeaf019_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23827)) namedLeaf019 = true :=
  by decide +kernel

def namedLeaf020 : LeafData := { rows := ![![6, 5, 4, 3, 2, 1], ![2, 3, 4, 5, 6, 0], ![1, 4, 5, 3, 6, 0], ![1, 4, 5, 2, 6, 0], ![1, 3, 2, 5, 6, 0], ![1, 3, 2, 4, 6, 0], ![1, 2, 3, 4, 5, 0]], proof := .tail 48 }

theorem namedLeaf020_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23828)) namedLeaf020 = true :=
  by decide +kernel

def namedLeaf021 : LeafData := { rows := ![![6, 5, 4, 3, 2, 1], ![2, 3, 4, 5, 6, 0], ![1, 4, 5, 3, 6, 0], ![1, 4, 5, 2, 6, 0], ![1, 3, 2, 6, 5, 0], ![1, 3, 2, 6, 4, 0], ![1, 2, 3, 5, 4, 0]], proof := .tail 46 }

theorem namedLeaf021_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23829)) namedLeaf021 = true :=
  by decide +kernel

def namedLeaf022 : LeafData := { rows := ![![6, 5, 4, 3, 2, 1], ![2, 3, 4, 5, 6, 0], ![1, 5, 4, 3, 6, 0], ![1, 4, 5, 2, 6, 0], ![1, 3, 5, 2, 6, 0], ![1, 3, 4, 2, 6, 0], ![1, 2, 3, 4, 5, 0]], proof := .tail 31 }

theorem namedLeaf022_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23830)) namedLeaf022 = true :=
  by decide +kernel

def namedLeaf023 : LeafData := { rows := ![![6, 5, 4, 3, 2, 1], ![2, 3, 4, 5, 6, 0], ![1, 5, 4, 3, 6, 0], ![1, 5, 4, 2, 6, 0], ![1, 5, 3, 2, 6, 0], ![1, 4, 3, 2, 6, 0], ![1, 2, 3, 4, 5, 0]], proof := .tail 12 }

theorem namedLeaf023_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23831)) namedLeaf023 = true :=
  by decide +kernel

def namedLeaf024 : LeafData := { rows := ![![6, 5, 4, 3, 2, 1], ![2, 3, 4, 5, 6, 0], ![1, 4, 5, 6, 3, 0], ![1, 4, 5, 6, 2, 0], ![1, 3, 2, 5, 6, 0], ![1, 3, 2, 4, 6, 0], ![1, 3, 2, 4, 5, 0]], proof := .tail 48 }

theorem namedLeaf024_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23832)) namedLeaf024 = true :=
  by decide +kernel

def namedLeaf025 : LeafData := { rows := ![![6, 5, 4, 3, 2, 1], ![2, 3, 4, 5, 6, 0], ![1, 4, 5, 6, 3, 0], ![1, 4, 5, 6, 2, 0], ![1, 3, 2, 6, 5, 0], ![1, 3, 2, 6, 4, 0], ![1, 3, 2, 5, 4, 0]], proof := .tail 57 }

theorem namedLeaf025_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23833)) namedLeaf025 = true :=
  by decide +kernel

def namedLeaf026 : LeafData := { rows := ![![6, 5, 4, 3, 2, 1], ![2, 3, 4, 5, 6, 0], ![1, 4, 6, 5, 3, 0], ![1, 4, 5, 6, 2, 0], ![1, 3, 2, 6, 5, 0], ![1, 3, 6, 2, 4, 0], ![1, 3, 5, 2, 4, 0]], proof := .tail 49 }

theorem namedLeaf026_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23834)) namedLeaf026 = true :=
  by decide +kernel

def namedLeaf027 : LeafData := { rows := ![![6, 5, 4, 3, 2, 1], ![2, 3, 4, 5, 6, 0], ![1, 4, 6, 5, 3, 0], ![1, 4, 6, 5, 2, 0], ![1, 3, 2, 6, 5, 0], ![1, 6, 3, 2, 4, 0], ![1, 5, 3, 2, 4, 0]], proof := .tail 91 }

theorem namedLeaf027_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23835)) namedLeaf027 = true :=
  by decide +kernel

def namedLeaf028 : LeafData := { rows := ![![6, 5, 4, 3, 2, 1], ![2, 3, 4, 5, 6, 0], ![1, 6, 4, 5, 3, 0], ![1, 4, 5, 6, 2, 0], ![1, 3, 6, 2, 5, 0], ![1, 3, 6, 2, 4, 0], ![1, 3, 5, 4, 2, 0]], proof := .tail 2 }

theorem namedLeaf028_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23836)) namedLeaf028 = true :=
  by decide +kernel

def namedLeaf029 : LeafData := { rows := ![![6, 5, 4, 3, 2, 1], ![2, 3, 4, 5, 6, 0], ![1, 6, 4, 5, 3, 0], ![1, 4, 6, 5, 2, 0], ![1, 3, 6, 2, 5, 0], ![1, 6, 3, 2, 4, 0], ![1, 5, 3, 4, 2, 0]], proof := .tail 2 }

theorem namedLeaf029_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23837)) namedLeaf029 = true :=
  by decide +kernel

def namedLeaf030 : LeafData := { rows := ![![6, 5, 4, 3, 2, 1], ![2, 3, 4, 5, 6, 0], ![1, 6, 4, 5, 3, 0], ![1, 6, 4, 5, 2, 0], ![1, 6, 3, 2, 5, 0], ![1, 6, 3, 2, 4, 0], ![1, 5, 4, 3, 2, 0]], proof := .tail 45 }

theorem namedLeaf030_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23838)) namedLeaf030 = true :=
  by decide +kernel

def namedLeaf031 : LeafData := { rows := ![![6, 5, 4, 3, 2, 1], ![2, 3, 4, 5, 6, 0], ![1, 5, 4, 6, 3, 0], ![1, 4, 5, 6, 2, 0], ![1, 3, 5, 2, 6, 0], ![1, 3, 4, 2, 6, 0], ![1, 3, 2, 4, 5, 0]], proof := .tail 31 }

theorem namedLeaf031_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23839)) namedLeaf031 = true :=
  by decide +kernel

def namedLeaf032 : LeafData := { rows := ![![6, 5, 4, 3, 2, 1], ![2, 3, 4, 5, 6, 0], ![1, 5, 4, 6, 3, 0], ![1, 5, 4, 6, 2, 0], ![1, 5, 3, 2, 6, 0], ![1, 4, 3, 2, 6, 0], ![1, 3, 2, 4, 5, 0]], proof := .tail 12 }

theorem namedLeaf032_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23840)) namedLeaf032 = true :=
  by decide +kernel

def namedLeaf033 : LeafData := { rows := ![![6, 5, 4, 3, 2, 1], ![2, 3, 4, 5, 6, 0], ![1, 5, 6, 4, 3, 0], ![1, 4, 5, 6, 2, 0], ![1, 3, 5, 6, 2, 0], ![1, 3, 4, 2, 6, 0], ![1, 3, 4, 2, 5, 0]], proof := .tail 13 }

theorem namedLeaf033_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23841)) namedLeaf033 = true :=
  by decide +kernel

def namedLeaf034 : LeafData := { rows := ![![6, 5, 4, 3, 2, 1], ![2, 3, 4, 5, 6, 0], ![1, 5, 6, 4, 3, 0], ![1, 5, 4, 6, 2, 0], ![1, 5, 3, 6, 2, 0], ![1, 4, 3, 2, 6, 0], ![1, 3, 4, 2, 5, 0]], proof := .tail 34 }

theorem namedLeaf034_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23842)) namedLeaf034 = true :=
  by decide +kernel

def namedLeaf035 : LeafData := { rows := ![![6, 5, 4, 3, 2, 1], ![2, 3, 4, 5, 6, 0], ![1, 5, 6, 4, 3, 0], ![1, 5, 6, 4, 2, 0], ![1, 5, 6, 3, 2, 0], ![1, 4, 3, 2, 6, 0], ![1, 4, 3, 2, 5, 0]], proof := .tail 68 }

theorem namedLeaf035_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23843)) namedLeaf035 = true :=
  by decide +kernel

def namedLeaf036 : LeafData := { rows := ![![6, 5, 4, 3, 2, 1], ![2, 3, 4, 5, 6, 0], ![1, 6, 5, 4, 3, 0], ![1, 4, 5, 6, 2, 0], ![1, 3, 5, 6, 2, 0], ![1, 3, 4, 6, 2, 0], ![1, 3, 4, 5, 2, 0]], proof := .tail 84 }

theorem namedLeaf036_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23844)) namedLeaf036 = true :=
  by decide +kernel

def namedLeaf037 : LeafData := { rows := ![![6, 5, 4, 3, 2, 1], ![2, 3, 4, 5, 6, 0], ![1, 6, 5, 4, 3, 0], ![1, 4, 5, 6, 2, 0], ![1, 3, 6, 5, 2, 0], ![1, 3, 6, 4, 2, 0], ![1, 3, 5, 4, 2, 0]], proof := .tail 78 }

theorem namedLeaf037_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23845)) namedLeaf037 = true :=
  by decide +kernel

def namedLeaf038 : LeafData := { rows := ![![6, 5, 4, 3, 2, 1], ![2, 3, 4, 5, 6, 0], ![1, 6, 5, 4, 3, 0], ![1, 4, 6, 5, 2, 0], ![1, 3, 6, 5, 2, 0], ![1, 6, 3, 4, 2, 0], ![1, 5, 3, 4, 2, 0]], proof := .tail 95 }

theorem namedLeaf038_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23846)) namedLeaf038 = true :=
  by decide +kernel

def namedLeaf039 : LeafData := { rows := ![![6, 5, 4, 3, 2, 1], ![2, 3, 4, 5, 6, 0], ![1, 6, 5, 4, 3, 0], ![1, 6, 4, 5, 2, 0], ![1, 6, 3, 5, 2, 0], ![1, 6, 3, 4, 2, 0], ![1, 5, 4, 3, 2, 0]], proof := .tail 32 }

theorem namedLeaf039_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23847)) namedLeaf039 = true :=
  by decide +kernel

def namedLeaf040 : LeafData := { rows := ![![6, 5, 4, 3, 2, 1], ![2, 3, 4, 5, 6, 0], ![1, 6, 5, 4, 3, 0], ![1, 5, 4, 6, 2, 0], ![1, 5, 3, 6, 2, 0], ![1, 4, 3, 6, 2, 0], ![1, 3, 4, 5, 2, 0]], proof := .tail 99 }

theorem namedLeaf040_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23848)) namedLeaf040 = true :=
  by decide +kernel

def namedLeaf041 : LeafData := { rows := ![![6, 5, 4, 3, 2, 1], ![2, 3, 4, 5, 6, 0], ![1, 6, 5, 4, 3, 0], ![1, 5, 6, 4, 2, 0], ![1, 5, 6, 3, 2, 0], ![1, 4, 3, 6, 2, 0], ![1, 4, 3, 5, 2, 0]], proof := .tail 76 }

theorem namedLeaf041_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23849)) namedLeaf041 = true :=
  by decide +kernel

def namedLeaf042 : LeafData := { rows := ![![6, 5, 4, 3, 2, 1], ![2, 3, 4, 5, 6, 0], ![1, 6, 5, 4, 3, 0], ![1, 6, 5, 4, 2, 0], ![1, 5, 6, 3, 2, 0], ![1, 4, 6, 3, 2, 0], ![1, 4, 5, 3, 2, 0]], proof := .tail 44 }

theorem namedLeaf042_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23850)) namedLeaf042 = true :=
  by decide +kernel

def namedLeaf043 : LeafData := { rows := ![![6, 5, 4, 3, 2, 1], ![2, 3, 4, 5, 6, 0], ![1, 6, 5, 4, 3, 0], ![1, 6, 5, 4, 2, 0], ![1, 6, 5, 3, 2, 0], ![1, 6, 4, 3, 2, 0], ![1, 5, 4, 3, 2, 0]], proof := .tail 28 }

theorem namedLeaf043_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23851)) namedLeaf043 = true :=
  by decide +kernel

def namedLeaf044 : LeafData := { rows := ![![6, 5, 4, 3, 2, 1], ![2, 3, 4, 6, 5, 0], ![1, 3, 4, 6, 5, 0], ![1, 2, 4, 6, 5, 0], ![1, 2, 3, 6, 5, 0], ![6, 1, 2, 3, 4, 0], ![5, 1, 2, 3, 4, 0]], proof := .tail 81 }

theorem namedLeaf044_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23852)) namedLeaf044 = true :=
  by decide +kernel

def namedLeaf045 : LeafData := { rows := ![![6, 5, 4, 3, 2, 1], ![2, 3, 4, 6, 5, 0], ![1, 3, 4, 6, 5, 0], ![1, 2, 6, 4, 5, 0], ![1, 2, 6, 3, 5, 0], ![6, 1, 2, 3, 4, 0], ![5, 1, 2, 4, 3, 0]], proof := .tail 36 }

theorem namedLeaf045_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23853)) namedLeaf045 = true :=
  by decide +kernel

def namedLeaf046 : LeafData := { rows := ![![6, 5, 4, 3, 2, 1], ![2, 3, 4, 6, 5, 0], ![1, 3, 4, 6, 5, 0], ![1, 2, 6, 5, 4, 0], ![1, 2, 6, 5, 3, 0], ![6, 1, 2, 4, 3, 0], ![5, 1, 2, 4, 3, 0]], proof := .tail 29 }

theorem namedLeaf046_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23854)) namedLeaf046 = true :=
  by decide +kernel

def namedLeaf047 : LeafData := { rows := ![![6, 5, 4, 3, 2, 1], ![2, 3, 4, 6, 5, 0], ![1, 4, 3, 6, 5, 0], ![1, 4, 2, 6, 5, 0], ![1, 3, 2, 6, 5, 0], ![6, 1, 2, 3, 4, 0], ![5, 1, 2, 3, 4, 0]], proof := .tail 37 }

theorem namedLeaf047_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23855)) namedLeaf047 = true :=
  by decide +kernel

def namedLeaf048 : LeafData := { rows := ![![6, 5, 4, 3, 2, 1], ![2, 3, 4, 6, 5, 0], ![1, 3, 6, 4, 5, 0], ![1, 2, 6, 4, 5, 0], ![1, 6, 2, 3, 5, 0], ![6, 1, 2, 3, 4, 0], ![5, 1, 4, 2, 3, 0]], proof := .tail 86 }

theorem namedLeaf048_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23856)) namedLeaf048 = true :=
  by decide +kernel

def namedLeaf049 : LeafData := { rows := ![![6, 5, 4, 3, 2, 1], ![2, 3, 4, 6, 5, 0], ![1, 3, 6, 4, 5, 0], ![1, 2, 6, 5, 4, 0], ![1, 6, 2, 5, 3, 0], ![6, 1, 2, 4, 3, 0], ![5, 1, 4, 2, 3, 0]], proof := .tail 73 }

theorem namedLeaf049_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23857)) namedLeaf049 = true :=
  by decide +kernel

def namedLeaf050 : LeafData := { rows := ![![6, 5, 4, 3, 2, 1], ![2, 3, 4, 6, 5, 0], ![1, 3, 6, 5, 4, 0], ![1, 2, 6, 5, 4, 0], ![1, 6, 5, 2, 3, 0], ![6, 1, 4, 2, 3, 0], ![5, 1, 4, 2, 3, 0]], proof := .tail 79 }

theorem namedLeaf050_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23858)) namedLeaf050 = true :=
  by decide +kernel

def namedLeaf051 : LeafData := { rows := ![![6, 5, 4, 3, 2, 1], ![2, 3, 4, 6, 5, 0], ![1, 4, 6, 3, 5, 0], ![1, 4, 6, 2, 5, 0], ![1, 3, 2, 6, 5, 0], ![6, 1, 2, 3, 4, 0], ![5, 1, 3, 2, 4, 0]], proof := .tail 14 }

theorem namedLeaf051_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23859)) namedLeaf051 = true :=
  by decide +kernel

def namedLeaf052 : LeafData := { rows := ![![6, 5, 4, 3, 2, 1], ![2, 3, 4, 6, 5, 0], ![1, 6, 3, 4, 5, 0], ![1, 6, 2, 4, 5, 0], ![1, 6, 2, 3, 5, 0], ![6, 1, 2, 3, 4, 0], ![5, 1, 4, 3, 2, 0]], proof := .tail 98 }

theorem namedLeaf052_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23860)) namedLeaf052 = true :=
  by decide +kernel

def namedLeaf053 : LeafData := { rows := ![![6, 5, 4, 3, 2, 1], ![2, 3, 4, 6, 5, 0], ![1, 6, 3, 4, 5, 0], ![1, 6, 2, 5, 4, 0], ![1, 6, 2, 5, 3, 0], ![6, 1, 2, 4, 3, 0], ![5, 1, 4, 3, 2, 0]], proof := .tail 24 }

theorem namedLeaf053_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23861)) namedLeaf053 = true :=
  by decide +kernel

def namedLeaf054 : LeafData := { rows := ![![6, 5, 4, 3, 2, 1], ![2, 3, 4, 6, 5, 0], ![1, 6, 4, 3, 5, 0], ![1, 4, 6, 2, 5, 0], ![1, 3, 6, 2, 5, 0], ![6, 1, 2, 3, 4, 0], ![5, 1, 3, 4, 2, 0]], proof := .tail 2 }

theorem namedLeaf054_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23862)) namedLeaf054 = true :=
  by decide +kernel

def namedLeaf055 : LeafData := { rows := ![![6, 5, 4, 3, 2, 1], ![2, 3, 4, 6, 5, 0], ![1, 6, 4, 3, 5, 0], ![1, 6, 4, 2, 5, 0], ![1, 6, 3, 2, 5, 0], ![6, 1, 2, 3, 4, 0], ![5, 1, 4, 3, 2, 0]], proof := .tail 67 }

theorem namedLeaf055_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23863)) namedLeaf055 = true :=
  by decide +kernel

def namedLeaf056 : LeafData := { rows := ![![6, 5, 4, 3, 2, 1], ![2, 3, 4, 6, 5, 0], ![1, 6, 3, 5, 4, 0], ![1, 6, 2, 5, 4, 0], ![1, 6, 5, 2, 3, 0], ![6, 1, 4, 2, 3, 0], ![5, 1, 4, 3, 2, 0]], proof := .tail 20 }

theorem namedLeaf056_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23864)) namedLeaf056 = true :=
  by decide +kernel

def namedLeaf057 : LeafData := { rows := ![![6, 5, 4, 3, 2, 1], ![2, 3, 4, 6, 5, 0], ![1, 4, 6, 5, 3, 0], ![1, 4, 6, 5, 2, 0], ![1, 3, 2, 6, 5, 0], ![6, 1, 3, 2, 4, 0], ![5, 1, 3, 2, 4, 0]], proof := .tail 71 }

theorem namedLeaf057_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23865)) namedLeaf057 = true :=
  by decide +kernel

def namedLeaf058 : LeafData := { rows := ![![6, 5, 4, 3, 2, 1], ![2, 3, 4, 6, 5, 0], ![1, 6, 4, 5, 3, 0], ![1, 4, 6, 5, 2, 0], ![1, 3, 6, 2, 5, 0], ![6, 1, 3, 2, 4, 0], ![5, 1, 3, 4, 2, 0]], proof := .tail 2 }

theorem namedLeaf058_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23866)) namedLeaf058 = true :=
  by decide +kernel

def namedLeaf059 : LeafData := { rows := ![![6, 5, 4, 3, 2, 1], ![2, 3, 4, 6, 5, 0], ![1, 6, 4, 5, 3, 0], ![1, 6, 4, 5, 2, 0], ![1, 6, 3, 2, 5, 0], ![6, 1, 3, 2, 4, 0], ![5, 1, 4, 3, 2, 0]], proof := .tail 67 }

theorem namedLeaf059_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23867)) namedLeaf059 = true :=
  by decide +kernel

def namedLeaf060 : LeafData := { rows := ![![6, 5, 4, 3, 2, 1], ![2, 3, 4, 6, 5, 0], ![1, 6, 5, 3, 4, 0], ![1, 6, 5, 2, 4, 0], ![1, 6, 5, 2, 3, 0], ![6, 1, 4, 3, 2, 0], ![5, 1, 4, 3, 2, 0]], proof := .tail 11 }

theorem namedLeaf060_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23868)) namedLeaf060 = true :=
  by decide +kernel

def namedLeaf061 : LeafData := { rows := ![![6, 5, 4, 3, 2, 1], ![2, 3, 4, 6, 5, 0], ![1, 6, 5, 4, 3, 0], ![1, 4, 6, 5, 2, 0], ![1, 3, 6, 5, 2, 0], ![6, 1, 3, 4, 2, 0], ![5, 1, 3, 4, 2, 0]], proof := .tail 66 }

theorem namedLeaf061_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23869)) namedLeaf061 = true :=
  by decide +kernel

def namedLeaf062 : LeafData := { rows := ![![6, 5, 4, 3, 2, 1], ![2, 3, 4, 6, 5, 0], ![1, 6, 5, 4, 3, 0], ![1, 6, 4, 5, 2, 0], ![1, 6, 3, 5, 2, 0], ![6, 1, 3, 4, 2, 0], ![5, 1, 4, 3, 2, 0]], proof := .tail 93 }

theorem namedLeaf062_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23870)) namedLeaf062 = true :=
  by decide +kernel

def namedLeaf063 : LeafData := { rows := ![![6, 5, 4, 3, 2, 1], ![2, 3, 4, 6, 5, 0], ![1, 6, 5, 4, 3, 0], ![1, 6, 5, 4, 2, 0], ![1, 6, 5, 3, 2, 0], ![6, 1, 4, 3, 2, 0], ![5, 1, 4, 3, 2, 0]], proof := .tail 52 }

theorem namedLeaf063_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23871)) namedLeaf063 = true :=
  by decide +kernel

def namedLeaf064 : LeafData := { rows := ![![6, 5, 4, 3, 2, 1], ![2, 3, 6, 4, 5, 0], ![1, 3, 6, 4, 5, 0], ![1, 2, 6, 4, 5, 0], ![6, 1, 2, 3, 5, 0], ![6, 1, 2, 3, 4, 0], ![5, 4, 1, 2, 3, 0]], proof := .tail 54 }

theorem namedLeaf064_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23872)) namedLeaf064 = true :=
  by decide +kernel

def namedLeaf065 : LeafData := { rows := ![![6, 5, 4, 3, 2, 1], ![2, 3, 6, 4, 5, 0], ![1, 3, 6, 4, 5, 0], ![1, 2, 6, 5, 4, 0], ![6, 1, 2, 5, 3, 0], ![6, 1, 2, 4, 3, 0], ![5, 4, 1, 2, 3, 0]], proof := .tail 43 }

theorem namedLeaf065_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23873)) namedLeaf065 = true :=
  by decide +kernel

def namedLeaf066 : LeafData := { rows := ![![6, 5, 4, 3, 2, 1], ![2, 3, 6, 4, 5, 0], ![1, 3, 6, 5, 4, 0], ![1, 2, 6, 5, 4, 0], ![6, 1, 5, 2, 3, 0], ![6, 1, 4, 2, 3, 0], ![5, 4, 1, 2, 3, 0]], proof := .tail 39 }

theorem namedLeaf066_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23874)) namedLeaf066 = true :=
  by decide +kernel

def namedLeaf067 : LeafData := { rows := ![![6, 5, 4, 3, 2, 1], ![2, 3, 6, 4, 5, 0], ![1, 6, 3, 4, 5, 0], ![1, 6, 2, 4, 5, 0], ![6, 1, 2, 3, 5, 0], ![6, 1, 2, 3, 4, 0], ![5, 4, 1, 3, 2, 0]], proof := .tail 96 }

theorem namedLeaf067_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23875)) namedLeaf067 = true :=
  by decide +kernel

def namedLeaf068 : LeafData := { rows := ![![6, 5, 4, 3, 2, 1], ![2, 3, 6, 4, 5, 0], ![1, 6, 3, 4, 5, 0], ![1, 6, 2, 5, 4, 0], ![6, 1, 2, 5, 3, 0], ![6, 1, 2, 4, 3, 0], ![5, 4, 1, 3, 2, 0]], proof := .tail 74 }

theorem namedLeaf068_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23876)) namedLeaf068 = true :=
  by decide +kernel

def namedLeaf069 : LeafData := { rows := ![![6, 5, 4, 3, 2, 1], ![2, 3, 6, 4, 5, 0], ![1, 6, 3, 5, 4, 0], ![1, 6, 2, 5, 4, 0], ![6, 1, 5, 2, 3, 0], ![6, 1, 4, 2, 3, 0], ![5, 4, 1, 3, 2, 0]], proof := .tail 58 }

theorem namedLeaf069_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23877)) namedLeaf069 = true :=
  by decide +kernel

def namedLeaf070 : LeafData := { rows := ![![6, 5, 4, 3, 2, 1], ![2, 3, 6, 4, 5, 0], ![1, 6, 5, 3, 4, 0], ![1, 6, 5, 2, 4, 0], ![6, 1, 5, 2, 3, 0], ![6, 1, 4, 3, 2, 0], ![5, 4, 1, 3, 2, 0]], proof := .tail 50 }

theorem namedLeaf070_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23878)) namedLeaf070 = true :=
  by decide +kernel

def namedLeaf071 : LeafData := { rows := ![![6, 5, 4, 3, 2, 1], ![2, 3, 6, 4, 5, 0], ![1, 6, 4, 3, 5, 0], ![1, 6, 4, 2, 5, 0], ![6, 1, 3, 2, 5, 0], ![6, 1, 2, 3, 4, 0], ![5, 4, 1, 3, 2, 0]], proof := .tail 56 }

theorem namedLeaf071_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23879)) namedLeaf071 = true :=
  by decide +kernel

def namedLeaf072 : LeafData := { rows := ![![6, 5, 4, 3, 2, 1], ![2, 3, 6, 4, 5, 0], ![1, 6, 4, 5, 3, 0], ![1, 6, 4, 5, 2, 0], ![6, 1, 3, 2, 5, 0], ![6, 1, 3, 2, 4, 0], ![5, 4, 1, 3, 2, 0]], proof := .tail 9 }

theorem namedLeaf072_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23880)) namedLeaf072 = true :=
  by decide +kernel

def namedLeaf073 : LeafData := { rows := ![![6, 5, 4, 3, 2, 1], ![2, 3, 6, 4, 5, 0], ![1, 6, 5, 4, 3, 0], ![1, 6, 4, 5, 2, 0], ![6, 1, 3, 5, 2, 0], ![6, 1, 3, 4, 2, 0], ![5, 4, 1, 3, 2, 0]], proof := .tail 64 }

theorem namedLeaf073_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23881)) namedLeaf073 = true :=
  by decide +kernel

def namedLeaf074 : LeafData := { rows := ![![6, 5, 4, 3, 2, 1], ![2, 3, 6, 4, 5, 0], ![1, 6, 5, 4, 3, 0], ![1, 6, 5, 4, 2, 0], ![6, 1, 5, 3, 2, 0], ![6, 1, 4, 3, 2, 0], ![5, 4, 1, 3, 2, 0]], proof := .tail 60 }

theorem namedLeaf074_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23882)) namedLeaf074 = true :=
  by decide +kernel

def namedLeaf075 : LeafData := { rows := ![![6, 5, 4, 3, 2, 1], ![2, 3, 5, 4, 6, 0], ![1, 3, 5, 4, 6, 0], ![1, 2, 5, 4, 6, 0], ![5, 1, 2, 3, 6, 0], ![4, 1, 2, 3, 6, 0], ![1, 2, 3, 4, 5, 0]], proof := .tail 69 }

theorem namedLeaf075_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23883)) namedLeaf075 = true :=
  by decide +kernel

def namedLeaf076 : LeafData := { rows := ![![6, 5, 4, 3, 2, 1], ![2, 3, 5, 4, 6, 0], ![1, 3, 5, 4, 6, 0], ![1, 2, 5, 6, 4, 0], ![5, 1, 2, 6, 3, 0], ![4, 1, 2, 3, 6, 0], ![1, 2, 4, 3, 5, 0]], proof := .tail 69 }

theorem namedLeaf076_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23884)) namedLeaf076 = true :=
  by decide +kernel

def namedLeaf077 : LeafData := { rows := ![![6, 5, 4, 3, 2, 1], ![2, 3, 5, 4, 6, 0], ![1, 3, 5, 4, 6, 0], ![1, 2, 6, 5, 4, 0], ![5, 1, 2, 6, 3, 0], ![4, 1, 2, 6, 3, 0], ![1, 2, 4, 5, 3, 0]], proof := .tail 0 }

theorem namedLeaf077_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23885)) namedLeaf077 = true :=
  by decide +kernel

def namedLeaf078 : LeafData := { rows := ![![6, 5, 4, 3, 2, 1], ![2, 3, 5, 4, 6, 0], ![1, 3, 5, 6, 4, 0], ![1, 2, 5, 6, 4, 0], ![5, 1, 6, 2, 3, 0], ![4, 1, 2, 3, 6, 0], ![1, 4, 2, 3, 5, 0]], proof := .tail 69 }

theorem namedLeaf078_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23886)) namedLeaf078 = true :=
  by decide +kernel

def namedLeaf079 : LeafData := { rows := ![![6, 5, 4, 3, 2, 1], ![2, 3, 5, 4, 6, 0], ![1, 3, 5, 6, 4, 0], ![1, 2, 6, 5, 4, 0], ![5, 1, 6, 2, 3, 0], ![4, 1, 2, 6, 3, 0], ![1, 4, 2, 5, 3, 0]], proof := .tail 0 }

theorem namedLeaf079_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23887)) namedLeaf079 = true :=
  by decide +kernel

def namedLeaf080 : LeafData := { rows := ![![6, 5, 4, 3, 2, 1], ![2, 3, 5, 4, 6, 0], ![1, 3, 6, 5, 4, 0], ![1, 2, 6, 5, 4, 0], ![5, 1, 6, 2, 3, 0], ![4, 1, 6, 2, 3, 0], ![1, 4, 5, 2, 3, 0]], proof := .tail 22 }

theorem namedLeaf080_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23888)) namedLeaf080 = true :=
  by decide +kernel

def namedLeaf081 : LeafData := { rows := ![![6, 5, 4, 3, 2, 1], ![2, 3, 5, 4, 6, 0], ![1, 6, 3, 5, 4, 0], ![1, 6, 2, 5, 4, 0], ![5, 1, 6, 2, 3, 0], ![4, 1, 6, 2, 3, 0], ![1, 4, 5, 3, 2, 0]], proof := .tail 63 }

theorem namedLeaf081_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23889)) namedLeaf081 = true :=
  by decide +kernel

def namedLeaf082 : LeafData := { rows := ![![6, 5, 4, 3, 2, 1], ![2, 3, 5, 4, 6, 0], ![1, 5, 3, 4, 6, 0], ![1, 5, 2, 4, 6, 0], ![5, 1, 2, 3, 6, 0], ![4, 1, 3, 2, 6, 0], ![1, 2, 3, 4, 5, 0]], proof := .tail 4 }

theorem namedLeaf082_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23890)) namedLeaf082 = true :=
  by decide +kernel

def namedLeaf083 : LeafData := { rows := ![![6, 5, 4, 3, 2, 1], ![2, 3, 5, 4, 6, 0], ![1, 5, 3, 4, 6, 0], ![1, 5, 2, 6, 4, 0], ![5, 1, 2, 6, 3, 0], ![4, 1, 3, 2, 6, 0], ![1, 2, 4, 3, 5, 0]], proof := .tail 30 }

theorem namedLeaf083_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23891)) namedLeaf083 = true :=
  by decide +kernel

def namedLeaf084 : LeafData := { rows := ![![6, 5, 4, 3, 2, 1], ![2, 3, 5, 4, 6, 0], ![1, 5, 3, 6, 4, 0], ![1, 5, 2, 6, 4, 0], ![5, 1, 6, 2, 3, 0], ![4, 1, 3, 2, 6, 0], ![1, 4, 2, 3, 5, 0]], proof := .tail 55 }

theorem namedLeaf084_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23892)) namedLeaf084 = true :=
  by decide +kernel

def namedLeaf085 : LeafData := { rows := ![![6, 5, 4, 3, 2, 1], ![2, 3, 5, 4, 6, 0], ![1, 5, 6, 3, 4, 0], ![1, 5, 6, 2, 4, 0], ![5, 1, 6, 2, 3, 0], ![4, 1, 3, 2, 6, 0], ![1, 4, 3, 2, 5, 0]], proof := .tail 16 }

theorem namedLeaf085_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23893)) namedLeaf085 = true :=
  by decide +kernel

def namedLeaf086 : LeafData := { rows := ![![6, 5, 4, 3, 2, 1], ![2, 3, 5, 4, 6, 0], ![1, 6, 5, 3, 4, 0], ![1, 5, 6, 2, 4, 0], ![5, 1, 6, 2, 3, 0], ![4, 1, 3, 6, 2, 0], ![1, 4, 3, 5, 2, 0]], proof := .tail 65 }

theorem namedLeaf086_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23894)) namedLeaf086 = true :=
  by decide +kernel

def namedLeaf087 : LeafData := { rows := ![![6, 5, 4, 3, 2, 1], ![2, 3, 5, 4, 6, 0], ![1, 6, 5, 3, 4, 0], ![1, 6, 5, 2, 4, 0], ![5, 1, 6, 2, 3, 0], ![4, 1, 6, 3, 2, 0], ![1, 4, 5, 3, 2, 0]], proof := .tail 17 }

theorem namedLeaf087_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23895)) namedLeaf087 = true :=
  by decide +kernel

def namedLeaf088 : LeafData := { rows := ![![6, 5, 4, 3, 2, 1], ![2, 3, 5, 4, 6, 0], ![1, 5, 4, 3, 6, 0], ![1, 5, 4, 2, 6, 0], ![5, 1, 3, 2, 6, 0], ![4, 1, 3, 2, 6, 0], ![1, 2, 3, 4, 5, 0]], proof := .tail 1 }

theorem namedLeaf088_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23896)) namedLeaf088 = true :=
  by decide +kernel

def namedLeaf089 : LeafData := { rows := ![![6, 5, 4, 3, 2, 1], ![2, 3, 5, 4, 6, 0], ![1, 5, 4, 6, 3, 0], ![1, 5, 4, 6, 2, 0], ![5, 1, 3, 2, 6, 0], ![4, 1, 3, 2, 6, 0], ![1, 3, 2, 4, 5, 0]], proof := .tail 38 }

theorem namedLeaf089_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23897)) namedLeaf089 = true :=
  by decide +kernel

def namedLeaf090 : LeafData := { rows := ![![6, 5, 4, 3, 2, 1], ![2, 3, 5, 4, 6, 0], ![1, 5, 6, 4, 3, 0], ![1, 5, 4, 6, 2, 0], ![5, 1, 3, 6, 2, 0], ![4, 1, 3, 2, 6, 0], ![1, 3, 4, 2, 5, 0]], proof := .tail 70 }

theorem namedLeaf090_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23898)) namedLeaf090 = true :=
  by decide +kernel

def namedLeaf091 : LeafData := { rows := ![![6, 5, 4, 3, 2, 1], ![2, 3, 5, 4, 6, 0], ![1, 5, 6, 4, 3, 0], ![1, 5, 6, 4, 2, 0], ![5, 1, 6, 3, 2, 0], ![4, 1, 3, 2, 6, 0], ![1, 4, 3, 2, 5, 0]], proof := .tail 8 }

theorem namedLeaf091_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23899)) namedLeaf091 = true :=
  by decide +kernel

def namedLeaf092 : LeafData := { rows := ![![6, 5, 4, 3, 2, 1], ![2, 3, 5, 4, 6, 0], ![1, 6, 5, 4, 3, 0], ![1, 5, 4, 6, 2, 0], ![5, 1, 3, 6, 2, 0], ![4, 1, 3, 6, 2, 0], ![1, 3, 4, 5, 2, 0]], proof := .tail 5 }

theorem namedLeaf092_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23900)) namedLeaf092 = true :=
  by decide +kernel

def namedLeaf093 : LeafData := { rows := ![![6, 5, 4, 3, 2, 1], ![2, 3, 5, 4, 6, 0], ![1, 6, 5, 4, 3, 0], ![1, 5, 6, 4, 2, 0], ![5, 1, 6, 3, 2, 0], ![4, 1, 3, 6, 2, 0], ![1, 4, 3, 5, 2, 0]], proof := .tail 8 }

theorem namedLeaf093_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23901)) namedLeaf093 = true :=
  by decide +kernel

def namedLeaf094 : LeafData := { rows := ![![6, 5, 4, 3, 2, 1], ![2, 3, 5, 4, 6, 0], ![1, 6, 5, 4, 3, 0], ![1, 6, 5, 4, 2, 0], ![5, 1, 6, 3, 2, 0], ![4, 1, 6, 3, 2, 0], ![1, 4, 5, 3, 2, 0]], proof := .tail 80 }

theorem namedLeaf094_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23902)) namedLeaf094 = true :=
  by decide +kernel

def namedLeaf095 : LeafData := { rows := ![![6, 5, 4, 3, 2, 1], ![2, 3, 5, 6, 4, 0], ![1, 3, 5, 6, 4, 0], ![1, 2, 5, 6, 4, 0], ![5, 6, 1, 2, 3, 0], ![4, 1, 2, 3, 6, 0], ![4, 1, 2, 3, 5, 0]], proof := .tail 69 }

theorem namedLeaf095_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23903)) namedLeaf095 = true :=
  by decide +kernel

def namedLeaf096 : LeafData := { rows := ![![6, 5, 4, 3, 2, 1], ![2, 3, 5, 6, 4, 0], ![1, 3, 5, 6, 4, 0], ![1, 2, 6, 5, 4, 0], ![5, 6, 1, 2, 3, 0], ![4, 1, 2, 6, 3, 0], ![4, 1, 2, 5, 3, 0]], proof := .tail 85 }

theorem namedLeaf096_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23904)) namedLeaf096 = true :=
  by decide +kernel

def namedLeaf097 : LeafData := { rows := ![![6, 5, 4, 3, 2, 1], ![2, 3, 5, 6, 4, 0], ![1, 3, 6, 5, 4, 0], ![1, 2, 6, 5, 4, 0], ![5, 6, 1, 2, 3, 0], ![4, 1, 6, 2, 3, 0], ![4, 1, 5, 2, 3, 0]], proof := .tail 6 }

theorem namedLeaf097_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23905)) namedLeaf097 = true :=
  by decide +kernel

def namedLeaf098 : LeafData := { rows := ![![6, 5, 4, 3, 2, 1], ![2, 3, 5, 6, 4, 0], ![1, 6, 3, 5, 4, 0], ![1, 6, 2, 5, 4, 0], ![5, 6, 1, 2, 3, 0], ![4, 1, 6, 2, 3, 0], ![4, 1, 5, 3, 2, 0]], proof := .tail 63 }

theorem namedLeaf098_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23906)) namedLeaf098 = true :=
  by decide +kernel

def namedLeaf099 : LeafData := { rows := ![![6, 5, 4, 3, 2, 1], ![2, 3, 5, 6, 4, 0], ![1, 5, 3, 6, 4, 0], ![1, 5, 2, 6, 4, 0], ![5, 6, 1, 2, 3, 0], ![4, 1, 3, 2, 6, 0], ![4, 1, 2, 3, 5, 0]], proof := .tail 55 }

theorem namedLeaf099_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23907)) namedLeaf099 = true :=
  by decide +kernel

def namedLeaf100 : LeafData := { rows := ![![6, 5, 4, 3, 2, 1], ![2, 3, 5, 6, 4, 0], ![1, 5, 6, 3, 4, 0], ![1, 5, 6, 2, 4, 0], ![5, 6, 1, 2, 3, 0], ![4, 1, 3, 2, 6, 0], ![4, 1, 3, 2, 5, 0]], proof := .tail 77 }

theorem namedLeaf100_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23908)) namedLeaf100 = true :=
  by decide +kernel

def namedLeaf101 : LeafData := { rows := ![![6, 5, 4, 3, 2, 1], ![2, 3, 5, 6, 4, 0], ![1, 6, 5, 3, 4, 0], ![1, 5, 6, 2, 4, 0], ![5, 6, 1, 2, 3, 0], ![4, 1, 3, 6, 2, 0], ![4, 1, 3, 5, 2, 0]], proof := .tail 65 }

theorem namedLeaf101_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23909)) namedLeaf101 = true :=
  by decide +kernel

def namedLeaf102 : LeafData := { rows := ![![6, 5, 4, 3, 2, 1], ![2, 3, 5, 6, 4, 0], ![1, 6, 5, 3, 4, 0], ![1, 6, 5, 2, 4, 0], ![5, 6, 1, 2, 3, 0], ![4, 1, 6, 3, 2, 0], ![4, 1, 5, 3, 2, 0]], proof := .tail 17 }

theorem namedLeaf102_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23910)) namedLeaf102 = true :=
  by decide +kernel

def namedLeaf103 : LeafData := { rows := ![![6, 5, 4, 3, 2, 1], ![2, 3, 6, 5, 4, 0], ![1, 3, 6, 5, 4, 0], ![1, 2, 6, 5, 4, 0], ![5, 6, 1, 2, 3, 0], ![4, 6, 1, 2, 3, 0], ![4, 5, 1, 2, 3, 0]], proof := .tail 89 }

theorem namedLeaf103_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23911)) namedLeaf103 = true :=
  by decide +kernel

def namedLeaf104 : LeafData := { rows := ![![6, 5, 4, 3, 2, 1], ![2, 3, 6, 5, 4, 0], ![1, 6, 3, 5, 4, 0], ![1, 6, 2, 5, 4, 0], ![5, 6, 1, 2, 3, 0], ![4, 6, 1, 2, 3, 0], ![4, 5, 1, 3, 2, 0]], proof := .tail 63 }

theorem namedLeaf104_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23912)) namedLeaf104 = true :=
  by decide +kernel

def namedLeaf105 : LeafData := { rows := ![![6, 5, 4, 3, 2, 1], ![2, 3, 6, 5, 4, 0], ![1, 6, 5, 3, 4, 0], ![1, 6, 5, 2, 4, 0], ![5, 6, 1, 2, 3, 0], ![4, 6, 1, 3, 2, 0], ![4, 5, 1, 3, 2, 0]], proof := .tail 17 }

theorem namedLeaf105_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23913)) namedLeaf105 = true :=
  by decide +kernel

def namedLeaf106 : LeafData := { rows := ![![6, 5, 4, 3, 2, 1], ![2, 3, 6, 5, 4, 0], ![1, 3, 6, 5, 4, 0], ![1, 2, 6, 5, 4, 0], ![6, 5, 1, 2, 3, 0], ![6, 4, 1, 2, 3, 0], ![5, 4, 1, 2, 3, 0]], proof := .tail 94 }

theorem namedLeaf106_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23914)) namedLeaf106 = true :=
  by decide +kernel

def namedLeaf107 : LeafData := { rows := ![![6, 5, 4, 3, 2, 1], ![2, 3, 6, 5, 4, 0], ![1, 6, 3, 5, 4, 0], ![1, 6, 2, 5, 4, 0], ![6, 5, 1, 2, 3, 0], ![6, 4, 1, 2, 3, 0], ![5, 4, 1, 3, 2, 0]], proof := .tail 61 }

theorem namedLeaf107_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23915)) namedLeaf107 = true :=
  by decide +kernel

def namedLeaf108 : LeafData := { rows := ![![6, 5, 4, 3, 2, 1], ![2, 3, 6, 5, 4, 0], ![1, 6, 5, 3, 4, 0], ![1, 6, 5, 2, 4, 0], ![6, 5, 1, 2, 3, 0], ![6, 4, 1, 3, 2, 0], ![5, 4, 1, 3, 2, 0]], proof := .tail 35 }

theorem namedLeaf108_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23916)) namedLeaf108 = true :=
  by decide +kernel

def namedLeaf109 : LeafData := { rows := ![![6, 5, 4, 3, 2, 1], ![2, 3, 5, 6, 4, 0], ![1, 5, 6, 4, 3, 0], ![1, 5, 6, 4, 2, 0], ![5, 6, 1, 3, 2, 0], ![4, 1, 3, 2, 6, 0], ![4, 1, 3, 2, 5, 0]], proof := .tail 33 }

theorem namedLeaf109_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23917)) namedLeaf109 = true :=
  by decide +kernel

def namedLeaf110 : LeafData := { rows := ![![6, 5, 4, 3, 2, 1], ![2, 3, 5, 6, 4, 0], ![1, 6, 5, 4, 3, 0], ![1, 5, 6, 4, 2, 0], ![5, 6, 1, 3, 2, 0], ![4, 1, 3, 6, 2, 0], ![4, 1, 3, 5, 2, 0]], proof := .tail 76 }

theorem namedLeaf110_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23918)) namedLeaf110 = true :=
  by decide +kernel

def namedLeaf111 : LeafData := { rows := ![![6, 5, 4, 3, 2, 1], ![2, 3, 5, 6, 4, 0], ![1, 6, 5, 4, 3, 0], ![1, 6, 5, 4, 2, 0], ![5, 6, 1, 3, 2, 0], ![4, 1, 6, 3, 2, 0], ![4, 1, 5, 3, 2, 0]], proof := .tail 83 }

theorem namedLeaf111_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23919)) namedLeaf111 = true :=
  by decide +kernel

def namedLeaf112 : LeafData := { rows := ![![6, 5, 4, 3, 2, 1], ![2, 3, 6, 5, 4, 0], ![1, 6, 5, 4, 3, 0], ![1, 6, 5, 4, 2, 0], ![5, 6, 1, 3, 2, 0], ![4, 6, 1, 3, 2, 0], ![4, 5, 1, 3, 2, 0]], proof := .tail 83 }

theorem namedLeaf112_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23920)) namedLeaf112 = true :=
  by decide +kernel

def namedLeaf113 : LeafData := { rows := ![![6, 5, 4, 3, 2, 1], ![2, 3, 6, 5, 4, 0], ![1, 6, 5, 4, 3, 0], ![1, 6, 5, 4, 2, 0], ![6, 5, 1, 3, 2, 0], ![6, 4, 1, 3, 2, 0], ![5, 4, 1, 3, 2, 0]], proof := .tail 51 }

theorem namedLeaf113_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23921)) namedLeaf113 = true :=
  by decide +kernel

def namedLeaf114 : LeafData := { rows := ![![6, 5, 4, 3, 2, 1], ![2, 6, 3, 4, 5, 0], ![1, 6, 3, 4, 5, 0], ![6, 1, 2, 4, 5, 0], ![6, 1, 2, 3, 5, 0], ![6, 1, 2, 3, 4, 0], ![5, 4, 3, 1, 2, 0]], proof := .tail 47 }

theorem namedLeaf114_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23922)) namedLeaf114 = true :=
  by decide +kernel

def namedLeaf115 : LeafData := { rows := ![![6, 5, 4, 3, 2, 1], ![2, 6, 3, 4, 5, 0], ![1, 6, 3, 4, 5, 0], ![6, 1, 2, 5, 4, 0], ![6, 1, 2, 5, 3, 0], ![6, 1, 2, 4, 3, 0], ![5, 4, 3, 1, 2, 0]], proof := .tail 23 }

theorem namedLeaf115_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23923)) namedLeaf115 = true :=
  by decide +kernel

def namedLeaf116 : LeafData := { rows := ![![6, 5, 4, 3, 2, 1], ![2, 6, 3, 4, 5, 0], ![1, 6, 3, 5, 4, 0], ![6, 1, 2, 5, 4, 0], ![6, 1, 5, 2, 3, 0], ![6, 1, 4, 2, 3, 0], ![5, 4, 3, 1, 2, 0]], proof := .tail 59 }

theorem namedLeaf116_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23924)) namedLeaf116 = true :=
  by decide +kernel

def namedLeaf117 : LeafData := { rows := ![![6, 5, 4, 3, 2, 1], ![2, 6, 3, 4, 5, 0], ![1, 6, 5, 3, 4, 0], ![6, 1, 5, 2, 4, 0], ![6, 1, 5, 2, 3, 0], ![6, 1, 4, 3, 2, 0], ![5, 4, 3, 1, 2, 0]], proof := .tail 3 }

theorem namedLeaf117_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23925)) namedLeaf117 = true :=
  by decide +kernel

def namedLeaf118 : LeafData := { rows := ![![6, 5, 4, 3, 2, 1], ![2, 6, 3, 4, 5, 0], ![1, 6, 4, 3, 5, 0], ![6, 1, 4, 2, 5, 0], ![6, 1, 3, 2, 5, 0], ![6, 1, 2, 3, 4, 0], ![5, 4, 3, 1, 2, 0]], proof := .tail 82 }

theorem namedLeaf118_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23926)) namedLeaf118 = true :=
  by decide +kernel

def namedLeaf119 : LeafData := { rows := ![![6, 5, 4, 3, 2, 1], ![2, 6, 3, 4, 5, 0], ![1, 6, 4, 5, 3, 0], ![6, 1, 4, 5, 2, 0], ![6, 1, 3, 2, 5, 0], ![6, 1, 3, 2, 4, 0], ![5, 4, 3, 1, 2, 0]], proof := .tail 47 }

theorem namedLeaf119_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23927)) namedLeaf119 = true :=
  by decide +kernel

def namedLeaf120 : LeafData := { rows := ![![6, 5, 4, 3, 2, 1], ![2, 6, 3, 4, 5, 0], ![1, 6, 5, 4, 3, 0], ![6, 1, 4, 5, 2, 0], ![6, 1, 3, 5, 2, 0], ![6, 1, 3, 4, 2, 0], ![5, 4, 3, 1, 2, 0]], proof := .tail 41 }

theorem namedLeaf120_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23928)) namedLeaf120 = true :=
  by decide +kernel

def namedLeaf121 : LeafData := { rows := ![![6, 5, 4, 3, 2, 1], ![2, 6, 3, 4, 5, 0], ![1, 6, 5, 4, 3, 0], ![6, 1, 5, 4, 2, 0], ![6, 1, 5, 3, 2, 0], ![6, 1, 4, 3, 2, 0], ![5, 4, 3, 1, 2, 0]], proof := .tail 60 }

theorem namedLeaf121_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23929)) namedLeaf121 = true :=
  by decide +kernel

def namedLeaf122 : LeafData := { rows := ![![6, 5, 4, 3, 2, 1], ![2, 6, 3, 5, 4, 0], ![1, 6, 3, 5, 4, 0], ![6, 1, 2, 5, 4, 0], ![5, 6, 1, 2, 3, 0], ![4, 6, 1, 2, 3, 0], ![4, 5, 3, 1, 2, 0]], proof := .tail 62 }

theorem namedLeaf122_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23930)) namedLeaf122 = true :=
  by decide +kernel

def namedLeaf123 : LeafData := { rows := ![![6, 5, 4, 3, 2, 1], ![2, 6, 3, 5, 4, 0], ![1, 6, 5, 3, 4, 0], ![6, 1, 5, 2, 4, 0], ![5, 6, 1, 2, 3, 0], ![4, 6, 1, 3, 2, 0], ![4, 5, 3, 1, 2, 0]], proof := .tail 17 }

theorem namedLeaf123_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23931)) namedLeaf123 = true :=
  by decide +kernel

def namedLeaf124 : LeafData := { rows := ![![6, 5, 4, 3, 2, 1], ![2, 6, 3, 5, 4, 0], ![1, 6, 5, 4, 3, 0], ![6, 1, 5, 4, 2, 0], ![5, 6, 1, 3, 2, 0], ![4, 6, 1, 3, 2, 0], ![4, 5, 3, 1, 2, 0]], proof := .tail 21 }

theorem namedLeaf124_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23932)) namedLeaf124 = true :=
  by decide +kernel

def namedLeaf125 : LeafData := { rows := ![![6, 5, 4, 3, 2, 1], ![2, 6, 3, 5, 4, 0], ![1, 6, 3, 5, 4, 0], ![6, 1, 2, 5, 4, 0], ![6, 5, 1, 2, 3, 0], ![6, 4, 1, 2, 3, 0], ![5, 4, 3, 1, 2, 0]], proof := .tail 97 }

theorem namedLeaf125_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23933)) namedLeaf125 = true :=
  by decide +kernel

def namedLeaf126 : LeafData := { rows := ![![6, 5, 4, 3, 2, 1], ![2, 6, 3, 5, 4, 0], ![1, 6, 5, 3, 4, 0], ![6, 1, 5, 2, 4, 0], ![6, 5, 1, 2, 3, 0], ![6, 4, 1, 3, 2, 0], ![5, 4, 3, 1, 2, 0]], proof := .tail 26 }

theorem namedLeaf126_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23934)) namedLeaf126 = true :=
  by decide +kernel

def namedLeaf127 : LeafData := { rows := ![![6, 5, 4, 3, 2, 1], ![2, 6, 3, 5, 4, 0], ![1, 6, 5, 4, 3, 0], ![6, 1, 5, 4, 2, 0], ![6, 5, 1, 3, 2, 0], ![6, 4, 1, 3, 2, 0], ![5, 4, 3, 1, 2, 0]], proof := .tail 42 }

theorem namedLeaf127_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23935)) namedLeaf127 = true :=
  by decide +kernel

def fallback : LeafData := { rows := fun _ _ => 0, proof := .tail 0 }
def lookup (offset : ℕ) : LeafData :=
  if offset < 128 then (if offset < 64 then (if offset < 32 then (if offset < 16 then (if offset < 8 then (if offset < 4 then (if offset < 2 then (if offset < 1 then (namedLeaf000) else (namedLeaf001)) else (if offset < 3 then (namedLeaf002) else (namedLeaf003))) else (if offset < 6 then (if offset < 5 then (namedLeaf004) else (namedLeaf005)) else (if offset < 7 then (namedLeaf006) else (namedLeaf007)))) else (if offset < 12 then (if offset < 10 then (if offset < 9 then (namedLeaf008) else (namedLeaf009)) else (if offset < 11 then (namedLeaf010) else (namedLeaf011))) else (if offset < 14 then (if offset < 13 then (namedLeaf012) else (namedLeaf013)) else (if offset < 15 then (namedLeaf014) else (namedLeaf015))))) else (if offset < 24 then (if offset < 20 then (if offset < 18 then (if offset < 17 then (namedLeaf016) else (namedLeaf017)) else (if offset < 19 then (namedLeaf018) else (namedLeaf019))) else (if offset < 22 then (if offset < 21 then (namedLeaf020) else (namedLeaf021)) else (if offset < 23 then (namedLeaf022) else (namedLeaf023)))) else (if offset < 28 then (if offset < 26 then (if offset < 25 then (namedLeaf024) else (namedLeaf025)) else (if offset < 27 then (namedLeaf026) else (namedLeaf027))) else (if offset < 30 then (if offset < 29 then (namedLeaf028) else (namedLeaf029)) else (if offset < 31 then (namedLeaf030) else (namedLeaf031)))))) else (if offset < 48 then (if offset < 40 then (if offset < 36 then (if offset < 34 then (if offset < 33 then (namedLeaf032) else (namedLeaf033)) else (if offset < 35 then (namedLeaf034) else (namedLeaf035))) else (if offset < 38 then (if offset < 37 then (namedLeaf036) else (namedLeaf037)) else (if offset < 39 then (namedLeaf038) else (namedLeaf039)))) else (if offset < 44 then (if offset < 42 then (if offset < 41 then (namedLeaf040) else (namedLeaf041)) else (if offset < 43 then (namedLeaf042) else (namedLeaf043))) else (if offset < 46 then (if offset < 45 then (namedLeaf044) else (namedLeaf045)) else (if offset < 47 then (namedLeaf046) else (namedLeaf047))))) else (if offset < 56 then (if offset < 52 then (if offset < 50 then (if offset < 49 then (namedLeaf048) else (namedLeaf049)) else (if offset < 51 then (namedLeaf050) else (namedLeaf051))) else (if offset < 54 then (if offset < 53 then (namedLeaf052) else (namedLeaf053)) else (if offset < 55 then (namedLeaf054) else (namedLeaf055)))) else (if offset < 60 then (if offset < 58 then (if offset < 57 then (namedLeaf056) else (namedLeaf057)) else (if offset < 59 then (namedLeaf058) else (namedLeaf059))) else (if offset < 62 then (if offset < 61 then (namedLeaf060) else (namedLeaf061)) else (if offset < 63 then (namedLeaf062) else (namedLeaf063))))))) else (if offset < 96 then (if offset < 80 then (if offset < 72 then (if offset < 68 then (if offset < 66 then (if offset < 65 then (namedLeaf064) else (namedLeaf065)) else (if offset < 67 then (namedLeaf066) else (namedLeaf067))) else (if offset < 70 then (if offset < 69 then (namedLeaf068) else (namedLeaf069)) else (if offset < 71 then (namedLeaf070) else (namedLeaf071)))) else (if offset < 76 then (if offset < 74 then (if offset < 73 then (namedLeaf072) else (namedLeaf073)) else (if offset < 75 then (namedLeaf074) else (namedLeaf075))) else (if offset < 78 then (if offset < 77 then (namedLeaf076) else (namedLeaf077)) else (if offset < 79 then (namedLeaf078) else (namedLeaf079))))) else (if offset < 88 then (if offset < 84 then (if offset < 82 then (if offset < 81 then (namedLeaf080) else (namedLeaf081)) else (if offset < 83 then (namedLeaf082) else (namedLeaf083))) else (if offset < 86 then (if offset < 85 then (namedLeaf084) else (namedLeaf085)) else (if offset < 87 then (namedLeaf086) else (namedLeaf087)))) else (if offset < 92 then (if offset < 90 then (if offset < 89 then (namedLeaf088) else (namedLeaf089)) else (if offset < 91 then (namedLeaf090) else (namedLeaf091))) else (if offset < 94 then (if offset < 93 then (namedLeaf092) else (namedLeaf093)) else (if offset < 95 then (namedLeaf094) else (namedLeaf095)))))) else (if offset < 112 then (if offset < 104 then (if offset < 100 then (if offset < 98 then (if offset < 97 then (namedLeaf096) else (namedLeaf097)) else (if offset < 99 then (namedLeaf098) else (namedLeaf099))) else (if offset < 102 then (if offset < 101 then (namedLeaf100) else (namedLeaf101)) else (if offset < 103 then (namedLeaf102) else (namedLeaf103)))) else (if offset < 108 then (if offset < 106 then (if offset < 105 then (namedLeaf104) else (namedLeaf105)) else (if offset < 107 then (namedLeaf106) else (namedLeaf107))) else (if offset < 110 then (if offset < 109 then (namedLeaf108) else (namedLeaf109)) else (if offset < 111 then (namedLeaf110) else (namedLeaf111))))) else (if offset < 120 then (if offset < 116 then (if offset < 114 then (if offset < 113 then (namedLeaf112) else (namedLeaf113)) else (if offset < 115 then (namedLeaf114) else (namedLeaf115))) else (if offset < 118 then (if offset < 117 then (namedLeaf116) else (namedLeaf117)) else (if offset < 119 then (namedLeaf118) else (namedLeaf119)))) else (if offset < 124 then (if offset < 122 then (if offset < 121 then (namedLeaf120) else (namedLeaf121)) else (if offset < 123 then (namedLeaf122) else (namedLeaf123))) else (if offset < 126 then (if offset < 125 then (namedLeaf124) else (namedLeaf125)) else (if offset < 127 then (namedLeaf126) else (namedLeaf127)))))))) else fallback

theorem point_checked (j : Fin 128) :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 (23808 + j.val))) (lookup j.val) = true := by
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

theorem correct (id : Fin 24698) (hlow : 23808 ≤ id.val) (hhigh : id.val < 23936) :
    leafCheck library (N4R2WordTree.catalog id) (lookup (id.val - 23808)) = true := by
  let j : Fin 128 := ⟨id.val - 23808, by omega⟩
  have hsum : 23808 + j.val = id.val := by dsimp [j]; omega
  have hindex : Fin.ofNat 24698 (23808 + j.val) = id := by
    apply Fin.ext
    simp only [Fin.ofNat, hsum, Nat.mod_eq_of_lt id.isLt]
  have hh := point_checked j
  rw [hindex] at hh
  exact hh

#print axioms point_checked
#print axioms correct
end Jsp404.N4R2OuterLeftData.LeafShard186
