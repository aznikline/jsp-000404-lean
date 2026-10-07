import Jsp000404.N4R2OuterLeftReplay
import Jsp000404.N4R2WordCatalog

set_option autoImplicit false
set_option pp.fullNames true
set_option maxRecDepth 8192
set_option maxHeartbeats 0
set_option Elab.async false

namespace Jsp404.N4R2OuterLeftData.LeafShard028
open N4R2OuterLeftReplay

-- Cycle fingerprint 00cbb9363763c5b6ad0429e7e3b14849f96f8ed98856dd482d6e09ee2efda898.
def localCycle00000 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 2, .distance 2 6, .distance 4 6, .distance 3 4, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, -1, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, true] }
  origin := ![.corridorUpper 2 3, .triangle 15 0, .triangle 18 0, .triangle 29 1, .triangle 32 0, .triangle 31 0, .corridorLower 4 5, .thetaNext 3]

-- Cycle fingerprint 02e770b85c3240d3543bc81265b1452001c8cdddd3d3f9b656d444465f75b8ae.
def localCycle00001 : Cycle where
  length := 10
  data := {
    node := ![.theta 2, .distance 1 2, .distance 2 3, .distance 2 4, .distance 0 2, .distance 2 6, .distance 4 6, .distance 4 5, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, -1, 0, -1, -1, 0, 0, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, true, false, false, true] }
  origin := ![.corridorUpper 1 2, .triangle 15 0, .triangle 25 2, .triangle 6 0, .triangle 8 0, .triangle 29 1, .triangle 34 1, .triangle 31 0, .corridorLower 3 4, .thetaNext 2]

-- Cycle fingerprint 03f7ac870d26a8686894dc38a883ea61fe764b41e7b0afce2acf4d04664ceec6.
def localCycle00002 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 5, .distance 0 1, .theta 1, .zero, .theta 3, .distance 2 3, .distance 1 2, .distance 1 5]
    constant := ![-2, -2, 0, 0, 3, -1, 0]
    coefficient := ![0, 0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, false, false, false, true] }
  origin := ![.gapLower 1 1, .gapLower 1 0, .thetaLower 1, .thetaUpper 3, .corridorUpper 2 3, .triangle 15 0, .triangle 17 2]

-- Cycle fingerprint 0611b0b6cd563623eb224ec84cbabe8c83591210f5fe1736f1e27681d6d038b0.
def localCycle00003 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 3, .distance 2 3, .distance 1 2, .distance 1 6, .distance 1 5, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, -1, 0, -2, -2, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, false] }
  origin := ![.thetaUpper 3, .corridorUpper 2 3, .triangle 15 0, .triangle 18 2, .gapLower 1 2, .gapLower 1 1, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint 08e981218163a0e28e04c3ec13d54613b568252b43e7733dafa9df43e4f0744e.
def localCycle00004 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 3, .distance 2 3, .distance 1 2, .distance 1 6, .distance 1 5, .distance 0 1, .theta 1, .zero]
    constant := ![0, 3, -1, 0, -2, -1, -2, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, false] }
  origin := ![.thetaUpper 3, .corridorUpper 2 3, .triangle 15 0, .triangle 18 2, .gapLower 1 2, .triangle 3 0, .gapLower 1 0, .thetaLower 1]

-- Cycle fingerprint 09606e163fc17476190726a2738e800f39b36b5180eaf7fbc817e77d20e5e9b7.
def localCycle00005 : Cycle where
  length := 10
  data := {
    node := ![.theta 2, .distance 1 2, .distance 2 3, .distance 3 6, .distance 0 3, .distance 0 2, .distance 2 5, .distance 4 5, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, -1, -1, -1, 0, -1, 0, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, true, false, false, true] }
  origin := ![.corridorUpper 1 2, .triangle 15 0, .triangle 27 0, .triangle 11 0, .triangle 5 1, .triangle 7 0, .triangle 28 1, .triangle 31 0, .corridorLower 3 4, .thetaNext 2]

-- Cycle fingerprint 0ccecf61284b253e811696ffd5d5a9ba593b420a5d9b13a3870f0f5bf7ea584b.
def localCycle00006 : Cycle where
  length := 3
  data := {
    node := ![.distance 0 1, .theta 1, .distance 1 3, .distance 0 1]
    constant := ![-2, 2, -1]
    coefficient := ![0, 1, 0]
    strict := ![false, false, false] }
  origin := ![.gapLower 1 0, .gapLower 1 6, .triangle 1 0]

-- Cycle fingerprint 0cf01e27847327c7c86468c1bf923d9c12832dfe4a0261066ccadf93eefd9a98.
def localCycle00007 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 2, .distance 2 6, .distance 0 2, .distance 2 5, .distance 3 5, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, -1, -1, -1, -1, 0, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, false, true] }
  origin := ![.corridorUpper 2 3, .triangle 15 0, .triangle 18 0, .triangle 8 0, .triangle 7 0, .triangle 26 1, .triangle 31 1, .corridorLower 4 5, .thetaNext 3]

-- Cycle fingerprint 106288107c80c0b91fc692d9eac5687ffa5aabab2a6ca23434bcc975bc55e1d5.
def localCycle00008 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 3, .distance 1 4, .distance 1 6, .distance 1 2, .distance 0 1, .theta 1, .zero, .theta 3, .distance 2 3, .distance 1 3]
    constant := ![0, -2, 0, -1, -2, 0, 0, 3, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![true, false, true, false, false, false, false, false, true] }
  origin := ![.triangle 19 2, .gapLower 1 4, .triangle 18 1, .triangle 0 0, .gapLower 1 0, .thetaLower 1, .thetaUpper 3, .corridorUpper 2 3, .triangle 15 2]

-- Cycle fingerprint 115259faee77657b131f6d5ec7a6adb6d34c785d3e367e257190719ff6f0ea4f.
def localCycle00009 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 2 4, .distance 0 2, .distance 2 5, .distance 3 5, .distance 4 5, .distance 5 6, .theta 5, .theta 4]
    constant := ![3, -1, -1, 0, 0, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false, false, true] }
  origin := ![.corridorUpper 2 4, .triangle 6 0, .triangle 7 0, .triangle 26 1, .triangle 31 1, .triangle 34 0, .corridorLower 5 6, .thetaNext 4]

-- Cycle fingerprint 12544ecce5e016dc3d3f83b35923b2deeeee53b8d4a6cbdbff3b903f3a7dc506.
def localCycle00010 : Cycle where
  length := 6
  data := {
    node := ![.theta 3, .distance 2 3, .distance 0 2, .distance 2 5, .distance 4 5, .distance 3 4, .theta 3]
    constant := ![3, -1, -1, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 5 0, .triangle 7 0, .triangle 28 1, .triangle 31 0, .corridorLower 3 4]

-- Cycle fingerprint 1268ec3e2ebf6f332ccde9801ec684a3b8bed902aa6eb69a2927b3ee9b877969.
def localCycle00011 : Cycle where
  length := 8
  data := {
    node := ![.distance 2 3, .distance 1 2, .distance 1 6, .distance 1 5, .distance 0 5, .distance 2 5, .distance 3 5, .theta 3, .distance 2 3]
    constant := ![-1, 0, -2, 0, 0, 0, -1, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, false, true, true, true, false, false] }
  origin := ![.triangle 15 0, .triangle 18 2, .gapLower 1 2, .triangle 3 2, .triangle 7 1, .triangle 26 1, .corridorLower 3 5, .corridorUpper 2 3]

-- Cycle fingerprint 142701bc411f5a33d460045ab5fdba14bc3c6d6b7282bb087bf83b395f95c7b5.
def localCycle00012 : Cycle where
  length := 9
  data := {
    node := ![.distance 3 6, .distance 3 5, .theta 3, .distance 2 3, .distance 1 3, .distance 1 4, .distance 0 4, .distance 0 2, .distance 2 6, .distance 3 6]
    constant := ![0, -1, 3, 0, -3, 0, 0, -1, 0]
    coefficient := ![0, 0, 1, 0, 0, 0, 0, 0, 0]
    strict := ![true, false, false, true, false, true, true, false, true] }
  origin := ![.triangle 33 1, .corridorLower 3 5, .corridorUpper 2 3, .triangle 15 2, .gapLower 1 5, .triangle 2 2, .triangle 6 1, .triangle 8 0, .triangle 27 1]

-- Cycle fingerprint 15c31bfc94b63b69abd8e213ac05e06123ed31d472b967a34b0b4d07c9a64018.
def localCycle00013 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 2 3, .distance 0 2, .distance 0 5, .distance 5 6, .distance 4 6, .distance 3 4, .theta 3]
    constant := ![3, -1, 0, -1, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 5 0, .triangle 7 2, .triangle 14 0, .triangle 34 2, .triangle 32 0, .corridorLower 3 4]

-- Cycle fingerprint 174ae4beae2d9e20e73862a9ea70b2cafb792de60539bebc8fbb4ea64e84ab05.
def localCycle00014 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 2, .distance 1 6, .distance 1 5, .distance 0 1, .theta 0, .zero, .theta 3]
    constant := ![3, -1, 0, 0, -3, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 1]
    strict := ![false, false, true, true, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 0, .triangle 18 2, .triangle 24 1, .gapLower 1 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 3]

-- Cycle fingerprint 195b3bf113b6d2785ce0b85483890dea2a05d17bf8c28dc1443c4832ed221bc8.
def localCycle00015 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 2, .distance 2 6, .distance 2 4, .distance 0 2, .distance 2 5, .distance 3 5, .theta 3]
    constant := ![3, -1, -1, 0, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 0, .triangle 18 0, .triangle 29 1, .triangle 6 0, .triangle 7 0, .triangle 26 1, .corridorLower 3 5]

-- Cycle fingerprint 1d54965690f8d84ad59e6b54c1e6de7131135f227dad2cba1b13aa01cad72a7d.
def localCycle00016 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 2, .distance 2 4, .distance 0 2, .distance 2 5, .distance 4 5, .distance 3 4, .theta 3, .distance 2 3, .distance 3 6, .distance 1 3, .distance 1 2]
    constant := ![-1, -1, -1, 0, -1, -1, 3, -1, -1, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, false, false, false] }
  origin := ![.triangle 16 0, .triangle 6 0, .triangle 7 0, .triangle 28 1, .triangle 31 0, .corridorLower 3 4, .corridorUpper 2 3, .triangle 27 0, .triangle 21 0, .gapLower 1 4]

-- Cycle fingerprint 215099e50b8c09d0896f9a05fc27b3571439e481c1b787c6238ff1fac9d07663.
def localCycle00017 : Cycle where
  length := 11
  data := {
    node := ![.distance 4 5, .distance 3 4, .theta 3, .distance 2 3, .distance 2 4, .distance 4 6, .distance 3 6, .distance 0 3, .distance 0 4, .distance 0 2, .distance 2 5, .distance 4 5]
    constant := ![-1, -1, 3, 0, -1, 0, -1, 0, 0, -1, 0]
    coefficient := ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true, false, false, false, false, true] }
  origin := ![.triangle 31 0, .corridorLower 3 4, .corridorUpper 2 3, .triangle 25 2, .triangle 29 0, .triangle 32 2, .triangle 11 0, .gapLower 0 4, .gapLower 0 3, .triangle 7 0, .triangle 28 1]

-- Cycle fingerprint 23080d03c4ec2389d7a9fc1db317215ae5c52562fa1c2cffef3541172bc3bd90.
def localCycle00018 : Cycle where
  length := 12
  data := {
    node := ![.theta 2, .distance 1 2, .distance 2 3, .distance 2 4, .distance 4 6, .distance 3 6, .distance 0 3, .distance 0 2, .distance 2 5, .distance 4 5, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, -1, 0, -1, 0, -1, 0, -1, 0, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, true, false, true, false, false, true] }
  origin := ![.corridorUpper 1 2, .triangle 15 0, .triangle 25 2, .triangle 29 0, .triangle 32 2, .triangle 11 0, .triangle 5 1, .triangle 7 0, .triangle 28 1, .triangle 31 0, .corridorLower 3 4, .thetaNext 2]

-- Cycle fingerprint 235e216223dabba9940592b5965a6532d59184bacd8c18fa115d7e5485c78cef.
def localCycle00019 : Cycle where
  length := 11
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 2, .distance 2 4, .distance 4 6, .distance 3 6, .distance 0 3, .distance 0 2, .distance 2 5, .distance 4 5, .distance 3 4, .theta 3]
    constant := ![3, -1, -1, -1, 0, -1, 0, -1, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, true, false, true, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 0, .triangle 16 0, .triangle 29 0, .triangle 32 2, .triangle 11 0, .triangle 5 1, .triangle 7 0, .triangle 28 1, .triangle 31 0, .corridorLower 3 4]

-- Cycle fingerprint 244d3e343a3a14abae2452b8d8ab72470402ec748c1ed7efd80f9a57abe25509.
def localCycle00020 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 1 2, .distance 2 6, .distance 2 3, .distance 0 2, .distance 2 5, .distance 4 5, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, -1, 0, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, false, false, true] }
  origin := ![.corridorUpper 1 2, .triangle 18 0, .triangle 27 1, .triangle 5 0, .triangle 7 0, .triangle 28 1, .triangle 31 0, .corridorLower 3 4, .thetaNext 2]

-- Cycle fingerprint 26458611282b0488e7a55dfa7e5d5ecd8761c0cdd0c79cc7d8d1903e7d06ad14.
def localCycle00021 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 3, .distance 1 4, .distance 0 1, .theta 1, .zero, .theta 3, .distance 2 3, .distance 1 3]
    constant := ![-2, -1, -2, 0, 0, 3, 0]
    coefficient := ![0, 0, 0, 0, 1, 1, 0]
    strict := ![false, false, false, false, false, false, true] }
  origin := ![.gapLower 1 5, .triangle 2 0, .gapLower 1 0, .thetaLower 1, .thetaUpper 3, .corridorUpper 2 3, .triangle 15 2]

-- Cycle fingerprint 2715b9dbdf9c3607b203585cb18a5d7aeb99062a6b403a5845e38eb8d250c5bc.
def localCycle00022 : Cycle where
  length := 11
  data := {
    node := ![.theta 2, .distance 1 2, .distance 2 3, .distance 2 4, .distance 4 6, .distance 0 4, .distance 0 2, .distance 2 5, .distance 4 5, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, -1, 0, -1, -1, 0, -1, 0, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, false, true, false, false, true] }
  origin := ![.corridorUpper 1 2, .triangle 15 0, .triangle 25 2, .triangle 29 0, .triangle 13 0, .triangle 6 1, .triangle 7 0, .triangle 28 1, .triangle 31 0, .corridorLower 3 4, .thetaNext 2]

-- Cycle fingerprint 276fee3267b4477f54aa680277f99efb8e3d0a126f0e805b42e8b238240b6a46.
def localCycle00023 : Cycle where
  length := 6
  data := {
    node := ![.zero, .theta 3, .distance 2 3, .distance 1 2, .distance 0 1, .theta 1, .zero]
    constant := ![0, 3, -1, -1, -3, 0]
    coefficient := ![1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.thetaUpper 3, .corridorUpper 2 3, .triangle 15 0, .triangle 0 0, .gapLower 1 0, .thetaLower 1]

-- Cycle fingerprint 28242205e92bce83cb15b50a5f55ea9d28c2091d95a04d9ceea914f354fbac8d.
def localCycle00024 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 0 2, .distance 2 5, .distance 4 5, .distance 5 6, .distance 3 5, .distance 3 4, .theta 3]
    constant := ![3, -1, -1, 0, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 5 0, .triangle 7 0, .triangle 28 1, .triangle 34 0, .triangle 33 0, .gapLower 3 1, .corridorLower 3 4]

-- Cycle fingerprint 28a0f012f13fd2c17900066a56372a9a52186b2033019054faede2e2f123223c.
def localCycle00025 : Cycle where
  length := 9
  data := {
    node := ![.distance 2 4, .distance 1 2, .distance 1 6, .distance 0 6, .distance 2 6, .distance 3 6, .distance 4 6, .distance 4 5, .theta 4, .distance 2 4]
    constant := ![-1, -3, 0, 0, 0, 0, 0, -1, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![false, false, true, true, true, true, true, false, false] }
  origin := ![.triangle 16 0, .gapLower 1 3, .triangle 4 2, .triangle 8 1, .triangle 27 1, .triangle 32 1, .triangle 34 1, .corridorLower 4 5, .corridorUpper 2 4]

-- Cycle fingerprint 28db2d48469496830c523a3b9a3a2174dbd009e0dce30c8791bcee645ec4bd70.
def localCycle00026 : Cycle where
  length := 6
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 2, .distance 2 6, .distance 4 6, .distance 3 4, .theta 3]
    constant := ![3, -1, -1, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 0, .triangle 18 0, .triangle 29 1, .triangle 32 0, .corridorLower 3 4]

-- Cycle fingerprint 292bf4752e3f9d66c4a4acc7b04e7720108825aca665bd50d1cb58fc7191fe9d.
def localCycle00027 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 4, .distance 1 6, .distance 1 2, .distance 0 1, .theta 1, .zero, .theta 3, .distance 2 3, .distance 1 3, .distance 1 4]
    constant := ![0, -2, -1, -2, 0, 0, 3, 0, 0]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![true, false, false, false, false, false, false, true, true] }
  origin := ![.triangle 23 2, .gapLower 1 3, .triangle 0 0, .gapLower 1 0, .thetaLower 1, .thetaUpper 3, .corridorUpper 2 3, .triangle 15 2, .triangle 19 2]

-- Cycle fingerprint 2d37c57a75a0d7265407c29f622b3b04da921b3b25ca1a676a87906579a54f56.
def localCycle00028 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 2, .distance 1 6, .distance 0 6, .distance 2 6, .distance 3 6, .distance 3 5, .theta 3]
    constant := ![3, -1, -2, 0, 0, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, true, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 0, .gapLower 1 3, .triangle 4 2, .triangle 8 1, .triangle 27 1, .triangle 33 1, .corridorLower 3 5]

-- Cycle fingerprint 31271dcf2c599d96a6f58c2f10cf7d4e65529e765fde75450b6c62ea34c77f84.
def localCycle00029 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 2, .distance 1 5, .distance 5 6, .distance 4 6, .distance 3 4, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, -1, 0, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false, false, true] }
  origin := ![.corridorUpper 2 3, .triangle 15 0, .triangle 17 2, .triangle 24 0, .triangle 34 2, .triangle 32 0, .triangle 31 0, .corridorLower 4 5, .thetaNext 3]

-- Cycle fingerprint 395bbb54f676e23c3c2c28ae0ca0ee8e7721971a60a101b3c4ed40123a759ca8.
def localCycle00030 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 2 6, .distance 1 2, .distance 2 4, .distance 0 2, .distance 2 5, .distance 3 5, .theta 3]
    constant := ![3, 0, -1, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 27 2, .triangle 18 0, .triangle 16 0, .triangle 6 0, .triangle 7 0, .triangle 26 1, .corridorLower 3 5]

-- Cycle fingerprint 3cec7ebf7a45414217e093be2806b1b3ebd0f5b0c20ffae5882a87c6eef29f34.
def localCycle00031 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 5, .distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 1 2, .distance 1 5]
    constant := ![-3, -1, 0, 0, 3, -1, 0]
    coefficient := ![0, 0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, false, false, false, true] }
  origin := ![.gapLower 1 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 15 0, .triangle 17 2]

-- Cycle fingerprint 3eb82ab253e6ffba7c19c051ab285ec71bff3594e7c36e96027b2c3441274714.
def localCycle00032 : Cycle where
  length := 8
  data := {
    node := ![.distance 2 3, .distance 1 2, .distance 1 6, .distance 1 5, .distance 0 1, .theta 1, .zero, .theta 3, .distance 2 3]
    constant := ![-1, 0, 0, -1, -3, 0, 0, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 1]
    strict := ![false, true, true, false, false, false, false, false] }
  origin := ![.triangle 15 0, .triangle 18 2, .triangle 24 1, .triangle 3 0, .gapLower 1 0, .thetaLower 1, .thetaUpper 3, .corridorUpper 2 3]

-- Cycle fingerprint 3ecc2b1f0a2dedfbad68e7d33e0b5208fc80474ae49c8b7512466d8402511260.
def localCycle00033 : Cycle where
  length := 4
  data := {
    node := ![.distance 1 2, .distance 1 5, .distance 5 6, .distance 2 6, .distance 1 2]
    constant := ![-3, 2, 0, -1]
    coefficient := ![0, 0, 0, 0]
    strict := ![false, true, false, false] }
  origin := ![.gapLower 1 2, .gapUpper 5 5, .gapLower 6 5, .triangle 18 0]

-- Cycle fingerprint 3fce33f0a4ef6d2ed42b85353910300024b71bce38fe09901120ece5ccf5628b.
def localCycle00034 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 2, .distance 2 4, .distance 4 5, .distance 5 6, .distance 3 5, .distance 3 4, .theta 3]
    constant := ![3, -1, -1, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 0, .triangle 16 0, .triangle 28 0, .triangle 34 0, .triangle 33 0, .gapLower 3 1, .corridorLower 3 4]

-- Cycle fingerprint 404acaebf7ab865460b9842c408858c772760167e0e52d4eb310f187c1209308.
def localCycle00035 : Cycle where
  length := 11
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 1 4, .distance 4 6, .distance 2 4, .distance 0 2, .distance 2 5, .distance 4 5, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, 0, 0, -1, -1, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, false, false, true, false, false, true] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 19 2, .triangle 23 0, .triangle 29 0, .triangle 6 0, .triangle 7 0, .triangle 28 1, .triangle 31 0, .corridorLower 3 4, .thetaNext 2]

-- Cycle fingerprint 40748c204bbe8a93529bf2dd723811b704508ed2fe15ffdd41667abe7eee1a7c.
def localCycle00036 : Cycle where
  length := 10
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 2, .distance 1 4, .distance 4 6, .distance 2 4, .distance 0 2, .distance 2 5, .distance 4 5, .distance 3 4, .theta 3]
    constant := ![3, -1, 0, -1, -1, 0, -1, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, true, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 0, .triangle 16 2, .triangle 23 0, .triangle 29 0, .gapLower 2 2, .triangle 7 0, .triangle 28 1, .triangle 31 0, .corridorLower 3 4]

-- Cycle fingerprint 454ae938c64c1a87802adca637315959fcf4267f7b8ef4f000da48ddca23119a.
def localCycle00037 : Cycle where
  length := 10
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 2, .distance 1 4, .distance 1 5, .distance 5 6, .distance 2 6, .distance 0 2, .distance 2 5, .distance 3 5, .theta 3]
    constant := ![3, -1, 0, 0, -1, 0, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, true, false, false, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 0, .triangle 16 2, .triangle 22 2, .triangle 24 0, .triangle 30 2, .triangle 8 0, .triangle 7 0, .triangle 26 1, .corridorLower 3 5]

-- Cycle fingerprint 45638d4861c71386509a41b525d5f4c594699ebc573b8fc1df49f0ecea85be66.
def localCycle00038 : Cycle where
  length := 11
  data := {
    node := ![.theta 2, .distance 1 2, .distance 2 3, .distance 2 4, .distance 0 2, .distance 2 5, .distance 4 5, .distance 5 6, .distance 3 5, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, -1, 0, -1, -1, 0, -1, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, false, false, false, false, true] }
  origin := ![.corridorUpper 1 2, .triangle 15 0, .triangle 25 2, .triangle 6 0, .triangle 7 0, .triangle 28 1, .triangle 34 0, .triangle 33 0, .gapLower 3 1, .corridorLower 3 4, .thetaNext 2]

-- Cycle fingerprint 477f06811639247f4ace17b820515b404dd5c22da64ccfb6c37b685b8e222523.
def localCycle00039 : Cycle where
  length := 13
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 1 4, .distance 1 5, .distance 5 6, .distance 4 6, .distance 2 4, .distance 0 2, .distance 2 5, .distance 4 5, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, 0, 0, 0, -1, 0, -1, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, true, false, false, false, true, false, false, true] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 19 2, .triangle 22 2, .triangle 24 0, .triangle 34 2, .triangle 29 0, .triangle 6 0, .triangle 7 0, .triangle 28 1, .triangle 31 0, .corridorLower 3 4, .thetaNext 2]

-- Cycle fingerprint 4786db9e3dc8f30aa060f95fd08d7c0cd6b7a591500e447d417146ca52dccf07.
def localCycle00040 : Cycle where
  length := 11
  data := {
    node := ![.distance 3 6, .distance 4 6, .distance 4 5, .theta 4, .theta 3, .distance 2 3, .distance 1 3, .distance 1 4, .distance 1 2, .distance 0 2, .distance 2 6, .distance 3 6]
    constant := ![0, 0, -1, 0, 3, 0, -2, -2, 0, -1, 0]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0]
    strict := ![true, true, false, true, false, true, false, false, true, false, true] }
  origin := ![.triangle 32 1, .triangle 34 1, .corridorLower 4 5, .thetaNext 3, .corridorUpper 2 3, .triangle 15 2, .gapLower 1 5, .gapLower 1 4, .triangle 0 2, .triangle 8 0, .triangle 27 1]

-- Cycle fingerprint 47c4d8c5c15408b332ceb028888257c2b4fe09fad57366a8ebd21f786b59ac1b.
def localCycle00041 : Cycle where
  length := 10
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 2, .distance 2 4, .distance 4 6, .distance 0 4, .distance 0 2, .distance 2 5, .distance 4 5, .distance 3 4, .theta 3]
    constant := ![3, -1, -1, -1, -1, 0, -1, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, true, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 0, .triangle 16 0, .triangle 29 0, .triangle 13 0, .triangle 6 1, .triangle 7 0, .triangle 28 1, .triangle 31 0, .corridorLower 3 4]

-- Cycle fingerprint 49b057bd3589d61b8f23a9c198ac4bdabc11ce5d86a60d8b626edb3155cdbff3.
def localCycle00042 : Cycle where
  length := 10
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 2, .distance 2 4, .distance 0 2, .distance 2 5, .distance 3 5, .distance 5 6, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, -1, -1, 0, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, false, false, true] }
  origin := ![.corridorUpper 2 3, .triangle 15 0, .triangle 16 0, .gapLower 2 3, .triangle 7 0, .triangle 26 1, .triangle 33 0, .triangle 34 0, .corridorLower 4 5, .thetaNext 3]

-- Cycle fingerprint 4a89c7c97e813c715424c4690d8ff6ebee9c45a314ca966efe9d426d24969f30.
def localCycle00043 : Cycle where
  length := 9
  data := {
    node := ![.distance 2 3, .distance 1 3, .distance 1 4, .distance 1 2, .distance 1 5, .distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3]
    constant := ![0, -2, 0, 0, -2, -1, 0, 0, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1, 1]
    strict := ![true, false, true, true, false, false, false, false, false] }
  origin := ![.triangle 15 2, .gapLower 1 5, .triangle 16 1, .triangle 17 2, .gapLower 1 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3]

-- Cycle fingerprint 4a9f7de645f0d7d90f6e919d04cee3613dccfb4e87109c85e9d1d10b2d5d0be7.
def localCycle00044 : Cycle where
  length := 10
  data := {
    node := ![.theta 2, .distance 1 2, .distance 2 3, .distance 2 6, .distance 2 4, .distance 0 2, .distance 2 5, .distance 4 5, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, -1, 0, 0, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, true, false, false, true] }
  origin := ![.corridorUpper 1 2, .triangle 15 0, .triangle 27 2, .triangle 29 1, .triangle 6 0, .triangle 7 0, .triangle 28 1, .triangle 31 0, .corridorLower 3 4, .thetaNext 2]

-- Cycle fingerprint 4c3a4f8f1142b0282d9f13984be4a5807475b3d3a5d73376461b9d37f12b8c57.
def localCycle00045 : Cycle where
  length := 5
  data := {
    node := ![.distance 1 2, .distance 1 5, .distance 5 6, .distance 4 6, .distance 2 4, .distance 1 2]
    constant := ![0, 2, 0, -1, -1]
    coefficient := ![0, 0, 0, 0, 0]
    strict := ![true, true, true, false, false] }
  origin := ![.triangle 17 2, .gapUpper 5 5, .triangle 34 2, .triangle 29 0, .triangle 16 0]

-- Cycle fingerprint 4c7038f2c39a607a9b3baf12d08a5ea2c1847bb5ad46906fb0c704c3355639f3.
def localCycle00046 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 2, .distance 2 4, .distance 0 2, .distance 0 5, .distance 5 6, .distance 4 5, .distance 3 4, .theta 3]
    constant := ![3, -1, -1, -1, 0, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 0, .triangle 16 0, .triangle 6 0, .triangle 7 2, .triangle 14 0, .triangle 34 0, .triangle 31 0, .corridorLower 3 4]

-- Cycle fingerprint 4cd936fc77d9ad06076a3bfe9bf90c456aad9e6c80365592be8cda4e7e03bc45.
def localCycle00047 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 2, .distance 2 6, .distance 3 6, .distance 0 3, .distance 3 4, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, -1, -1, 0, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, false, true] }
  origin := ![.corridorUpper 2 3, .triangle 15 0, .triangle 18 0, .triangle 27 1, .triangle 11 0, .triangle 9 0, .triangle 31 0, .corridorLower 4 5, .thetaNext 3]

-- Cycle fingerprint 50a76d2bb01e85381c09072e5797636937b53d1757e4a01afe5315bb1b9f464a.
def localCycle00048 : Cycle where
  length := 3
  data := {
    node := ![.distance 2 4, .distance 1 4, .distance 1 2, .distance 2 4]
    constant := ![0, -3, 2]
    coefficient := ![0, 0, 0]
    strict := ![false, false, true] }
  origin := ![.gapLower 4 5, .gapLower 1 4, .gapUpper 2 4]

-- Cycle fingerprint 5104451f71c4f8f8f5546343afa1405ccd0d77d8e41dc8ca493ae8fa8960b78c.
def localCycle00049 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 2, .distance 2 6, .distance 0 2, .distance 2 5, .distance 4 5, .distance 3 4, .theta 3]
    constant := ![3, -1, -1, -1, -1, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 0, .triangle 18 0, .triangle 8 0, .triangle 7 0, .triangle 28 1, .triangle 31 0, .corridorLower 3 4]

-- Cycle fingerprint 5137a82ffc17598fb6edfd9b9f44a8f9635c10dbfbb4562bc3846c752a11b2f9.
def localCycle00050 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 0 2, .distance 2 5, .distance 3 5, .distance 5 6, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, -1, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, true] }
  origin := ![.corridorUpper 2 3, .triangle 5 0, .triangle 7 0, .triangle 26 1, .triangle 33 0, .triangle 34 0, .corridorLower 4 5, .thetaNext 3]

-- Cycle fingerprint 524f3bd11ac26f94071efb0485efadc1be34abf7fab6cc40780151b99274ca8b.
def localCycle00051 : Cycle where
  length := 11
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 2, .distance 2 4, .distance 0 2, .distance 2 5, .distance 3 5, .distance 4 5, .distance 5 6, .theta 5, .theta 4, .theta 3]
    constant := ![3, -1, -1, -1, -1, 0, 0, -1, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, false, false, true, true] }
  origin := ![.corridorUpper 2 3, .triangle 15 0, .triangle 16 0, .triangle 6 0, .triangle 7 0, .triangle 26 1, .triangle 31 1, .triangle 34 0, .corridorLower 5 6, .thetaNext 4, .thetaNext 3]

-- Cycle fingerprint 533b6ca70f330e41cfefb85aa914ab62e9f73a08e7d1969255fb952fee976544.
def localCycle00052 : Cycle where
  length := 9
  data := {
    node := ![.distance 3 4, .distance 4 6, .distance 4 5, .theta 4, .theta 3, .theta 2, .theta 1, .distance 1 3, .distance 0 3, .distance 3 4]
    constant := ![-1, 0, -1, 0, 0, 0, 1, 0, -1]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 0, 0]
    strict := ![false, true, false, true, true, true, false, true, false] }
  origin := ![.triangle 32 0, .triangle 34 1, .corridorLower 4 5, .thetaNext 3, .thetaNext 2, .thetaNext 1, .gapLower 1 6, .triangle 1 2, .triangle 9 0]

-- Cycle fingerprint 53e8df4569da00cada0978e754a3b265cfd897c7249653147833a1f4d1e47a07.
def localCycle00053 : Cycle where
  length := 13
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 2 3, .distance 1 2, .distance 2 4, .distance 0 2, .distance 2 5, .distance 3 5, .distance 4 5, .theta 4, .zero]
    constant := ![0, 3, 0, 0, -1, -1, -1, -1, -1, 0, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, false, false, true, true, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 27 0, .triangle 15 0, .triangle 16 0, .triangle 6 0, .triangle 7 0, .triangle 26 1, .triangle 31 1, .corridorLower 4 5, .thetaLower 4]

-- Cycle fingerprint 54824e66c60884b252fc09d00aec9db1ee9182327a7bc84e099bc443eda182a5.
def localCycle00054 : Cycle where
  length := 12
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 1 4, .distance 1 5, .distance 5 6, .distance 2 6, .distance 0 2, .distance 2 5, .distance 4 5, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, 0, 0, 0, -1, 0, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, true, false, false, true, false, false, true] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 19 2, .triangle 22 2, .triangle 24 0, .triangle 30 2, .triangle 8 0, .triangle 7 0, .triangle 28 1, .triangle 31 0, .corridorLower 3 4, .thetaNext 2]

-- Cycle fingerprint 553a0730f2d5a52e5899fe10cb6801c379396ef82b0a02b7a1a5714435fdb317.
def localCycle00055 : Cycle where
  length := 9
  data := {
    node := ![.distance 2 3, .distance 1 3, .distance 1 4, .distance 1 2, .distance 1 6, .distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3]
    constant := ![0, -2, 0, -2, -1, -1, 0, 0, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1, 1]
    strict := ![true, false, true, false, false, false, false, false, false] }
  origin := ![.triangle 15 2, .gapLower 1 5, .triangle 16 1, .gapLower 1 3, .triangle 4 0, .corridorLower 0 1, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3]

-- Cycle fingerprint 57d860c365e29b08f4e707fadbe638de7fd664601ea685e3f5bf14d61c6e0948.
def localCycle00056 : Cycle where
  length := 9
  data := {
    node := ![.distance 2 3, .distance 1 3, .distance 1 4, .distance 1 6, .distance 0 6, .distance 0 2, .distance 2 5, .distance 3 5, .theta 3, .distance 2 3]
    constant := ![0, -2, -2, 0, 0, -1, 0, -1, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![true, false, false, true, true, false, true, false, false] }
  origin := ![.triangle 15 2, .gapLower 1 5, .gapLower 1 4, .triangle 4 2, .triangle 8 1, .triangle 7 0, .triangle 26 1, .corridorLower 3 5, .corridorUpper 2 3]

-- Cycle fingerprint 591e01ebcda5fa868d136918eae88b4cb64d55fe3779428a5d02dd575b92ff1f.
def localCycle00057 : Cycle where
  length := 9
  data := {
    node := ![.distance 2 3, .distance 3 6, .distance 1 3, .distance 1 2, .distance 2 4, .distance 0 2, .distance 2 5, .distance 3 5, .theta 3, .distance 2 3]
    constant := ![-1, -1, 0, -1, -1, -1, 0, -1, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![false, false, false, false, false, false, true, false, false] }
  origin := ![.triangle 27 0, .triangle 21 0, .gapLower 1 4, .triangle 16 0, .triangle 6 0, .triangle 7 0, .triangle 26 1, .corridorLower 3 5, .corridorUpper 2 3]

-- Cycle fingerprint 598f2442cce5d6b47904f3804079c3ef0138e36125a527c1e57ab71548a1d7ed.
def localCycle00058 : Cycle where
  length := 10
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 3 6, .distance 2 3, .distance 0 2, .distance 2 5, .distance 4 5, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, 0, -1, -1, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, true, false, false, true] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 21 0, .triangle 27 0, .triangle 5 0, .triangle 7 0, .triangle 28 1, .triangle 31 0, .corridorLower 3 4, .thetaNext 2]

-- Cycle fingerprint 5fe643747ad66ead08adda477ade93c7976aaadce7576cbeaeae5dfb389202c0.
def localCycle00059 : Cycle where
  length := 3
  data := {
    node := ![.distance 5 6, .distance 1 6, .distance 1 5, .distance 5 6]
    constant := ![0, -3, 2]
    coefficient := ![0, 0, 0]
    strict := ![false, false, true] }
  origin := ![.gapLower 6 5, .gapLower 1 2, .gapUpper 5 5]

-- Cycle fingerprint 606f07878008c78de53138b2c5e66e356665e1ea249dddbfa301a6223580e11c.
def localCycle00060 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 6, .distance 1 5, .distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 1 3, .distance 1 4, .distance 1 2, .distance 1 6]
    constant := ![0, -2, -1, 0, 0, 3, 0, 0, -2, 0]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![true, false, false, false, false, false, true, true, false, true] }
  origin := ![.triangle 24 1, .gapLower 1 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 15 2, .triangle 19 2, .gapLower 1 4, .triangle 18 2]

-- Cycle fingerprint 62cb2fb27b56c9048c4d4652486267fdde9dba4f70bb5222ad7c7dc0817d79d0.
def localCycle00061 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 3, .distance 3 6, .distance 0 3, .distance 0 2, .distance 2 5, .distance 4 5, .distance 3 4, .theta 3]
    constant := ![3, 0, -1, -1, 0, -1, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, false, true, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 2, .triangle 21 0, .triangle 11 0, .triangle 5 1, .triangle 7 0, .triangle 28 1, .triangle 31 0, .corridorLower 3 4]

-- Cycle fingerprint 62d723a68c84995972e80f2e542e1dcab7b29ece90db96d52673ca4804d6499d.
def localCycle00062 : Cycle where
  length := 8
  data := {
    node := ![.distance 1 3, .distance 1 4, .distance 0 4, .distance 0 2, .distance 2 5, .distance 3 5, .theta 3, .distance 2 3, .distance 1 3]
    constant := ![-3, 0, 0, -1, 0, -1, 3, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 0]
    strict := ![false, true, true, false, true, false, false, true] }
  origin := ![.gapLower 1 5, .triangle 2 2, .triangle 6 1, .triangle 7 0, .triangle 26 1, .corridorLower 3 5, .corridorUpper 2 3, .triangle 15 2]

-- Cycle fingerprint 66dc02b1420154ac50aa750486f2b99010e37a9abdb5115ea9f978d9ed583cf7.
def localCycle00063 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 2 3, .distance 0 2, .distance 2 5, .distance 5 6, .distance 4 5, .distance 3 4, .theta 3]
    constant := ![3, -1, -1, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 5 0, .triangle 7 0, .triangle 30 0, .triangle 34 0, .triangle 31 0, .corridorLower 3 4]

-- Cycle fingerprint 6b7e3d0ca0709f0da62fac9d4f618ed40608f4ea63cd5e8cf24eb3249d936bf6.
def localCycle00064 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 6, .distance 0 3, .distance 3 4, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true] }
  origin := ![.corridorUpper 2 3, .triangle 27 0, .triangle 11 0, .triangle 9 0, .triangle 31 0, .corridorLower 4 5, .thetaNext 3]

-- Cycle fingerprint 6dea7ea444f48258e26d9f0bb94f6101c67e9abb8d64c97011e3aa12cc307c15.
def localCycle00065 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 2, .distance 1 6, .distance 1 5, .distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 1 3, .distance 1 4, .distance 1 2]
    constant := ![0, -2, -1, -1, 0, 0, 3, 0, -2, 0]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![true, false, false, false, false, false, false, true, false, true] }
  origin := ![.triangle 18 2, .gapLower 1 2, .triangle 3 0, .corridorLower 0 1, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 15 2, .gapLower 1 5, .triangle 16 1]

-- Cycle fingerprint 71db307b1e505be439c0b55109f3ac2e7589965121c6bcd9a2b41663c121013c.
def localCycle00066 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 2, .distance 2 4, .distance 0 2, .distance 0 5, .distance 5 6, .distance 4 6, .distance 3 4, .theta 3]
    constant := ![3, -1, -1, -1, 0, -1, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, true, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 0, .triangle 16 0, .triangle 6 0, .triangle 7 2, .triangle 14 0, .triangle 34 2, .triangle 32 0, .corridorLower 3 4]

-- Cycle fingerprint 720b7293df6542c5ce01e995317d8ea59d8e96c64df34e81da474a7eb39e6bd3.
def localCycle00067 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 3, .distance 3 6, .distance 0 3, .distance 3 4, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, 0, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false, true] }
  origin := ![.corridorUpper 2 3, .triangle 15 2, .triangle 21 0, .triangle 11 0, .triangle 9 0, .triangle 31 0, .corridorLower 4 5, .thetaNext 3]

-- Cycle fingerprint 72532da4118e8d2636e1f54b00dfecd1d918e1bed54bd0fe2d23ac04757b149b.
def localCycle00068 : Cycle where
  length := 8
  data := {
    node := ![.theta 1, .zero, .theta 3, .distance 2 3, .distance 1 2, .distance 1 6, .distance 1 5, .distance 0 1, .theta 1]
    constant := ![0, 0, 3, -1, -2, 0, -1, -2]
    coefficient := ![0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, false] }
  origin := ![.thetaLower 1, .thetaUpper 3, .corridorUpper 2 3, .triangle 15 0, .gapLower 1 3, .triangle 24 1, .triangle 3 0, .gapLower 1 0]

-- Cycle fingerprint 7277df3bc52ce3ba4fcf1c9e5cd17b8d6dcee7a43ddd21f19821a70bf3a265ae.
def localCycle00069 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 2, .distance 1 5, .distance 0 1, .theta 1, .zero, .theta 3, .distance 2 3, .distance 1 2]
    constant := ![-2, -1, -2, 0, 0, 3, -1]
    coefficient := ![0, 0, 0, 0, 1, 1, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 1 2, .triangle 3 0, .gapLower 1 0, .thetaLower 1, .thetaUpper 3, .corridorUpper 2 3, .triangle 15 0]

-- Cycle fingerprint 786c56090b0f94fe60ab615e72b384e33270d08b16d0e582b752df215ae23c73.
def localCycle00070 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 2, .distance 2 4, .distance 4 5, .distance 3 4, .distance 3 6, .theta 3]
    constant := ![3, -1, -1, -1, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 0, .triangle 16 0, .triangle 28 0, .triangle 31 0, .triangle 32 2, .gapLower 3 0]

-- Cycle fingerprint 78dfbe0f58ac8955883afebc49515d730009a832c2a6217b27bd4a1c6cb93eb4.
def localCycle00071 : Cycle where
  length := 9
  data := {
    node := ![.distance 2 4, .distance 4 6, .distance 0 4, .distance 0 2, .distance 2 5, .distance 4 5, .distance 3 4, .theta 3, .distance 2 3, .distance 2 4]
    constant := ![-1, -1, 0, -1, 0, -1, -1, 3, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1, 0]
    strict := ![false, false, false, false, true, false, false, false, true] }
  origin := ![.triangle 29 0, .triangle 13 0, .gapLower 0 3, .triangle 7 0, .triangle 28 1, .triangle 31 0, .corridorLower 3 4, .corridorUpper 2 3, .triangle 25 2]

-- Cycle fingerprint 7a09075281b67dba3355668d0d06894ca6dedab756edcd5969d463914f0480a4.
def localCycle00072 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 3, .distance 1 4, .distance 0 4, .distance 4 6, .distance 3 4, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, 0, 0, 0, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, false, false, false, true] }
  origin := ![.corridorUpper 2 3, .triangle 15 2, .triangle 19 2, .triangle 2 2, .triangle 13 0, .triangle 32 0, .triangle 31 0, .corridorLower 4 5, .thetaNext 3]

-- Cycle fingerprint 7e243d04fe835e8fab2662693f27a34f052d337120e445302aa900f4caa4d0d7.
def localCycle00073 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 2, .distance 1 6, .distance 1 5, .distance 0 1, .theta 1, .zero, .theta 3]
    constant := ![3, -1, 0, 0, -2, -2, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 1]
    strict := ![false, false, true, true, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 0, .triangle 18 2, .triangle 24 1, .gapLower 1 1, .gapLower 1 0, .thetaLower 1, .thetaUpper 3]

-- Cycle fingerprint 7e9d356cbf0ef5eb33fabb533c687068e1e5034bd6516ea77e88fa110222a146.
def localCycle00074 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 2 4, .distance 0 2, .distance 2 5, .distance 4 5, .distance 3 4, .distance 4 6, .theta 4]
    constant := ![3, -1, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false] }
  origin := ![.corridorUpper 2 4, .triangle 6 0, .triangle 7 0, .triangle 28 1, .triangle 31 0, .triangle 32 0, .corridorLower 4 6]

-- Cycle fingerprint 7efe143f04fd10756c7df8a9921f7fb988bcb8e3725b0a55743a13dc9fdba645.
def localCycle00075 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 2 3, .distance 0 2, .distance 2 6, .distance 4 6, .distance 4 5, .distance 3 4, .theta 3]
    constant := ![3, -1, -1, 0, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 5 0, .triangle 8 0, .triangle 29 1, .triangle 34 1, .triangle 31 0, .corridorLower 3 4]

-- Cycle fingerprint 83d7833d4fa529850f4b6584334297ca64b3735460b3e2fd07668b743988d58d.
def localCycle00076 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 2, .distance 2 6, .distance 2 5, .theta 2, .theta 1, .distance 1 3, .distance 1 4, .distance 0 4, .distance 0 2]
    constant := ![-1, 0, -1, 0, 2, -2, 0, 0]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![false, true, false, true, false, false, true, true] }
  origin := ![.triangle 8 0, .triangle 30 1, .corridorLower 2 5, .thetaNext 1, .gapLower 1 6, .gapLower 1 5, .triangle 2 2, .triangle 6 1]

-- Cycle fingerprint 854b8ae7c29ae1395e314e360c1dd350253cdb4ed8219734b4d730ce26b3490d.
def localCycle00077 : Cycle where
  length := 8
  data := {
    node := ![.distance 1 2, .distance 0 2, .distance 2 5, .theta 2, .theta 1, .distance 1 3, .distance 1 4, .distance 1 6, .distance 1 2]
    constant := ![0, -1, -1, 0, 2, 0, 0, -2]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![true, false, false, true, false, true, true, false] }
  origin := ![.triangle 0 2, .triangle 7 0, .corridorLower 2 5, .thetaNext 1, .gapLower 1 6, .triangle 19 2, .triangle 23 2, .gapLower 1 3]

-- Cycle fingerprint 8a61f33122fa6afa1d2d58c1e58b6b6738e5cd40b36f66ac065f6e2c62c520c6.
def localCycle00078 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 2, .distance 2 6, .distance 2 5, .theta 2, .theta 1, .distance 1 3, .distance 1 4, .distance 1 2, .distance 0 2]
    constant := ![-1, 0, -1, 0, 2, 0, -2, 0]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![false, true, false, true, false, true, false, true] }
  origin := ![.triangle 8 0, .triangle 30 1, .corridorLower 2 5, .thetaNext 1, .gapLower 1 6, .triangle 19 2, .gapLower 1 4, .triangle 0 2]

-- Cycle fingerprint 8bec11efce61b989b8f77d195fb599c0a237fc98bcede2d665147ba17ddef1aa.
def localCycle00079 : Cycle where
  length := 6
  data := {
    node := ![.theta 3, .distance 2 3, .distance 0 2, .distance 0 5, .distance 5 6, .distance 3 5, .theta 3]
    constant := ![3, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 5 0, .triangle 7 2, .triangle 14 0, .triangle 33 0, .corridorLower 3 5]

-- Cycle fingerprint 8d75599d7c07b21b98b2d287b1e918ee16d11210a70b4721dbe380541425379e.
def localCycle00080 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 2, .distance 2 6, .distance 0 6, .distance 4 6, .distance 3 4, .theta 3]
    constant := ![3, -1, -1, 0, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 0, .triangle 18 0, .triangle 8 2, .triangle 13 1, .triangle 32 0, .corridorLower 3 4]

-- Cycle fingerprint 9135dff4dc4e5aa5632a2f72e501c488e7d2a6cf645942953151c1d1d84196ec.
def localCycle00081 : Cycle where
  length := 11
  data := {
    node := ![.distance 2 5, .distance 3 5, .distance 4 5, .theta 4, .theta 3, .distance 2 3, .distance 1 3, .distance 1 4, .distance 1 6, .distance 1 2, .distance 0 2, .distance 2 5]
    constant := ![0, 0, -1, 0, 3, 0, -2, 0, -2, 0, -1]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0]
    strict := ![true, true, false, true, false, true, false, true, false, true, false] }
  origin := ![.triangle 26 1, .triangle 31 1, .corridorLower 4 5, .thetaNext 3, .corridorUpper 2 3, .triangle 15 2, .gapLower 1 5, .triangle 23 2, .gapLower 1 3, .triangle 0 2, .triangle 7 0]

-- Cycle fingerprint 91d88dcfee1f1a31487e943f60ee180f5cd887e6bd8379e93fe721ba387c24c9.
def localCycle00082 : Cycle where
  length := 7
  data := {
    node := ![.theta 1, .distance 1 3, .distance 1 4, .distance 0 4, .distance 0 2, .distance 2 5, .theta 2, .theta 1]
    constant := ![2, -2, 0, 0, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, true] }
  origin := ![.gapLower 1 6, .gapLower 1 5, .triangle 2 2, .triangle 6 1, .triangle 7 0, .corridorLower 2 5, .thetaNext 1]

-- Cycle fingerprint 9455f2e2a3118ca25aa43b452cdf41458810acf061bbdeea5cdefd109616c1be.
def localCycle00083 : Cycle where
  length := 11
  data := {
    node := ![.distance 3 5, .distance 4 5, .theta 4, .theta 3, .distance 2 3, .distance 1 3, .distance 1 4, .distance 1 6, .distance 0 6, .distance 0 2, .distance 2 5, .distance 3 5]
    constant := ![0, -1, 0, 3, 0, 0, -3, 0, 0, -1, 0]
    coefficient := ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![true, false, true, false, true, true, false, true, true, false, true] }
  origin := ![.triangle 31 1, .corridorLower 4 5, .thetaNext 3, .corridorUpper 2 3, .triangle 15 2, .triangle 19 2, .gapLower 1 4, .triangle 4 2, .triangle 8 1, .triangle 7 0, .triangle 26 1]

-- Cycle fingerprint 94acef7eba7533cff3adf6b26bd8810ba7128cc7604d16ce9ab0c02e578270fd.
def localCycle00084 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 2, .distance 2 4, .distance 2 6, .distance 0 2, .distance 2 5, .distance 3 5, .theta 3]
    constant := ![3, -1, -1, 0, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 0, .triangle 16 0, .triangle 29 2, .triangle 8 0, .triangle 7 0, .triangle 26 1, .corridorLower 3 5]

-- Cycle fingerprint 95bf7de5b22604ea0eddaec5abad8f3f1757cfb3efe9fc8046f0b1fbfdfef4f0.
def localCycle00085 : Cycle where
  length := 11
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 2, .distance 1 4, .distance 1 5, .distance 5 6, .distance 2 6, .distance 0 2, .distance 2 5, .distance 4 5, .distance 3 4, .theta 3]
    constant := ![3, -1, 0, 0, -1, 0, -1, -1, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, true, false, false, true, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 0, .triangle 16 2, .triangle 22 2, .triangle 24 0, .triangle 30 2, .triangle 8 0, .triangle 7 0, .triangle 28 1, .triangle 31 0, .corridorLower 3 4]

-- Cycle fingerprint 97de5cedf7913a10e8877f649fbaf13a90c5ff9c623d319d3d5b9bff4d65553e.
def localCycle00086 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 6, .distance 0 3, .distance 0 2, .distance 2 5, .distance 4 5, .distance 3 4, .theta 3]
    constant := ![3, -1, -1, 0, -1, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 27 0, .triangle 11 0, .triangle 5 1, .triangle 7 0, .triangle 28 1, .triangle 31 0, .corridorLower 3 4]

-- Cycle fingerprint 9b13e5c74519887157e2f106495705cd9ff859c60f648cab4dbbaa46203858c2.
def localCycle00087 : Cycle where
  length := 12
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 2, .distance 1 4, .distance 1 5, .distance 5 6, .distance 4 6, .distance 2 4, .distance 0 2, .distance 2 5, .distance 4 5, .distance 3 4, .theta 3]
    constant := ![3, -1, 0, 0, -1, 0, -1, 0, -1, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, true, false, false, false, true, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 0, .triangle 16 2, .triangle 22 2, .triangle 24 0, .triangle 34 2, .triangle 29 0, .gapLower 2 2, .triangle 7 0, .triangle 28 1, .triangle 31 0, .corridorLower 3 4]

-- Cycle fingerprint 9cf73b6b1ff487ef9b6c1756b14f1f3863bfcf8463087fc6bddaaf2bc7f44162.
def localCycle00088 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 2, .distance 1 5, .distance 5 6, .distance 4 5, .distance 3 4, .theta 3]
    constant := ![3, -1, 0, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 0, .triangle 17 2, .triangle 24 0, .triangle 34 0, .triangle 31 0, .corridorLower 3 4]

-- Cycle fingerprint a3dfa395fef333ee966e8859e56aef1977d6ee911e5155580c45bd9aca19fe27.
def localCycle00089 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 2, .distance 1 5, .distance 5 6, .distance 4 6, .distance 3 4, .theta 3]
    constant := ![3, -1, 0, -1, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 0, .triangle 17 2, .triangle 24 0, .triangle 34 2, .triangle 32 0, .corridorLower 3 4]

-- Cycle fingerprint ad2f76d02617eadb6fc5ae9b1ecc129ecee73c14b94bfa26dd0b50762b098b04.
def localCycle00090 : Cycle where
  length := 6
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 2, .distance 2 4, .distance 4 6, .distance 3 4, .theta 3]
    constant := ![3, -1, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 0, .triangle 16 0, .triangle 29 0, .triangle 32 0, .corridorLower 3 4]

-- Cycle fingerprint ada3780fb7afacaad062cbc34dcb2f3b29362d87ae0c7413a923f60fa64cb9d7.
def localCycle00091 : Cycle where
  length := 11
  data := {
    node := ![.theta 2, .distance 1 2, .distance 2 3, .distance 2 4, .distance 0 2, .distance 2 5, .distance 4 5, .distance 3 4, .distance 4 6, .theta 4, .theta 3, .theta 2]
    constant := ![3, -1, 0, -1, -1, 0, -1, -1, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, false, false, false, true, true] }
  origin := ![.corridorUpper 1 2, .triangle 15 0, .triangle 25 2, .triangle 6 0, .triangle 7 0, .triangle 28 1, .triangle 31 0, .triangle 32 0, .corridorLower 4 6, .thetaNext 3, .thetaNext 2]

-- Cycle fingerprint b11a600cad92772d9e96a251cc6ab1421ec8f2371bdc8ce6dd7fd6703e57ad30.
def localCycle00092 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 2 6, .distance 1 2, .distance 2 3, .distance 3 4, .distance 4 5, .theta 4, .zero]
    constant := ![0, 3, 0, 0, 0, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, true, false, false, false, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 27 2, .triangle 18 0, .triangle 15 0, .triangle 25 0, .triangle 31 0, .corridorLower 4 5, .thetaLower 4]

-- Cycle fingerprint b3784e9cec4cb99a348090cfe8c966185e3e8a319727119f1db20bd1840d76b7.
def localCycle00093 : Cycle where
  length := 11
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 2, .distance 1 4, .distance 1 5, .distance 5 6, .distance 4 6, .distance 2 4, .distance 0 2, .distance 2 5, .distance 3 5, .theta 3]
    constant := ![3, -1, 0, 0, -1, 0, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, true, false, false, false, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 0, .triangle 16 2, .triangle 22 2, .triangle 24 0, .triangle 34 2, .triangle 29 0, .triangle 6 0, .triangle 7 0, .triangle 26 1, .corridorLower 3 5]

-- Cycle fingerprint b88494372b747508db08c7de6f861a9168177e4cdbf5be052c2fd319de488b78.
def localCycle00094 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 3 6, .distance 2 3, .distance 1 2, .distance 2 4, .distance 0 2, .distance 2 5, .distance 4 5, .distance 3 4, .theta 3]
    constant := ![4, -1, -1, -1, -1, -1, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, false, false] }
  origin := ![.gapLower 3 6, .triangle 27 0, .triangle 15 0, .triangle 16 0, .triangle 6 0, .triangle 7 0, .triangle 28 1, .triangle 31 0, .corridorLower 3 4]

-- Cycle fingerprint b8add20e989d34c73c657c58bb3f27c3e01ac2e44fa82b739fffd54296678248.
def localCycle00095 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 3, .distance 1 4, .distance 1 6, .distance 1 5, .distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 1 3]
    constant := ![0, -2, 0, -2, -1, 0, 0, 3, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![true, false, true, false, false, false, false, false, true] }
  origin := ![.triangle 19 2, .gapLower 1 4, .triangle 24 1, .gapLower 1 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 15 2]

-- Cycle fingerprint b992a551c5d7723b6109420fe32fdff8f38c9a84aa4c6e357802e30479766599.
def localCycle00096 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 1 2, .distance 2 3, .distance 2 4, .distance 0 2, .distance 2 5, .distance 4 5, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, -1, 0, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, false, false, true] }
  origin := ![.corridorUpper 1 2, .triangle 15 0, .triangle 25 2, .triangle 6 0, .triangle 7 0, .triangle 28 1, .triangle 31 0, .corridorLower 3 4, .thetaNext 2]

-- Cycle fingerprint c04d12a8eb28d01f1c541c64bbf5f57003ef34383fe32f46223b96637019b892.
def localCycle00097 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 2, .distance 2 4, .distance 0 2, .distance 2 5, .distance 5 6, .distance 4 5, .distance 3 4, .theta 3]
    constant := ![3, -1, -1, 0, -1, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 0, .triangle 16 0, .gapLower 2 3, .triangle 7 0, .triangle 30 0, .triangle 34 0, .triangle 31 0, .corridorLower 3 4]

-- Cycle fingerprint c2dedc4d6c796215fc083589462166de5526900333910fb922fb557785e0093c.
def localCycle00098 : Cycle where
  length := 8
  data := {
    node := ![.theta 0, .zero, .theta 3, .distance 2 3, .distance 1 2, .distance 1 6, .distance 1 5, .distance 0 1, .theta 0]
    constant := ![0, 0, 3, -1, -2, 0, -2, -1]
    coefficient := ![0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, false] }
  origin := ![.thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 15 0, .gapLower 1 3, .triangle 24 1, .gapLower 1 1, .corridorLower 0 1]

-- Cycle fingerprint c5324fc7e71136ca71a5fab953c66414071c7ffc9a02439eac759a72fb91a0d5.
def localCycle00099 : Cycle where
  length := 8
  data := {
    node := ![.distance 3 5, .theta 3, .distance 2 3, .distance 2 4, .distance 4 6, .distance 0 4, .distance 0 2, .distance 2 5, .distance 3 5]
    constant := ![-1, 3, 0, -1, -1, 0, -1, 0]
    coefficient := ![0, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, true] }
  origin := ![.corridorLower 3 5, .corridorUpper 2 3, .triangle 25 2, .triangle 29 0, .triangle 13 0, .gapLower 0 3, .triangle 7 0, .triangle 26 1]

-- Cycle fingerprint c5fcfee85447095ca6307e251d8936a1182e055f305628a1a4a6fdbc373cd6a9.
def localCycle00100 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 2, .distance 1 6, .distance 1 5, .distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 1 3, .distance 1 4, .distance 1 2]
    constant := ![0, 0, -2, -1, 0, 0, 3, 0, -2, 0]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![true, true, false, false, false, false, false, true, false, true] }
  origin := ![.triangle 18 2, .triangle 24 1, .gapLower 1 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 15 2, .gapLower 1 5, .triangle 16 1]

-- Cycle fingerprint c6880f8e574e82c8b1e748d62ac128a69df0d1d01d9943f11f386e33e7d93d80.
def localCycle00101 : Cycle where
  length := 10
  data := {
    node := ![.theta 2, .distance 1 2, .distance 2 3, .distance 2 4, .distance 0 2, .distance 0 5, .distance 5 6, .distance 4 5, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, -1, 0, -1, 0, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false, false, false, true] }
  origin := ![.corridorUpper 1 2, .triangle 15 0, .triangle 25 2, .triangle 6 0, .triangle 7 2, .triangle 14 0, .triangle 34 0, .triangle 31 0, .corridorLower 3 4, .thetaNext 2]

-- Cycle fingerprint c6bf6e38b10dd84c9eb5a0df7cb8de66707bb7f3cdb226374243632a6bf969c7.
def localCycle00102 : Cycle where
  length := 11
  data := {
    node := ![.distance 3 5, .distance 4 5, .theta 4, .theta 3, .distance 2 3, .distance 1 3, .distance 1 4, .distance 1 6, .distance 1 2, .distance 0 2, .distance 2 5, .distance 3 5]
    constant := ![0, -1, 0, 3, 0, 0, -2, -2, 0, -1, 0]
    coefficient := ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![true, false, true, false, true, true, false, false, true, false, true] }
  origin := ![.triangle 31 1, .corridorLower 4 5, .thetaNext 3, .corridorUpper 2 3, .triangle 15 2, .triangle 19 2, .gapLower 1 4, .gapLower 1 3, .triangle 0 2, .triangle 7 0, .triangle 26 1]

-- Cycle fingerprint c920072ec595f9f208e0af2153aa38bb05591c3f6032a4e9e44fc7e0b211aa69.
def localCycle00103 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 3, .distance 1 4, .distance 4 6, .distance 3 4, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, 0, 0, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, false, false, true] }
  origin := ![.corridorUpper 2 3, .triangle 15 2, .triangle 19 2, .triangle 23 0, .triangle 32 0, .triangle 31 0, .corridorLower 4 5, .thetaNext 3]

-- Cycle fingerprint ca0bf9f2bc9f4c5d734fed748209d874093880b7aff73a15eedf4e5e930db08c.
def localCycle00104 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 2, .distance 2 4, .distance 0 2, .distance 2 6, .distance 4 6, .distance 3 4, .theta 3]
    constant := ![3, -1, -1, -1, -1, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 0, .triangle 16 0, .triangle 6 0, .triangle 8 0, .triangle 29 1, .triangle 32 0, .corridorLower 3 4]

-- Cycle fingerprint cabff57a27c131513bf9402c2ae067204ce5cedac13f2d011f753d4afe2fed5f.
def localCycle00105 : Cycle where
  length := 14
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 2 6, .distance 1 2, .distance 2 3, .distance 2 4, .distance 0 2, .distance 2 5, .distance 4 5, .distance 3 4, .theta 3, .zero]
    constant := ![0, 3, 0, 0, 0, -1, -1, 0, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, true, false, false, true, false, false, true, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 27 2, .triangle 18 0, .triangle 15 0, .triangle 25 2, .triangle 6 0, .triangle 7 0, .triangle 28 1, .triangle 31 0, .corridorLower 3 4, .thetaLower 3]

-- Cycle fingerprint cc661757948d3264df9a0d99750e4a5bbf1a56ebd7fedd333428c92b7fd7246c.
def localCycle00106 : Cycle where
  length := 4
  data := {
    node := ![.distance 1 2, .distance 1 5, .distance 5 6, .distance 2 6, .distance 1 2]
    constant := ![-2, 2, 0, -1]
    coefficient := ![0, 0, 0, 0]
    strict := ![false, true, false, false] }
  origin := ![.gapLower 1 2, .gapUpper 5 5, .gapLower 6 5, .triangle 18 0]

-- Cycle fingerprint d0c765ccbd3eddc8ecba1d0192e84ca3f8129736a1a31e07a008eec554e51195.
def localCycle00107 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 2, .distance 2 6, .distance 2 4, .distance 0 2, .distance 2 5, .distance 4 5, .distance 3 4, .theta 3]
    constant := ![3, -1, -1, 0, -1, -1, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, true, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 0, .triangle 18 0, .triangle 29 1, .triangle 6 0, .triangle 7 0, .triangle 28 1, .triangle 31 0, .corridorLower 3 4]

-- Cycle fingerprint d19cf0d9945003bd24e7e5ae4e751656040cb4c4f6eca00ec8a8c7cddd6cdcc3.
def localCycle00108 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 2, .distance 2 4, .distance 0 2, .distance 2 6, .distance 4 6, .distance 4 5, .distance 3 4, .theta 3]
    constant := ![3, -1, -1, -1, -1, 0, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 0, .triangle 16 0, .triangle 6 0, .triangle 8 0, .triangle 29 1, .triangle 34 1, .triangle 31 0, .corridorLower 3 4]

-- Cycle fingerprint d2eda2961e6b837c8bc631cb2b250b485e842aec67fb191c54f05e1afb8cd421.
def localCycle00109 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 5, .distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 1 3, .distance 1 4, .distance 1 6, .distance 1 2, .distance 1 5]
    constant := ![-2, -1, 0, 0, 3, 0, 0, 0, -2, 0]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, true, false, true] }
  origin := ![.gapLower 1 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 15 2, .triangle 19 2, .triangle 23 2, .gapLower 1 3, .triangle 17 2]

-- Cycle fingerprint d682b6bad45e7fd8fc9aee15eb260fe0ec13c7db6e22c3db2ab4fe385090f4dd.
def localCycle00110 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 2, .distance 1 4, .distance 4 6, .distance 2 4, .distance 0 2, .distance 2 5, .distance 3 5, .theta 3]
    constant := ![3, -1, 0, -1, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 0, .triangle 16 2, .triangle 23 0, .triangle 29 0, .triangle 6 0, .triangle 7 0, .triangle 26 1, .corridorLower 3 5]

-- Cycle fingerprint d7021794de82843ecbbb5a3d2203c37ae5dc134c61b45f596da52507d27d5d08.
def localCycle00111 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 2, .distance 2 4, .distance 0 2, .distance 0 5, .distance 5 6, .distance 3 5, .theta 3]
    constant := ![3, -1, -1, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 0, .triangle 16 0, .triangle 6 0, .triangle 7 2, .triangle 14 0, .triangle 33 0, .corridorLower 3 5]

-- Cycle fingerprint d8773d7716d759f1e795be1f044d2464527315de8696b3f434821a17480440d0.
def localCycle00112 : Cycle where
  length := 8
  data := {
    node := ![.distance 2 5, .distance 3 5, .theta 3, .distance 2 3, .distance 1 2, .distance 1 6, .distance 1 5, .distance 0 5, .distance 2 5]
    constant := ![0, -1, 3, -1, -2, -2, 0, 0]
    coefficient := ![0, 0, 1, 0, 0, 0, 0, 0]
    strict := ![true, false, false, false, false, false, true, true] }
  origin := ![.triangle 26 1, .corridorLower 3 5, .corridorUpper 2 3, .triangle 15 0, .gapLower 1 3, .gapLower 1 2, .triangle 3 2, .triangle 7 1]

-- Cycle fingerprint da36820e580ee9d42b2ba80e816780accb60228885dd054565f62411b80f0dac.
def localCycle00113 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 2, .distance 2 4, .distance 0 2, .distance 2 5, .distance 5 6, .distance 3 5, .theta 3]
    constant := ![3, -1, -1, 0, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 0, .triangle 16 0, .gapLower 2 3, .triangle 7 0, .triangle 30 0, .triangle 33 0, .corridorLower 3 5]

-- Cycle fingerprint db128e1b29ae93b53106f217d49392e31f79dec37d2a1a6718aed19df6da7e05.
def localCycle00114 : Cycle where
  length := 6
  data := {
    node := ![.distance 1 2, .distance 1 5, .distance 5 6, .distance 4 6, .distance 3 6, .distance 2 3, .distance 1 2]
    constant := ![0, 2, 0, 0, -1, -1]
    coefficient := ![0, 0, 0, 0, 0, 0]
    strict := ![true, true, true, true, false, false] }
  origin := ![.triangle 17 2, .gapUpper 5 5, .triangle 34 2, .triangle 32 2, .triangle 27 0, .triangle 15 0]

-- Cycle fingerprint db50cb21964ee201ad2577272d306bc234bda0327e03b92dd9d5a5c88c22cf7a.
def localCycle00115 : Cycle where
  length := 6
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 2, .distance 1 5, .distance 5 6, .distance 3 5, .theta 3]
    constant := ![3, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 0, .triangle 17 2, .triangle 24 0, .triangle 33 0, .corridorLower 3 5]

-- Cycle fingerprint db53f232338dc0372a64979bad29e54bb782e2b68c3913cbfb79b0e1c6bebd35.
def localCycle00116 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 2, .distance 2 4, .distance 0 2, .distance 2 5, .distance 4 5, .distance 3 4, .theta 3]
    constant := ![3, -1, -1, -1, -1, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 0, .triangle 16 0, .triangle 6 0, .triangle 7 0, .triangle 28 1, .triangle 31 0, .corridorLower 3 4]

-- Cycle fingerprint dbde3065a8ff7a4f531371977eebeebdf89cc329d785488b0e27fbc609f31c63.
def localCycle00117 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 2 3, .distance 2 4, .distance 4 6, .distance 3 4, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, 0, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, true] }
  origin := ![.corridorUpper 2 3, .triangle 25 2, .triangle 29 0, .triangle 32 0, .triangle 31 0, .corridorLower 4 5, .thetaNext 3]

-- Cycle fingerprint df1e85bbe2ac19fac25b95e3a7efc001e5c1c6323e7d2b04f4cc18aaf0856a85.
def localCycle00118 : Cycle where
  length := 10
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 1 4, .distance 1 5, .distance 5 6, .distance 2 5, .distance 4 5, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, 0, 0, 0, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, false, true, false, false, true] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 19 2, .triangle 22 2, .triangle 24 0, .triangle 30 0, .triangle 28 1, .triangle 31 0, .corridorLower 3 4, .thetaNext 2]

-- Cycle fingerprint e41b5e627652714f95956ffe288a8ca14b4f54d14af4383fa9e83f9b87237196.
def localCycle00119 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 2, .distance 2 4, .distance 2 6, .distance 0 2, .distance 2 5, .distance 4 5, .distance 3 4, .theta 3]
    constant := ![3, -1, -1, 0, -1, -1, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, true, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 0, .triangle 16 0, .triangle 29 2, .triangle 8 0, .triangle 7 0, .triangle 28 1, .triangle 31 0, .corridorLower 3 4]

-- Cycle fingerprint e43dc40f871fdc4d811f030776530124474145ee9a1ca5d3dabed0e9e78c6c74.
def localCycle00120 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 2, .distance 2 4, .distance 0 2, .distance 2 6, .distance 3 6, .distance 3 5, .theta 3]
    constant := ![3, -1, -1, -1, -1, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 0, .triangle 16 0, .triangle 6 0, .triangle 8 0, .triangle 27 1, .triangle 33 1, .corridorLower 3 5]

-- Cycle fingerprint e46c218b1a8272ef55eca8bf7a5ad33846462d5283c48ba3c57069063b5bd964.
def localCycle00121 : Cycle where
  length := 5
  data := {
    node := ![.distance 1 5, .distance 5 6, .distance 2 6, .distance 1 6, .distance 1 2, .distance 1 5]
    constant := ![2, 0, 0, -2, -2]
    coefficient := ![0, 0, 0, 0, 0]
    strict := ![true, false, true, false, false] }
  origin := ![.gapUpper 5 5, .gapLower 6 5, .triangle 18 2, .gapLower 1 3, .gapLower 1 2]

-- Cycle fingerprint e4a56c010b5cdbdb403b87ba7c91ac09bdb6ce53a4cc2cba175644129b5c5213.
def localCycle00122 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 2 4, .distance 0 2, .distance 2 5, .distance 4 5, .distance 3 5, .distance 5 6, .theta 5, .theta 4]
    constant := ![3, -1, -1, 0, 0, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false, false, true] }
  origin := ![.corridorUpper 2 4, .triangle 6 0, .triangle 7 0, .triangle 28 1, .triangle 31 2, .triangle 33 0, .corridorLower 5 6, .thetaNext 4]

-- Cycle fingerprint e886e3ff718d69a6a21ffe7fae0f90d5c7d5d6fe0f556187a989792b46e7bcd8.
def localCycle00123 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .theta 1, .distance 1 3, .distance 0 3, .distance 3 4, .distance 4 6, .distance 4 5, .theta 4, .theta 3, .theta 2]
    constant := ![0, 2, 0, -1, -1, 0, -1, 0, 0]
    coefficient := ![0, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![true, false, true, false, false, true, false, true, true] }
  origin := ![.thetaNext 1, .gapLower 1 6, .triangle 1 2, .triangle 9 0, .triangle 32 0, .triangle 34 1, .corridorLower 4 5, .thetaNext 3, .thetaNext 2]

-- Cycle fingerprint e984789e413552df22791401367d2490383f124f2c6efd1053cc2089cf96e354.
def localCycle00124 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 3, .distance 1 4, .distance 1 2, .distance 1 6, .distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 1 3]
    constant := ![0, -2, -2, -1, -1, 0, 0, 3, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![true, false, false, false, false, false, false, false, true] }
  origin := ![.triangle 19 2, .gapLower 1 4, .gapLower 1 3, .triangle 4 0, .corridorLower 0 1, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 15 2]

-- Cycle fingerprint eb4a599d2d4fa081acdae8d5c3baf97892d9de7dd1f4318de88ecb115fe2f7e1.
def localCycle00125 : Cycle where
  length := 10
  data := {
    node := ![.theta 2, .distance 1 2, .distance 2 3, .distance 2 4, .distance 0 2, .distance 2 5, .distance 5 6, .distance 4 5, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, -1, 0, -1, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false, false, true] }
  origin := ![.corridorUpper 1 2, .triangle 15 0, .triangle 25 2, .triangle 6 0, .triangle 7 0, .triangle 30 0, .triangle 34 0, .triangle 31 0, .corridorLower 3 4, .thetaNext 2]

-- Cycle fingerprint f03db862483f4c2bbf07b170d4160441c160ca3618c694ddf27894f2a8e6c1ca.
def localCycle00126 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 6, .distance 0 2, .distance 2 5, .theta 2, .theta 1, .distance 1 3, .distance 1 4, .distance 1 6, .distance 0 6]
    constant := ![0, -1, -1, 0, 2, 0, -2, 0]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![true, false, false, true, false, true, false, true] }
  origin := ![.triangle 8 1, .triangle 7 0, .corridorLower 2 5, .thetaNext 1, .gapLower 1 6, .triangle 19 2, .gapLower 1 4, .triangle 4 2]

-- Cycle fingerprint f0f616b9a1495e8db86ad175e7622069d69f8e10409b8c9fb488b7239d162b39.
def localCycle00127 : Cycle where
  length := 10
  data := {
    node := ![.theta 2, .distance 1 2, .distance 2 3, .distance 2 4, .distance 2 6, .distance 0 2, .distance 2 5, .distance 4 5, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, -1, 0, 0, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, true, false, false, true] }
  origin := ![.corridorUpper 1 2, .triangle 15 0, .triangle 25 2, .triangle 29 2, .triangle 8 0, .triangle 7 0, .triangle 28 1, .triangle 31 0, .corridorLower 3 4, .thetaNext 2]

-- Cycle fingerprint f1643d5d4dc9af2f579444272d4a89e3ee02e3413e76c88a785911301ffaf6a3.
def localCycle00128 : Cycle where
  length := 6
  data := {
    node := ![.theta 3, .distance 2 3, .distance 0 2, .distance 2 5, .distance 5 6, .distance 3 5, .theta 3]
    constant := ![3, -1, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 5 0, .triangle 7 0, .triangle 30 0, .triangle 33 0, .corridorLower 3 5]

-- Cycle fingerprint f1646594c969d496d6352b9538ecc3f56c8f19a379ea88090dca0759052cf54c.
def localCycle00129 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 3, .distance 1 4, .distance 4 6, .distance 0 4, .distance 0 2, .distance 2 5, .distance 3 5, .theta 3]
    constant := ![3, 0, 0, -1, -1, 0, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, true, false, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 2, .triangle 19 2, .triangle 23 0, .triangle 13 0, .triangle 6 1, .triangle 7 0, .triangle 26 1, .corridorLower 3 5]

-- Cycle fingerprint f7264cb87561645ea2db0eb2cc16a6a5189978f9145e8f38f857b2651af96659.
def localCycle00130 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 6, .distance 1 5, .distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 1 3, .distance 1 4, .distance 1 2, .distance 1 6]
    constant := ![-2, -1, -1, 0, 0, 3, 0, 0, -2, 0]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, true, false, true] }
  origin := ![.gapLower 1 2, .triangle 3 0, .corridorLower 0 1, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 15 2, .triangle 19 2, .gapLower 1 4, .triangle 18 2]

-- Cycle fingerprint f7da6d28293cc001b2555acb13a055030f7651ac95a2bb5700f4ec96358925ea.
def localCycle00131 : Cycle where
  length := 5
  data := {
    node := ![.distance 1 5, .distance 5 6, .distance 2 6, .distance 1 6, .distance 1 2, .distance 1 5]
    constant := ![2, 0, 0, -3, 0]
    coefficient := ![0, 0, 0, 0, 0]
    strict := ![true, false, false, false, true] }
  origin := ![.gapUpper 5 5, .gapLower 6 5, .gapLower 6 4, .gapLower 1 3, .triangle 17 2]

-- Cycle fingerprint fd330b87796de7cc1a6659d897f5b1417a7c6dcbcef383cffc3a5022dcb967bd.
def localCycle00132 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 2 3, .distance 0 2, .distance 0 5, .distance 5 6, .distance 4 5, .distance 3 4, .theta 3]
    constant := ![3, -1, 0, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 5 0, .triangle 7 2, .triangle 14 0, .triangle 34 0, .triangle 31 0, .corridorLower 3 4]

-- Cycle fingerprint fd42e5c96ccc32894adcd1436e9e68c0b6e9538f61a818ec13bc50c8f82c7f09.
def localCycle00133 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 2, .distance 0 2, .distance 2 6, .distance 4 6, .distance 3 4, .theta 3]
    constant := ![3, -1, 0, -1, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 0, .triangle 0 2, .triangle 8 0, .triangle 29 1, .triangle 32 0, .corridorLower 3 4]

-- Cycle fingerprint fff793fbdca27929fdd8da9cd72ed03cb4f512a39620d71d5be81753872a1969.
def localCycle00134 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 3, .distance 2 3, .distance 1 3, .distance 1 4, .distance 1 2, .distance 0 1, .theta 1, .zero]
    constant := ![0, 3, 0, 0, -2, -1, -2, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, false] }
  origin := ![.thetaUpper 3, .corridorUpper 2 3, .triangle 15 2, .triangle 19 2, .gapLower 1 4, .triangle 0 0, .gapLower 1 0, .thetaLower 1]

def library : Library := fun id => if id < 67 then (if id < 33 then (if id < 16 then (if id < 8 then (if id < 4 then (if id < 2 then (if id < 1 then (if id = 0 then some localCycle00000 else none) else (if id = 1 then some localCycle00001 else none)) else (if id < 3 then (if id = 2 then some localCycle00002 else none) else (if id = 3 then some localCycle00003 else none))) else (if id < 6 then (if id < 5 then (if id = 4 then some localCycle00004 else none) else (if id = 5 then some localCycle00005 else none)) else (if id < 7 then (if id = 6 then some localCycle00006 else none) else (if id = 7 then some localCycle00007 else none)))) else (if id < 12 then (if id < 10 then (if id < 9 then (if id = 8 then some localCycle00008 else none) else (if id = 9 then some localCycle00009 else none)) else (if id < 11 then (if id = 10 then some localCycle00010 else none) else (if id = 11 then some localCycle00011 else none))) else (if id < 14 then (if id < 13 then (if id = 12 then some localCycle00012 else none) else (if id = 13 then some localCycle00013 else none)) else (if id < 15 then (if id = 14 then some localCycle00014 else none) else (if id = 15 then some localCycle00015 else none))))) else (if id < 24 then (if id < 20 then (if id < 18 then (if id < 17 then (if id = 16 then some localCycle00016 else none) else (if id = 17 then some localCycle00017 else none)) else (if id < 19 then (if id = 18 then some localCycle00018 else none) else (if id = 19 then some localCycle00019 else none))) else (if id < 22 then (if id < 21 then (if id = 20 then some localCycle00020 else none) else (if id = 21 then some localCycle00021 else none)) else (if id < 23 then (if id = 22 then some localCycle00022 else none) else (if id = 23 then some localCycle00023 else none)))) else (if id < 28 then (if id < 26 then (if id < 25 then (if id = 24 then some localCycle00024 else none) else (if id = 25 then some localCycle00025 else none)) else (if id < 27 then (if id = 26 then some localCycle00026 else none) else (if id = 27 then some localCycle00027 else none))) else (if id < 30 then (if id < 29 then (if id = 28 then some localCycle00028 else none) else (if id = 29 then some localCycle00029 else none)) else (if id < 31 then (if id = 30 then some localCycle00030 else none) else (if id < 32 then (if id = 31 then some localCycle00031 else none) else (if id = 32 then some localCycle00032 else none))))))) else (if id < 50 then (if id < 41 then (if id < 37 then (if id < 35 then (if id < 34 then (if id = 33 then some localCycle00033 else none) else (if id = 34 then some localCycle00034 else none)) else (if id < 36 then (if id = 35 then some localCycle00035 else none) else (if id = 36 then some localCycle00036 else none))) else (if id < 39 then (if id < 38 then (if id = 37 then some localCycle00037 else none) else (if id = 38 then some localCycle00038 else none)) else (if id < 40 then (if id = 39 then some localCycle00039 else none) else (if id = 40 then some localCycle00040 else none)))) else (if id < 45 then (if id < 43 then (if id < 42 then (if id = 41 then some localCycle00041 else none) else (if id = 42 then some localCycle00042 else none)) else (if id < 44 then (if id = 43 then some localCycle00043 else none) else (if id = 44 then some localCycle00044 else none))) else (if id < 47 then (if id < 46 then (if id = 45 then some localCycle00045 else none) else (if id = 46 then some localCycle00046 else none)) else (if id < 48 then (if id = 47 then some localCycle00047 else none) else (if id < 49 then (if id = 48 then some localCycle00048 else none) else (if id = 49 then some localCycle00049 else none)))))) else (if id < 58 then (if id < 54 then (if id < 52 then (if id < 51 then (if id = 50 then some localCycle00050 else none) else (if id = 51 then some localCycle00051 else none)) else (if id < 53 then (if id = 52 then some localCycle00052 else none) else (if id = 53 then some localCycle00053 else none))) else (if id < 56 then (if id < 55 then (if id = 54 then some localCycle00054 else none) else (if id = 55 then some localCycle00055 else none)) else (if id < 57 then (if id = 56 then some localCycle00056 else none) else (if id = 57 then some localCycle00057 else none)))) else (if id < 62 then (if id < 60 then (if id < 59 then (if id = 58 then some localCycle00058 else none) else (if id = 59 then some localCycle00059 else none)) else (if id < 61 then (if id = 60 then some localCycle00060 else none) else (if id = 61 then some localCycle00061 else none))) else (if id < 64 then (if id < 63 then (if id = 62 then some localCycle00062 else none) else (if id = 63 then some localCycle00063 else none)) else (if id < 65 then (if id = 64 then some localCycle00064 else none) else (if id < 66 then (if id = 65 then some localCycle00065 else none) else (if id = 66 then some localCycle00066 else none)))))))) else (if id < 101 then (if id < 84 then (if id < 75 then (if id < 71 then (if id < 69 then (if id < 68 then (if id = 67 then some localCycle00067 else none) else (if id = 68 then some localCycle00068 else none)) else (if id < 70 then (if id = 69 then some localCycle00069 else none) else (if id = 70 then some localCycle00070 else none))) else (if id < 73 then (if id < 72 then (if id = 71 then some localCycle00071 else none) else (if id = 72 then some localCycle00072 else none)) else (if id < 74 then (if id = 73 then some localCycle00073 else none) else (if id = 74 then some localCycle00074 else none)))) else (if id < 79 then (if id < 77 then (if id < 76 then (if id = 75 then some localCycle00075 else none) else (if id = 76 then some localCycle00076 else none)) else (if id < 78 then (if id = 77 then some localCycle00077 else none) else (if id = 78 then some localCycle00078 else none))) else (if id < 81 then (if id < 80 then (if id = 79 then some localCycle00079 else none) else (if id = 80 then some localCycle00080 else none)) else (if id < 82 then (if id = 81 then some localCycle00081 else none) else (if id < 83 then (if id = 82 then some localCycle00082 else none) else (if id = 83 then some localCycle00083 else none)))))) else (if id < 92 then (if id < 88 then (if id < 86 then (if id < 85 then (if id = 84 then some localCycle00084 else none) else (if id = 85 then some localCycle00085 else none)) else (if id < 87 then (if id = 86 then some localCycle00086 else none) else (if id = 87 then some localCycle00087 else none))) else (if id < 90 then (if id < 89 then (if id = 88 then some localCycle00088 else none) else (if id = 89 then some localCycle00089 else none)) else (if id < 91 then (if id = 90 then some localCycle00090 else none) else (if id = 91 then some localCycle00091 else none)))) else (if id < 96 then (if id < 94 then (if id < 93 then (if id = 92 then some localCycle00092 else none) else (if id = 93 then some localCycle00093 else none)) else (if id < 95 then (if id = 94 then some localCycle00094 else none) else (if id = 95 then some localCycle00095 else none))) else (if id < 98 then (if id < 97 then (if id = 96 then some localCycle00096 else none) else (if id = 97 then some localCycle00097 else none)) else (if id < 99 then (if id = 98 then some localCycle00098 else none) else (if id < 100 then (if id = 99 then some localCycle00099 else none) else (if id = 100 then some localCycle00100 else none))))))) else (if id < 118 then (if id < 109 then (if id < 105 then (if id < 103 then (if id < 102 then (if id = 101 then some localCycle00101 else none) else (if id = 102 then some localCycle00102 else none)) else (if id < 104 then (if id = 103 then some localCycle00103 else none) else (if id = 104 then some localCycle00104 else none))) else (if id < 107 then (if id < 106 then (if id = 105 then some localCycle00105 else none) else (if id = 106 then some localCycle00106 else none)) else (if id < 108 then (if id = 107 then some localCycle00107 else none) else (if id = 108 then some localCycle00108 else none)))) else (if id < 113 then (if id < 111 then (if id < 110 then (if id = 109 then some localCycle00109 else none) else (if id = 110 then some localCycle00110 else none)) else (if id < 112 then (if id = 111 then some localCycle00111 else none) else (if id = 112 then some localCycle00112 else none))) else (if id < 115 then (if id < 114 then (if id = 113 then some localCycle00113 else none) else (if id = 114 then some localCycle00114 else none)) else (if id < 116 then (if id = 115 then some localCycle00115 else none) else (if id < 117 then (if id = 116 then some localCycle00116 else none) else (if id = 117 then some localCycle00117 else none)))))) else (if id < 126 then (if id < 122 then (if id < 120 then (if id < 119 then (if id = 118 then some localCycle00118 else none) else (if id = 119 then some localCycle00119 else none)) else (if id < 121 then (if id = 120 then some localCycle00120 else none) else (if id = 121 then some localCycle00121 else none))) else (if id < 124 then (if id < 123 then (if id = 122 then some localCycle00122 else none) else (if id = 123 then some localCycle00123 else none)) else (if id < 125 then (if id = 124 then some localCycle00124 else none) else (if id = 125 then some localCycle00125 else none)))) else (if id < 130 then (if id < 128 then (if id < 127 then (if id = 126 then some localCycle00126 else none) else (if id = 127 then some localCycle00127 else none)) else (if id < 129 then (if id = 128 then some localCycle00128 else none) else (if id = 129 then some localCycle00129 else none))) else (if id < 132 then (if id < 131 then (if id = 130 then some localCycle00130 else none) else (if id = 131 then some localCycle00131 else none)) else (if id < 133 then (if id = 132 then some localCycle00132 else none) else (if id < 134 then (if id = 133 then some localCycle00133 else none) else (if id = 134 then some localCycle00134 else none))))))))

def namedLeaf000 : LeafData := { rows := ![![1, 5, 2, 4, 3, 6], ![0, 5, 2, 4, 3, 6], ![5, 0, 1, 4, 3, 6], ![4, 5, 0, 1, 2, 6], ![3, 5, 0, 1, 2, 6], ![3, 4, 2, 0, 1, 6], ![0, 1, 2, 3, 4, 5]], proof := .tail 114 }

theorem namedLeaf000_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3584)) namedLeaf000 = true :=
  by decide +kernel

def namedLeaf001 : LeafData := { rows := ![![1, 5, 2, 4, 3, 6], ![0, 5, 2, 4, 3, 6], ![5, 0, 1, 4, 6, 3], ![4, 5, 0, 1, 6, 2], ![3, 5, 0, 1, 2, 6], ![3, 4, 2, 0, 1, 6], ![0, 1, 3, 2, 4, 5]], proof := .tail 86 }

theorem namedLeaf001_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3585)) namedLeaf001 = true :=
  by decide +kernel

def namedLeaf002 : LeafData := { rows := ![![1, 5, 2, 4, 3, 6], ![0, 5, 2, 4, 3, 6], ![5, 0, 1, 6, 4, 3], ![4, 5, 0, 1, 6, 2], ![3, 5, 0, 1, 6, 2], ![3, 4, 2, 0, 1, 6], ![0, 1, 3, 4, 2, 5]], proof := .tail 17 }

theorem namedLeaf002_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3586)) namedLeaf002 = true :=
  by decide +kernel

def namedLeaf003 : LeafData := { rows := ![![1, 5, 2, 4, 3, 6], ![0, 5, 2, 4, 6, 3], ![5, 0, 1, 4, 6, 3], ![4, 5, 0, 6, 1, 2], ![3, 5, 0, 1, 2, 6], ![3, 4, 2, 0, 1, 6], ![0, 3, 1, 2, 4, 5]], proof := .tail 61 }

theorem namedLeaf003_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3587)) namedLeaf003 = true :=
  by decide +kernel

def namedLeaf004 : LeafData := { rows := ![![1, 5, 2, 4, 3, 6], ![0, 5, 2, 4, 6, 3], ![5, 0, 1, 6, 4, 3], ![4, 5, 0, 6, 1, 2], ![3, 5, 0, 1, 6, 2], ![3, 4, 2, 0, 1, 6], ![0, 3, 1, 4, 2, 5]], proof := .tail 17 }

theorem namedLeaf004_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3588)) namedLeaf004 = true :=
  by decide +kernel

def namedLeaf005 : LeafData := { rows := ![![1, 5, 2, 4, 3, 6], ![0, 5, 2, 6, 4, 3], ![5, 0, 1, 6, 4, 3], ![4, 5, 0, 6, 1, 2], ![3, 5, 0, 6, 1, 2], ![3, 4, 2, 0, 1, 6], ![0, 3, 4, 1, 2, 5]], proof := .tail 10 }

theorem namedLeaf005_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3589)) namedLeaf005 = true :=
  by decide +kernel

def namedLeaf006 : LeafData := { rows := ![![1, 5, 2, 4, 3, 6], ![0, 5, 6, 2, 4, 3], ![5, 0, 6, 1, 4, 3], ![4, 5, 0, 6, 1, 2], ![3, 5, 0, 6, 1, 2], ![3, 4, 2, 0, 1, 6], ![0, 3, 4, 2, 1, 5]], proof := .tail 49 }

theorem namedLeaf006_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3590)) namedLeaf006 = true :=
  by decide +kernel

def namedLeaf007 : LeafData := { rows := ![![1, 5, 2, 4, 3, 6], ![0, 6, 5, 2, 4, 3], ![5, 0, 6, 1, 4, 3], ![4, 5, 0, 6, 1, 2], ![3, 5, 0, 6, 1, 2], ![3, 4, 2, 0, 6, 1], ![0, 3, 4, 2, 5, 1]], proof := .tail 88 }

theorem namedLeaf007_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3591)) namedLeaf007 = true :=
  by decide +kernel

def namedLeaf008 : LeafData := { rows := ![![1, 5, 2, 4, 6, 3], ![0, 5, 2, 4, 6, 3], ![5, 0, 1, 4, 6, 3], ![4, 5, 6, 0, 1, 2], ![3, 5, 0, 1, 2, 6], ![3, 4, 2, 0, 1, 6], ![3, 0, 1, 2, 4, 5]], proof := .tail 45 }

theorem namedLeaf008_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3592)) namedLeaf008 = true :=
  by decide +kernel

def namedLeaf009 : LeafData := { rows := ![![1, 5, 2, 4, 6, 3], ![0, 5, 2, 4, 6, 3], ![5, 0, 1, 6, 4, 3], ![4, 5, 6, 0, 1, 2], ![3, 5, 0, 1, 6, 2], ![3, 4, 2, 0, 1, 6], ![3, 0, 1, 4, 2, 5]], proof := .tail 71 }

theorem namedLeaf009_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3593)) namedLeaf009 = true :=
  by decide +kernel

def namedLeaf010 : LeafData := { rows := ![![1, 5, 2, 4, 6, 3], ![0, 5, 2, 6, 4, 3], ![5, 0, 1, 6, 4, 3], ![4, 5, 6, 0, 1, 2], ![3, 5, 0, 6, 1, 2], ![3, 4, 2, 0, 1, 6], ![3, 0, 4, 1, 2, 5]], proof := .tail 10 }

theorem namedLeaf010_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3594)) namedLeaf010 = true :=
  by decide +kernel

def namedLeaf011 : LeafData := { rows := ![![1, 5, 2, 4, 6, 3], ![0, 5, 6, 2, 4, 3], ![5, 0, 6, 1, 4, 3], ![4, 5, 6, 0, 1, 2], ![3, 5, 0, 6, 1, 2], ![3, 4, 2, 0, 1, 6], ![3, 0, 4, 2, 1, 5]], proof := .tail 49 }

theorem namedLeaf011_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3595)) namedLeaf011 = true :=
  by decide +kernel

def namedLeaf012 : LeafData := { rows := ![![1, 5, 2, 4, 6, 3], ![0, 6, 5, 2, 4, 3], ![5, 0, 6, 1, 4, 3], ![4, 5, 6, 0, 1, 2], ![3, 5, 0, 6, 1, 2], ![3, 4, 2, 0, 6, 1], ![3, 0, 4, 2, 5, 1]], proof := .tail 88 }

theorem namedLeaf012_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3596)) namedLeaf012 = true :=
  by decide +kernel

def namedLeaf013 : LeafData := { rows := ![![1, 5, 2, 6, 4, 3], ![0, 5, 2, 6, 4, 3], ![5, 0, 1, 6, 4, 3], ![4, 5, 6, 0, 1, 2], ![3, 5, 6, 0, 1, 2], ![3, 4, 2, 0, 1, 6], ![3, 4, 0, 1, 2, 5]], proof := .tail 10 }

theorem namedLeaf013_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3597)) namedLeaf013 = true :=
  by decide +kernel

def namedLeaf014 : LeafData := { rows := ![![1, 5, 2, 6, 4, 3], ![0, 5, 6, 2, 4, 3], ![5, 0, 6, 1, 4, 3], ![4, 5, 6, 0, 1, 2], ![3, 5, 6, 0, 1, 2], ![3, 4, 2, 0, 1, 6], ![3, 4, 0, 2, 1, 5]], proof := .tail 49 }

theorem namedLeaf014_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3598)) namedLeaf014 = true :=
  by decide +kernel

def namedLeaf015 : LeafData := { rows := ![![1, 5, 2, 6, 4, 3], ![0, 6, 5, 2, 4, 3], ![5, 0, 6, 1, 4, 3], ![4, 5, 6, 0, 1, 2], ![3, 5, 6, 0, 1, 2], ![3, 4, 2, 0, 6, 1], ![3, 4, 0, 2, 5, 1]], proof := .tail 88 }

theorem namedLeaf015_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3599)) namedLeaf015 = true :=
  by decide +kernel

def namedLeaf016 : LeafData := { rows := ![![1, 5, 6, 2, 4, 3], ![0, 5, 6, 2, 4, 3], ![5, 6, 0, 1, 4, 3], ![4, 5, 6, 0, 1, 2], ![3, 5, 6, 0, 1, 2], ![3, 4, 2, 0, 1, 6], ![3, 4, 2, 0, 1, 5]], proof := .tail 75 }

theorem namedLeaf016_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3600)) namedLeaf016 = true :=
  by decide +kernel

def namedLeaf017 : LeafData := { rows := ![![1, 5, 6, 2, 4, 3], ![0, 6, 5, 2, 4, 3], ![5, 6, 0, 1, 4, 3], ![4, 5, 6, 0, 1, 2], ![3, 5, 6, 0, 1, 2], ![3, 4, 2, 0, 6, 1], ![3, 4, 2, 0, 5, 1]], proof := .tail 88 }

theorem namedLeaf017_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3601)) namedLeaf017 = true :=
  by decide +kernel

def namedLeaf018 : LeafData := { rows := ![![1, 6, 5, 2, 4, 3], ![0, 6, 5, 2, 4, 3], ![5, 6, 0, 1, 4, 3], ![4, 5, 6, 0, 1, 2], ![3, 5, 6, 0, 1, 2], ![3, 4, 2, 6, 0, 1], ![3, 4, 2, 5, 0, 1]], proof := .tail 132 }

theorem namedLeaf018_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3602)) namedLeaf018 = true :=
  by decide +kernel

def namedLeaf019 : LeafData := { rows := ![![1, 6, 5, 2, 4, 3], ![0, 6, 5, 2, 4, 3], ![6, 5, 0, 1, 4, 3], ![4, 5, 6, 0, 1, 2], ![3, 5, 6, 0, 1, 2], ![3, 4, 6, 2, 0, 1], ![3, 4, 5, 2, 0, 1]], proof := .tail 63 }

theorem namedLeaf019_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3603)) namedLeaf019 = true :=
  by decide +kernel

def namedLeaf020 : LeafData := { rows := ![![1, 6, 5, 2, 4, 3], ![0, 6, 5, 2, 4, 3], ![6, 5, 0, 1, 4, 3], ![4, 5, 6, 0, 1, 2], ![3, 6, 5, 0, 1, 2], ![3, 6, 4, 2, 0, 1], ![3, 5, 4, 2, 0, 1]], proof := .tail 24 }

theorem namedLeaf020_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3604)) namedLeaf020 = true :=
  by decide +kernel

def namedLeaf021 : LeafData := { rows := ![![1, 6, 5, 2, 4, 3], ![0, 6, 5, 2, 4, 3], ![6, 5, 0, 1, 4, 3], ![4, 6, 5, 0, 1, 2], ![3, 6, 5, 0, 1, 2], ![6, 3, 4, 2, 0, 1], ![5, 3, 4, 2, 0, 1]], proof := .tail 122 }

theorem namedLeaf021_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3605)) namedLeaf021 = true :=
  by decide +kernel

def namedLeaf022 : LeafData := { rows := ![![1, 6, 5, 2, 4, 3], ![0, 6, 5, 2, 4, 3], ![6, 5, 0, 1, 4, 3], ![6, 4, 5, 0, 1, 2], ![6, 3, 5, 0, 1, 2], ![6, 3, 4, 2, 0, 1], ![5, 4, 3, 2, 0, 1]], proof := .tail 74 }

theorem namedLeaf022_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3606)) namedLeaf022 = true :=
  by decide +kernel

def namedLeaf023 : LeafData := { rows := ![![1, 5, 2, 4, 3, 6], ![0, 5, 4, 2, 3, 6], ![5, 0, 4, 1, 3, 6], ![4, 5, 0, 1, 2, 6], ![3, 5, 0, 2, 1, 6], ![3, 4, 2, 0, 1, 6], ![0, 1, 2, 3, 4, 5]], proof := .tail 94 }

theorem namedLeaf023_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3607)) namedLeaf023 = true :=
  by decide +kernel

def namedLeaf024 : LeafData := { rows := ![![1, 5, 2, 4, 3, 6], ![0, 5, 4, 2, 3, 6], ![5, 0, 4, 1, 6, 3], ![4, 5, 0, 1, 6, 2], ![3, 5, 0, 2, 1, 6], ![3, 4, 2, 0, 1, 6], ![0, 1, 3, 2, 4, 5]], proof := .tail 16 }

theorem namedLeaf024_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3608)) namedLeaf024 = true :=
  by decide +kernel

def namedLeaf025 : LeafData := { rows := ![![1, 5, 2, 4, 3, 6], ![0, 5, 4, 2, 6, 3], ![5, 0, 4, 1, 6, 3], ![4, 5, 0, 6, 1, 2], ![3, 5, 0, 2, 1, 6], ![3, 4, 2, 0, 1, 6], ![0, 3, 1, 2, 4, 5]], proof := .tail 116 }

theorem namedLeaf025_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3609)) namedLeaf025 = true :=
  by decide +kernel

def namedLeaf026 : LeafData := { rows := ![![1, 5, 2, 4, 3, 6], ![0, 5, 4, 6, 2, 3], ![5, 0, 4, 6, 1, 3], ![4, 5, 0, 6, 1, 2], ![3, 5, 0, 2, 1, 6], ![3, 4, 2, 0, 1, 6], ![0, 3, 2, 1, 4, 5]], proof := .tail 107 }

theorem namedLeaf026_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3610)) namedLeaf026 = true :=
  by decide +kernel

def namedLeaf027 : LeafData := { rows := ![![1, 5, 2, 4, 3, 6], ![0, 5, 6, 4, 2, 3], ![5, 0, 4, 6, 1, 3], ![4, 5, 0, 6, 1, 2], ![3, 5, 0, 2, 6, 1], ![3, 4, 2, 0, 1, 6], ![0, 3, 2, 4, 1, 5]], proof := .tail 36 }

theorem namedLeaf027_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3611)) namedLeaf027 = true :=
  by decide +kernel

def namedLeaf028 : LeafData := { rows := ![![1, 5, 2, 4, 3, 6], ![0, 5, 6, 4, 2, 3], ![5, 0, 6, 4, 1, 3], ![4, 5, 0, 6, 1, 2], ![3, 5, 0, 6, 2, 1], ![3, 4, 2, 0, 1, 6], ![0, 3, 4, 2, 1, 5]], proof := .tail 19 }

theorem namedLeaf028_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3612)) namedLeaf028 = true :=
  by decide +kernel

def namedLeaf029 : LeafData := { rows := ![![1, 5, 2, 4, 3, 6], ![0, 6, 5, 4, 2, 3], ![5, 0, 4, 6, 1, 3], ![4, 5, 0, 6, 1, 2], ![3, 5, 0, 2, 6, 1], ![3, 4, 2, 0, 6, 1], ![0, 3, 2, 4, 5, 1]], proof := .tail 87 }

theorem namedLeaf029_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3613)) namedLeaf029 = true :=
  by decide +kernel

def namedLeaf030 : LeafData := { rows := ![![1, 5, 2, 4, 3, 6], ![0, 6, 5, 4, 2, 3], ![5, 0, 6, 4, 1, 3], ![4, 5, 0, 6, 1, 2], ![3, 5, 0, 6, 2, 1], ![3, 4, 2, 0, 6, 1], ![0, 3, 4, 2, 5, 1]], proof := .tail 19 }

theorem namedLeaf030_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3614)) namedLeaf030 = true :=
  by decide +kernel

def namedLeaf031 : LeafData := { rows := ![![1, 5, 2, 4, 6, 3], ![0, 5, 4, 2, 6, 3], ![5, 0, 4, 1, 6, 3], ![4, 5, 6, 0, 1, 2], ![3, 5, 0, 2, 1, 6], ![3, 4, 2, 0, 1, 6], ![3, 0, 1, 2, 4, 5]], proof := .tail 116 }

theorem namedLeaf031_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3615)) namedLeaf031 = true :=
  by decide +kernel

def namedLeaf032 : LeafData := { rows := ![![1, 5, 2, 4, 6, 3], ![0, 5, 4, 6, 2, 3], ![5, 0, 4, 6, 1, 3], ![4, 5, 6, 0, 1, 2], ![3, 5, 0, 2, 1, 6], ![3, 4, 2, 0, 1, 6], ![3, 0, 2, 1, 4, 5]], proof := .tail 107 }

theorem namedLeaf032_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3616)) namedLeaf032 = true :=
  by decide +kernel

def namedLeaf033 : LeafData := { rows := ![![1, 5, 2, 4, 6, 3], ![0, 5, 6, 4, 2, 3], ![5, 0, 4, 6, 1, 3], ![4, 5, 6, 0, 1, 2], ![3, 5, 0, 2, 6, 1], ![3, 4, 2, 0, 1, 6], ![3, 0, 2, 4, 1, 5]], proof := .tail 36 }

theorem namedLeaf033_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3617)) namedLeaf033 = true :=
  by decide +kernel

def namedLeaf034 : LeafData := { rows := ![![1, 5, 2, 4, 6, 3], ![0, 5, 6, 4, 2, 3], ![5, 0, 6, 4, 1, 3], ![4, 5, 6, 0, 1, 2], ![3, 5, 0, 6, 2, 1], ![3, 4, 2, 0, 1, 6], ![3, 0, 4, 2, 1, 5]], proof := .tail 41 }

theorem namedLeaf034_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3618)) namedLeaf034 = true :=
  by decide +kernel

def namedLeaf035 : LeafData := { rows := ![![1, 5, 2, 4, 6, 3], ![0, 6, 5, 4, 2, 3], ![5, 0, 4, 6, 1, 3], ![4, 5, 6, 0, 1, 2], ![3, 5, 0, 2, 6, 1], ![3, 4, 2, 0, 6, 1], ![3, 0, 2, 4, 5, 1]], proof := .tail 87 }

theorem namedLeaf035_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3619)) namedLeaf035 = true :=
  by decide +kernel

def namedLeaf036 : LeafData := { rows := ![![1, 5, 2, 4, 6, 3], ![0, 6, 5, 4, 2, 3], ![5, 0, 6, 4, 1, 3], ![4, 5, 6, 0, 1, 2], ![3, 5, 0, 6, 2, 1], ![3, 4, 2, 0, 6, 1], ![3, 0, 4, 2, 5, 1]], proof := .tail 85 }

theorem namedLeaf036_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3620)) namedLeaf036 = true :=
  by decide +kernel

def namedLeaf037 : LeafData := { rows := ![![1, 5, 2, 6, 4, 3], ![0, 5, 6, 4, 2, 3], ![5, 0, 6, 4, 1, 3], ![4, 5, 6, 0, 1, 2], ![3, 5, 6, 0, 2, 1], ![3, 4, 2, 0, 1, 6], ![3, 4, 0, 2, 1, 5]], proof := .tail 119 }

theorem namedLeaf037_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3621)) namedLeaf037 = true :=
  by decide +kernel

def namedLeaf038 : LeafData := { rows := ![![1, 5, 2, 6, 4, 3], ![0, 6, 5, 4, 2, 3], ![5, 0, 6, 4, 1, 3], ![4, 5, 6, 0, 1, 2], ![3, 5, 6, 0, 2, 1], ![3, 4, 2, 0, 6, 1], ![3, 4, 0, 2, 5, 1]], proof := .tail 85 }

theorem namedLeaf038_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3622)) namedLeaf038 = true :=
  by decide +kernel

def namedLeaf039 : LeafData := { rows := ![![1, 5, 6, 2, 4, 3], ![0, 5, 6, 4, 2, 3], ![5, 6, 0, 4, 1, 3], ![4, 5, 6, 0, 1, 2], ![3, 5, 6, 0, 2, 1], ![3, 4, 2, 0, 1, 6], ![3, 4, 2, 0, 1, 5]], proof := .tail 108 }

theorem namedLeaf039_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3623)) namedLeaf039 = true :=
  by decide +kernel

def namedLeaf040 : LeafData := { rows := ![![1, 5, 6, 2, 4, 3], ![0, 6, 5, 4, 2, 3], ![5, 6, 0, 4, 1, 3], ![4, 5, 6, 0, 1, 2], ![3, 5, 6, 0, 2, 1], ![3, 4, 2, 0, 6, 1], ![3, 4, 2, 0, 5, 1]], proof := .tail 108 }

theorem namedLeaf040_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3624)) namedLeaf040 = true :=
  by decide +kernel

def namedLeaf041 : LeafData := { rows := ![![1, 6, 5, 2, 4, 3], ![0, 6, 5, 4, 2, 3], ![5, 6, 0, 4, 1, 3], ![4, 5, 6, 0, 1, 2], ![3, 5, 6, 0, 2, 1], ![3, 4, 2, 6, 0, 1], ![3, 4, 2, 5, 0, 1]], proof := .tail 46 }

theorem namedLeaf041_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3625)) namedLeaf041 = true :=
  by decide +kernel

def namedLeaf042 : LeafData := { rows := ![![1, 6, 5, 2, 4, 3], ![0, 6, 5, 4, 2, 3], ![6, 5, 0, 4, 1, 3], ![4, 5, 6, 0, 1, 2], ![3, 5, 6, 0, 2, 1], ![3, 4, 6, 2, 0, 1], ![3, 4, 5, 2, 0, 1]], proof := .tail 97 }

theorem namedLeaf042_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3626)) namedLeaf042 = true :=
  by decide +kernel

def namedLeaf043 : LeafData := { rows := ![![1, 6, 5, 2, 4, 3], ![0, 6, 5, 4, 2, 3], ![6, 5, 0, 4, 1, 3], ![4, 5, 6, 0, 1, 2], ![3, 6, 5, 0, 2, 1], ![3, 6, 4, 2, 0, 1], ![3, 5, 4, 2, 0, 1]], proof := .tail 34 }

theorem namedLeaf043_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3627)) namedLeaf043 = true :=
  by decide +kernel

def namedLeaf044 : LeafData := { rows := ![![1, 6, 5, 2, 4, 3], ![0, 6, 5, 4, 2, 3], ![6, 5, 0, 4, 1, 3], ![4, 6, 5, 0, 1, 2], ![3, 6, 5, 0, 2, 1], ![6, 3, 4, 2, 0, 1], ![5, 3, 4, 2, 0, 1]], proof := .tail 116 }

theorem namedLeaf044_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3628)) namedLeaf044 = true :=
  by decide +kernel

def namedLeaf045 : LeafData := { rows := ![![1, 6, 5, 2, 4, 3], ![0, 6, 5, 4, 2, 3], ![6, 5, 0, 4, 1, 3], ![6, 4, 5, 0, 1, 2], ![6, 3, 5, 0, 2, 1], ![6, 3, 4, 2, 0, 1], ![5, 4, 3, 2, 0, 1]], proof := .tail 70 }

theorem namedLeaf045_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3629)) namedLeaf045 = true :=
  by decide +kernel

def namedLeaf046 : LeafData := { rows := ![![1, 5, 2, 4, 3, 6], ![0, 5, 4, 3, 2, 6], ![5, 0, 4, 3, 1, 6], ![4, 5, 0, 2, 1, 6], ![3, 5, 0, 2, 1, 6], ![3, 4, 2, 0, 1, 6], ![0, 1, 2, 3, 4, 5]], proof := .tail 105 }

theorem namedLeaf046_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3630)) namedLeaf046 = true :=
  by decide +kernel

def namedLeaf047 : LeafData := { rows := ![![1, 5, 2, 4, 3, 6], ![0, 5, 4, 3, 6, 2], ![5, 0, 4, 3, 6, 1], ![4, 5, 0, 2, 1, 6], ![3, 5, 0, 2, 1, 6], ![3, 4, 2, 0, 1, 6], ![0, 2, 1, 3, 4, 5]], proof := .tail 20 }

theorem namedLeaf047_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3631)) namedLeaf047 = true :=
  by decide +kernel

def namedLeaf048 : LeafData := { rows := ![![1, 5, 2, 4, 3, 6], ![0, 5, 4, 6, 3, 2], ![5, 0, 4, 3, 6, 1], ![4, 5, 0, 2, 6, 1], ![3, 5, 0, 2, 1, 6], ![3, 4, 2, 0, 1, 6], ![0, 2, 3, 1, 4, 5]], proof := .tail 58 }

theorem namedLeaf048_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3632)) namedLeaf048 = true :=
  by decide +kernel

def namedLeaf049 : LeafData := { rows := ![![1, 5, 2, 4, 3, 6], ![0, 5, 4, 6, 3, 2], ![5, 0, 4, 6, 3, 1], ![4, 5, 0, 6, 2, 1], ![3, 5, 0, 2, 1, 6], ![3, 4, 2, 0, 1, 6], ![0, 3, 2, 1, 4, 5]], proof := .tail 5 }

theorem namedLeaf049_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3633)) namedLeaf049 = true :=
  by decide +kernel

def namedLeaf050 : LeafData := { rows := ![![1, 5, 2, 4, 3, 6], ![0, 5, 6, 4, 3, 2], ![5, 0, 4, 3, 6, 1], ![4, 5, 0, 2, 6, 1], ![3, 5, 0, 2, 6, 1], ![3, 4, 2, 0, 1, 6], ![0, 2, 3, 4, 1, 5]], proof := .tail 35 }

theorem namedLeaf050_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3634)) namedLeaf050 = true :=
  by decide +kernel

def namedLeaf051 : LeafData := { rows := ![![1, 5, 2, 4, 3, 6], ![0, 5, 6, 4, 3, 2], ![5, 0, 4, 6, 3, 1], ![4, 5, 0, 6, 2, 1], ![3, 5, 0, 2, 6, 1], ![3, 4, 2, 0, 1, 6], ![0, 3, 2, 4, 1, 5]], proof := .tail 35 }

theorem namedLeaf051_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3635)) namedLeaf051 = true :=
  by decide +kernel

def namedLeaf052 : LeafData := { rows := ![![1, 5, 2, 4, 3, 6], ![0, 5, 6, 4, 3, 2], ![5, 0, 6, 4, 3, 1], ![4, 5, 0, 6, 2, 1], ![3, 5, 0, 6, 2, 1], ![3, 4, 2, 0, 1, 6], ![0, 3, 4, 2, 1, 5]], proof := .tail 18 }

theorem namedLeaf052_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3636)) namedLeaf052 = true :=
  by decide +kernel

def namedLeaf053 : LeafData := { rows := ![![1, 5, 2, 4, 3, 6], ![0, 6, 5, 4, 3, 2], ![5, 0, 4, 3, 6, 1], ![4, 5, 0, 2, 6, 1], ![3, 5, 0, 2, 6, 1], ![3, 4, 2, 0, 6, 1], ![0, 2, 3, 4, 5, 1]], proof := .tail 39 }

theorem namedLeaf053_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3637)) namedLeaf053 = true :=
  by decide +kernel

def namedLeaf054 : LeafData := { rows := ![![1, 5, 2, 4, 3, 6], ![0, 6, 5, 4, 3, 2], ![5, 0, 4, 6, 3, 1], ![4, 5, 0, 6, 2, 1], ![3, 5, 0, 2, 6, 1], ![3, 4, 2, 0, 6, 1], ![0, 3, 2, 4, 5, 1]], proof := .tail 39 }

theorem namedLeaf054_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3638)) namedLeaf054 = true :=
  by decide +kernel

def namedLeaf055 : LeafData := { rows := ![![1, 5, 2, 4, 3, 6], ![0, 6, 5, 4, 3, 2], ![5, 0, 6, 4, 3, 1], ![4, 5, 0, 6, 2, 1], ![3, 5, 0, 6, 2, 1], ![3, 4, 2, 0, 6, 1], ![0, 3, 4, 2, 5, 1]], proof := .tail 54 }

theorem namedLeaf055_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3639)) namedLeaf055 = true :=
  by decide +kernel

def namedLeaf056 : LeafData := { rows := ![![1, 5, 2, 4, 6, 3], ![0, 5, 4, 6, 3, 2], ![5, 0, 4, 6, 3, 1], ![4, 5, 6, 0, 2, 1], ![3, 5, 0, 2, 1, 6], ![3, 4, 2, 0, 1, 6], ![3, 0, 2, 1, 4, 5]], proof := .tail 44 }

theorem namedLeaf056_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3640)) namedLeaf056 = true :=
  by decide +kernel

def namedLeaf057 : LeafData := { rows := ![![1, 5, 2, 4, 6, 3], ![0, 5, 6, 4, 3, 2], ![5, 0, 4, 6, 3, 1], ![4, 5, 6, 0, 2, 1], ![3, 5, 0, 2, 6, 1], ![3, 4, 2, 0, 1, 6], ![3, 0, 2, 4, 1, 5]], proof := .tail 35 }

theorem namedLeaf057_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3641)) namedLeaf057 = true :=
  by decide +kernel

def namedLeaf058 : LeafData := { rows := ![![1, 5, 2, 4, 6, 3], ![0, 5, 6, 4, 3, 2], ![5, 0, 6, 4, 3, 1], ![4, 5, 6, 0, 2, 1], ![3, 5, 0, 6, 2, 1], ![3, 4, 2, 0, 1, 6], ![3, 0, 4, 2, 1, 5]], proof := .tail 22 }

theorem namedLeaf058_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3642)) namedLeaf058 = true :=
  by decide +kernel

def namedLeaf059 : LeafData := { rows := ![![1, 5, 2, 6, 4, 3], ![0, 5, 6, 4, 3, 2], ![5, 0, 6, 4, 3, 1], ![4, 5, 6, 0, 2, 1], ![3, 5, 6, 0, 2, 1], ![3, 4, 2, 0, 1, 6], ![3, 4, 0, 2, 1, 5]], proof := .tail 127 }

theorem namedLeaf059_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3643)) namedLeaf059 = true :=
  by decide +kernel

def namedLeaf060 : LeafData := { rows := ![![1, 5, 2, 4, 6, 3], ![0, 6, 5, 4, 3, 2], ![5, 0, 4, 6, 3, 1], ![4, 5, 6, 0, 2, 1], ![3, 5, 0, 2, 6, 1], ![3, 4, 2, 0, 6, 1], ![3, 0, 2, 4, 5, 1]], proof := .tail 39 }

theorem namedLeaf060_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3644)) namedLeaf060 = true :=
  by decide +kernel

def namedLeaf061 : LeafData := { rows := ![![1, 5, 2, 4, 6, 3], ![0, 6, 5, 4, 3, 2], ![5, 0, 6, 4, 3, 1], ![4, 5, 6, 0, 2, 1], ![3, 5, 0, 6, 2, 1], ![3, 4, 2, 0, 6, 1], ![3, 0, 4, 2, 5, 1]], proof := .tail 118 }

theorem namedLeaf061_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3645)) namedLeaf061 = true :=
  by decide +kernel

def namedLeaf062 : LeafData := { rows := ![![1, 5, 2, 6, 4, 3], ![0, 6, 5, 4, 3, 2], ![5, 0, 6, 4, 3, 1], ![4, 5, 6, 0, 2, 1], ![3, 5, 6, 0, 2, 1], ![3, 4, 2, 0, 6, 1], ![3, 4, 0, 2, 5, 1]], proof := .tail 54 }

theorem namedLeaf062_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3646)) namedLeaf062 = true :=
  by decide +kernel

def namedLeaf063 : LeafData := { rows := ![![1, 5, 6, 2, 4, 3], ![0, 5, 6, 4, 3, 2], ![5, 6, 0, 4, 3, 1], ![4, 5, 6, 0, 2, 1], ![3, 5, 6, 0, 2, 1], ![3, 4, 2, 0, 1, 6], ![3, 4, 2, 0, 1, 5]], proof := .tail 1 }

theorem namedLeaf063_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3647)) namedLeaf063 = true :=
  by decide +kernel

def namedLeaf064 : LeafData := { rows := ![![1, 5, 6, 2, 4, 3], ![0, 6, 5, 4, 3, 2], ![5, 6, 0, 4, 3, 1], ![4, 5, 6, 0, 2, 1], ![3, 5, 6, 0, 2, 1], ![3, 4, 2, 0, 6, 1], ![3, 4, 2, 0, 5, 1]], proof := .tail 1 }

theorem namedLeaf064_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3648)) namedLeaf064 = true :=
  by decide +kernel

def namedLeaf065 : LeafData := { rows := ![![1, 6, 5, 2, 4, 3], ![0, 6, 5, 4, 3, 2], ![5, 6, 0, 4, 3, 1], ![4, 5, 6, 0, 2, 1], ![3, 5, 6, 0, 2, 1], ![3, 4, 2, 6, 0, 1], ![3, 4, 2, 5, 0, 1]], proof := .tail 101 }

theorem namedLeaf065_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3649)) namedLeaf065 = true :=
  by decide +kernel

def namedLeaf066 : LeafData := { rows := ![![1, 6, 5, 2, 4, 3], ![0, 6, 5, 4, 3, 2], ![6, 5, 0, 4, 3, 1], ![4, 5, 6, 0, 2, 1], ![3, 5, 6, 0, 2, 1], ![3, 4, 6, 2, 0, 1], ![3, 4, 5, 2, 0, 1]], proof := .tail 125 }

theorem namedLeaf066_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3650)) namedLeaf066 = true :=
  by decide +kernel

def namedLeaf067 : LeafData := { rows := ![![1, 6, 5, 2, 4, 3], ![0, 6, 5, 4, 3, 2], ![6, 5, 0, 4, 3, 1], ![4, 5, 6, 0, 2, 1], ![3, 6, 5, 0, 2, 1], ![3, 6, 4, 2, 0, 1], ![3, 5, 4, 2, 0, 1]], proof := .tail 38 }

theorem namedLeaf067_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3651)) namedLeaf067 = true :=
  by decide +kernel

def namedLeaf068 : LeafData := { rows := ![![1, 6, 5, 2, 4, 3], ![0, 6, 5, 4, 3, 2], ![6, 5, 0, 4, 3, 1], ![4, 6, 5, 0, 2, 1], ![3, 6, 5, 0, 2, 1], ![6, 3, 4, 2, 0, 1], ![5, 3, 4, 2, 0, 1]], proof := .tail 96 }

theorem namedLeaf068_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3652)) namedLeaf068 = true :=
  by decide +kernel

def namedLeaf069 : LeafData := { rows := ![![1, 6, 5, 2, 4, 3], ![0, 6, 5, 4, 3, 2], ![6, 5, 0, 4, 3, 1], ![6, 4, 5, 0, 2, 1], ![6, 3, 5, 0, 2, 1], ![6, 3, 4, 2, 0, 1], ![5, 4, 3, 2, 0, 1]], proof := .tail 91 }

theorem namedLeaf069_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3653)) namedLeaf069 = true :=
  by decide +kernel

def namedLeaf070 : LeafData := { rows := ![![1, 5, 2, 4, 3, 6], ![0, 5, 2, 4, 3, 6], ![5, 0, 1, 4, 3, 6], ![5, 4, 0, 1, 2, 6], ![5, 3, 0, 1, 2, 6], ![4, 3, 2, 0, 1, 6], ![0, 1, 2, 3, 4, 5]], proof := .tail 114 }

theorem namedLeaf070_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3654)) namedLeaf070 = true :=
  by decide +kernel

def namedLeaf071 : LeafData := { rows := ![![1, 5, 2, 4, 3, 6], ![0, 5, 2, 4, 3, 6], ![5, 0, 1, 4, 6, 3], ![5, 4, 0, 1, 6, 2], ![5, 3, 0, 1, 2, 6], ![4, 3, 2, 0, 1, 6], ![0, 1, 3, 2, 4, 5]], proof := .tail 64 }

theorem namedLeaf071_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3655)) namedLeaf071 = true :=
  by decide +kernel

def namedLeaf072 : LeafData := { rows := ![![1, 5, 2, 4, 3, 6], ![0, 5, 2, 4, 3, 6], ![5, 0, 1, 6, 4, 3], ![5, 4, 0, 1, 6, 2], ![5, 3, 0, 1, 6, 2], ![4, 3, 2, 0, 1, 6], ![0, 1, 3, 4, 2, 5]], proof := .tail 117 }

theorem namedLeaf072_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3656)) namedLeaf072 = true :=
  by decide +kernel

def namedLeaf073 : LeafData := { rows := ![![1, 5, 2, 4, 3, 6], ![0, 5, 2, 4, 6, 3], ![5, 0, 1, 4, 6, 3], ![5, 4, 0, 6, 1, 2], ![5, 3, 0, 1, 2, 6], ![4, 3, 2, 0, 1, 6], ![0, 3, 1, 2, 4, 5]], proof := .tail 67 }

theorem namedLeaf073_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3657)) namedLeaf073 = true :=
  by decide +kernel

def namedLeaf074 : LeafData := { rows := ![![1, 5, 2, 4, 3, 6], ![0, 5, 2, 4, 6, 3], ![5, 0, 1, 6, 4, 3], ![5, 4, 0, 6, 1, 2], ![5, 3, 0, 1, 6, 2], ![4, 3, 2, 0, 1, 6], ![0, 3, 1, 4, 2, 5]], proof := .tail 117 }

theorem namedLeaf074_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3658)) namedLeaf074 = true :=
  by decide +kernel

def namedLeaf075 : LeafData := { rows := ![![1, 5, 2, 4, 3, 6], ![0, 5, 2, 6, 4, 3], ![5, 0, 1, 6, 4, 3], ![5, 4, 0, 6, 1, 2], ![5, 3, 0, 6, 1, 2], ![4, 3, 2, 0, 1, 6], ![0, 3, 4, 1, 2, 5]], proof := .tail 103 }

theorem namedLeaf075_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3659)) namedLeaf075 = true :=
  by decide +kernel

def namedLeaf076 : LeafData := { rows := ![![1, 5, 2, 4, 3, 6], ![0, 5, 6, 2, 4, 3], ![5, 0, 6, 1, 4, 3], ![5, 4, 0, 6, 1, 2], ![5, 3, 0, 6, 1, 2], ![4, 3, 2, 0, 1, 6], ![0, 3, 4, 2, 1, 5]], proof := .tail 0 }

theorem namedLeaf076_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3660)) namedLeaf076 = true :=
  by decide +kernel

def namedLeaf077 : LeafData := { rows := ![![1, 5, 2, 4, 6, 3], ![0, 5, 2, 4, 6, 3], ![5, 0, 1, 4, 6, 3], ![5, 4, 6, 0, 1, 2], ![5, 3, 0, 1, 2, 6], ![4, 3, 2, 0, 1, 6], ![3, 0, 1, 2, 4, 5]], proof := .tail 45 }

theorem namedLeaf077_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3661)) namedLeaf077 = true :=
  by decide +kernel

def namedLeaf078 : LeafData := { rows := ![![1, 5, 2, 4, 6, 3], ![0, 5, 2, 4, 6, 3], ![5, 0, 1, 6, 4, 3], ![5, 4, 6, 0, 1, 2], ![5, 3, 0, 1, 6, 2], ![4, 3, 2, 0, 1, 6], ![3, 0, 1, 4, 2, 5]], proof := .tail 99 }

theorem namedLeaf078_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3662)) namedLeaf078 = true :=
  by decide +kernel

def namedLeaf079 : LeafData := { rows := ![![1, 5, 2, 4, 6, 3], ![0, 5, 2, 6, 4, 3], ![5, 0, 1, 6, 4, 3], ![5, 4, 6, 0, 1, 2], ![5, 3, 0, 6, 1, 2], ![4, 3, 2, 0, 1, 6], ![3, 0, 4, 1, 2, 5]], proof := .tail 129 }

theorem namedLeaf079_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3663)) namedLeaf079 = true :=
  by decide +kernel

def namedLeaf080 : LeafData := { rows := ![![1, 5, 2, 6, 4, 3], ![0, 5, 2, 6, 4, 3], ![5, 0, 1, 6, 4, 3], ![5, 4, 6, 0, 1, 2], ![5, 3, 6, 0, 1, 2], ![4, 3, 2, 0, 1, 6], ![3, 4, 0, 1, 2, 5]], proof := .tail 72 }

theorem namedLeaf080_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3664)) namedLeaf080 = true :=
  by decide +kernel

def namedLeaf081 : LeafData := { rows := ![![1, 5, 2, 6, 4, 3], ![0, 5, 2, 6, 4, 3], ![5, 0, 1, 6, 4, 3], ![5, 6, 4, 0, 1, 2], ![5, 6, 3, 0, 1, 2], ![4, 3, 2, 0, 1, 6], ![4, 3, 0, 1, 2, 5]], proof := .low (![23, 31, 33, 131, 83, 62, 52, 2, 69, 27, 8, 21, 6, 106, 109, 95, 43, 123, 121, 106, 106, 106, 102, 81, 77, 56, 126, 82]) }

theorem namedLeaf081_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3665)) namedLeaf081 = true :=
  by decide +kernel

def namedLeaf082 : LeafData := { rows := ![![1, 5, 2, 4, 6, 3], ![0, 5, 6, 2, 4, 3], ![5, 0, 6, 1, 4, 3], ![5, 4, 6, 0, 1, 2], ![5, 3, 0, 6, 1, 2], ![4, 3, 2, 0, 1, 6], ![3, 0, 4, 2, 1, 5]], proof := .tail 26 }

theorem namedLeaf082_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3666)) namedLeaf082 = true :=
  by decide +kernel

def namedLeaf083 : LeafData := { rows := ![![1, 5, 2, 6, 4, 3], ![0, 5, 6, 2, 4, 3], ![5, 0, 6, 1, 4, 3], ![5, 4, 6, 0, 1, 2], ![5, 3, 6, 0, 1, 2], ![4, 3, 2, 0, 1, 6], ![3, 4, 0, 2, 1, 5]], proof := .tail 80 }

theorem namedLeaf083_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3667)) namedLeaf083 = true :=
  by decide +kernel

def namedLeaf084 : LeafData := { rows := ![![1, 5, 2, 6, 4, 3], ![0, 5, 6, 2, 4, 3], ![5, 0, 6, 1, 4, 3], ![5, 6, 4, 0, 1, 2], ![5, 6, 3, 0, 1, 2], ![4, 3, 2, 0, 1, 6], ![4, 3, 0, 2, 1, 5]], proof := .tail 7 }

theorem namedLeaf084_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3668)) namedLeaf084 = true :=
  by decide +kernel

def namedLeaf085 : LeafData := { rows := ![![1, 5, 2, 4, 3, 6], ![0, 6, 5, 2, 4, 3], ![5, 0, 6, 1, 4, 3], ![5, 4, 0, 6, 1, 2], ![5, 3, 0, 6, 1, 2], ![4, 3, 2, 0, 6, 1], ![0, 3, 4, 2, 5, 1]], proof := .tail 29 }

theorem namedLeaf085_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3669)) namedLeaf085 = true :=
  by decide +kernel

def namedLeaf086 : LeafData := { rows := ![![1, 5, 2, 4, 6, 3], ![0, 6, 5, 2, 4, 3], ![5, 0, 6, 1, 4, 3], ![5, 4, 6, 0, 1, 2], ![5, 3, 0, 6, 1, 2], ![4, 3, 2, 0, 6, 1], ![3, 0, 4, 2, 5, 1]], proof := .tail 89 }

theorem namedLeaf086_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3670)) namedLeaf086 = true :=
  by decide +kernel

def namedLeaf087 : LeafData := { rows := ![![1, 5, 2, 6, 4, 3], ![0, 6, 5, 2, 4, 3], ![5, 0, 6, 1, 4, 3], ![5, 4, 6, 0, 1, 2], ![5, 3, 6, 0, 1, 2], ![4, 3, 2, 0, 6, 1], ![3, 4, 0, 2, 5, 1]], proof := .tail 89 }

theorem namedLeaf087_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3671)) namedLeaf087 = true :=
  by decide +kernel

def namedLeaf088 : LeafData := { rows := ![![1, 5, 2, 6, 4, 3], ![0, 6, 5, 2, 4, 3], ![5, 0, 6, 1, 4, 3], ![5, 6, 4, 0, 1, 2], ![5, 6, 3, 0, 1, 2], ![4, 3, 2, 0, 6, 1], ![4, 3, 0, 2, 5, 1]], proof := .tail 115 }

theorem namedLeaf088_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3672)) namedLeaf088 = true :=
  by decide +kernel

def namedLeaf089 : LeafData := { rows := ![![1, 5, 6, 2, 4, 3], ![0, 5, 6, 2, 4, 3], ![5, 6, 0, 1, 4, 3], ![5, 4, 6, 0, 1, 2], ![5, 3, 6, 0, 1, 2], ![4, 3, 2, 0, 1, 6], ![3, 4, 2, 0, 1, 5]], proof := .tail 133 }

theorem namedLeaf089_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3673)) namedLeaf089 = true :=
  by decide +kernel

def namedLeaf090 : LeafData := { rows := ![![1, 5, 6, 2, 4, 3], ![0, 6, 5, 2, 4, 3], ![5, 6, 0, 1, 4, 3], ![5, 4, 6, 0, 1, 2], ![5, 3, 6, 0, 1, 2], ![4, 3, 2, 0, 6, 1], ![3, 4, 2, 0, 5, 1]], proof := .tail 89 }

theorem namedLeaf090_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3674)) namedLeaf090 = true :=
  by decide +kernel

def namedLeaf091 : LeafData := { rows := ![![1, 6, 5, 2, 4, 3], ![0, 6, 5, 2, 4, 3], ![5, 6, 0, 1, 4, 3], ![5, 4, 6, 0, 1, 2], ![5, 3, 6, 0, 1, 2], ![4, 3, 2, 6, 0, 1], ![3, 4, 2, 5, 0, 1]], proof := .tail 13 }

theorem namedLeaf091_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3675)) namedLeaf091 = true :=
  by decide +kernel

def namedLeaf092 : LeafData := { rows := ![![1, 6, 5, 2, 4, 3], ![0, 6, 5, 2, 4, 3], ![6, 5, 0, 1, 4, 3], ![5, 4, 6, 0, 1, 2], ![5, 3, 6, 0, 1, 2], ![4, 3, 6, 2, 0, 1], ![3, 4, 5, 2, 0, 1]], proof := .tail 128 }

theorem namedLeaf092_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3676)) namedLeaf092 = true :=
  by decide +kernel

def namedLeaf093 : LeafData := { rows := ![![1, 5, 6, 2, 4, 3], ![0, 5, 6, 2, 4, 3], ![5, 6, 0, 1, 4, 3], ![5, 6, 4, 0, 1, 2], ![5, 6, 3, 0, 1, 2], ![4, 3, 2, 0, 1, 6], ![4, 3, 2, 0, 1, 5]], proof := .low (![32, 14, 59, 25, 48, 12, 52, 73, 4, 68, 134, 21, 6, 3, 98, 60, 100, 123, 112, 130, 65, 11, 124, 55, 28, 40, 78, 76]) }

theorem namedLeaf093_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3677)) namedLeaf093 = true :=
  by decide +kernel

def namedLeaf094 : LeafData := { rows := ![![1, 5, 6, 2, 4, 3], ![0, 6, 5, 2, 4, 3], ![5, 6, 0, 1, 4, 3], ![5, 6, 4, 0, 1, 2], ![5, 6, 3, 0, 1, 2], ![4, 3, 2, 0, 6, 1], ![4, 3, 2, 0, 5, 1]], proof := .tail 115 }

theorem namedLeaf094_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3678)) namedLeaf094 = true :=
  by decide +kernel

def namedLeaf095 : LeafData := { rows := ![![1, 6, 5, 2, 4, 3], ![0, 6, 5, 2, 4, 3], ![5, 6, 0, 1, 4, 3], ![5, 6, 4, 0, 1, 2], ![5, 6, 3, 0, 1, 2], ![4, 3, 2, 6, 0, 1], ![4, 3, 2, 5, 0, 1]], proof := .tail 79 }

theorem namedLeaf095_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3679)) namedLeaf095 = true :=
  by decide +kernel

def namedLeaf096 : LeafData := { rows := ![![1, 6, 5, 2, 4, 3], ![0, 6, 5, 2, 4, 3], ![6, 5, 0, 1, 4, 3], ![5, 6, 4, 0, 1, 2], ![5, 6, 3, 0, 1, 2], ![4, 3, 6, 2, 0, 1], ![4, 3, 5, 2, 0, 1]], proof := .tail 128 }

theorem namedLeaf096_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3680)) namedLeaf096 = true :=
  by decide +kernel

def namedLeaf097 : LeafData := { rows := ![![1, 6, 5, 2, 4, 3], ![0, 6, 5, 2, 4, 3], ![6, 5, 0, 1, 4, 3], ![6, 5, 4, 0, 1, 2], ![5, 6, 3, 0, 1, 2], ![4, 6, 3, 2, 0, 1], ![4, 5, 3, 2, 0, 1]], proof := .tail 50 }

theorem namedLeaf097_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3681)) namedLeaf097 = true :=
  by decide +kernel

def namedLeaf098 : LeafData := { rows := ![![1, 6, 5, 2, 4, 3], ![0, 6, 5, 2, 4, 3], ![6, 5, 0, 1, 4, 3], ![6, 5, 4, 0, 1, 2], ![6, 5, 3, 0, 1, 2], ![6, 4, 3, 2, 0, 1], ![5, 4, 3, 2, 0, 1]], proof := .tail 9 }

theorem namedLeaf098_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3682)) namedLeaf098 = true :=
  by decide +kernel

def namedLeaf099 : LeafData := { rows := ![![1, 5, 2, 4, 3, 6], ![0, 5, 4, 2, 3, 6], ![5, 0, 4, 1, 3, 6], ![5, 4, 0, 1, 2, 6], ![5, 3, 0, 2, 1, 6], ![4, 3, 2, 0, 1, 6], ![0, 1, 2, 3, 4, 5]], proof := .tail 53 }

theorem namedLeaf099_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3683)) namedLeaf099 = true :=
  by decide +kernel

def namedLeaf100 : LeafData := { rows := ![![1, 5, 2, 4, 3, 6], ![0, 5, 4, 2, 3, 6], ![5, 0, 4, 1, 6, 3], ![5, 4, 0, 1, 6, 2], ![5, 3, 0, 2, 1, 6], ![4, 3, 2, 0, 1, 6], ![0, 1, 3, 2, 4, 5]], proof := .tail 57 }

theorem namedLeaf100_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3684)) namedLeaf100 = true :=
  by decide +kernel

def namedLeaf101 : LeafData := { rows := ![![1, 5, 2, 4, 3, 6], ![0, 5, 4, 2, 6, 3], ![5, 0, 4, 1, 6, 3], ![5, 4, 0, 6, 1, 2], ![5, 3, 0, 2, 1, 6], ![4, 3, 2, 0, 1, 6], ![0, 3, 1, 2, 4, 5]], proof := .tail 30 }

theorem namedLeaf101_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3685)) namedLeaf101 = true :=
  by decide +kernel

def namedLeaf102 : LeafData := { rows := ![![1, 5, 2, 4, 3, 6], ![0, 5, 4, 6, 2, 3], ![5, 0, 4, 6, 1, 3], ![5, 4, 0, 6, 1, 2], ![5, 3, 0, 2, 1, 6], ![4, 3, 2, 0, 1, 6], ![0, 3, 2, 1, 4, 5]], proof := .tail 47 }

theorem namedLeaf102_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3686)) namedLeaf102 = true :=
  by decide +kernel

def namedLeaf103 : LeafData := { rows := ![![1, 5, 2, 4, 3, 6], ![0, 5, 6, 4, 2, 3], ![5, 0, 4, 6, 1, 3], ![5, 4, 0, 6, 1, 2], ![5, 3, 0, 2, 6, 1], ![4, 3, 2, 0, 1, 6], ![0, 3, 2, 4, 1, 5]], proof := .tail 110 }

theorem namedLeaf103_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3687)) namedLeaf103 = true :=
  by decide +kernel

def namedLeaf104 : LeafData := { rows := ![![1, 5, 2, 4, 3, 6], ![0, 5, 6, 4, 2, 3], ![5, 0, 6, 4, 1, 3], ![5, 4, 0, 6, 1, 2], ![5, 3, 0, 6, 2, 1], ![4, 3, 2, 0, 1, 6], ![0, 3, 4, 2, 1, 5]], proof := .tail 90 }

theorem namedLeaf104_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3688)) namedLeaf104 = true :=
  by decide +kernel

def namedLeaf105 : LeafData := { rows := ![![1, 5, 2, 4, 6, 3], ![0, 5, 4, 2, 6, 3], ![5, 0, 4, 1, 6, 3], ![5, 4, 6, 0, 1, 2], ![5, 3, 0, 2, 1, 6], ![4, 3, 2, 0, 1, 6], ![3, 0, 1, 2, 4, 5]], proof := .tail 30 }

theorem namedLeaf105_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3689)) namedLeaf105 = true :=
  by decide +kernel

def namedLeaf106 : LeafData := { rows := ![![1, 5, 2, 4, 6, 3], ![0, 5, 4, 6, 2, 3], ![5, 0, 4, 6, 1, 3], ![5, 4, 6, 0, 1, 2], ![5, 3, 0, 2, 1, 6], ![4, 3, 2, 0, 1, 6], ![3, 0, 2, 1, 4, 5]], proof := .tail 15 }

theorem namedLeaf106_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3690)) namedLeaf106 = true :=
  by decide +kernel

def namedLeaf107 : LeafData := { rows := ![![1, 5, 2, 4, 6, 3], ![0, 5, 6, 4, 2, 3], ![5, 0, 4, 6, 1, 3], ![5, 4, 6, 0, 1, 2], ![5, 3, 0, 2, 6, 1], ![4, 3, 2, 0, 1, 6], ![3, 0, 2, 4, 1, 5]], proof := .tail 110 }

theorem namedLeaf107_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3691)) namedLeaf107 = true :=
  by decide +kernel

def namedLeaf108 : LeafData := { rows := ![![1, 5, 2, 4, 6, 3], ![0, 5, 6, 4, 2, 3], ![5, 0, 6, 4, 1, 3], ![5, 4, 6, 0, 1, 2], ![5, 3, 0, 6, 2, 1], ![4, 3, 2, 0, 1, 6], ![3, 0, 4, 2, 1, 5]], proof := .tail 90 }

theorem namedLeaf108_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3692)) namedLeaf108 = true :=
  by decide +kernel

def namedLeaf109 : LeafData := { rows := ![![1, 5, 2, 6, 4, 3], ![0, 5, 6, 4, 2, 3], ![5, 0, 6, 4, 1, 3], ![5, 4, 6, 0, 1, 2], ![5, 3, 6, 0, 2, 1], ![4, 3, 2, 0, 1, 6], ![3, 4, 0, 2, 1, 5]], proof := .tail 90 }

theorem namedLeaf109_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3693)) namedLeaf109 = true :=
  by decide +kernel

def namedLeaf110 : LeafData := { rows := ![![1, 5, 2, 6, 4, 3], ![0, 5, 6, 4, 2, 3], ![5, 0, 6, 4, 1, 3], ![5, 6, 4, 0, 1, 2], ![5, 6, 3, 0, 2, 1], ![4, 3, 2, 0, 1, 6], ![4, 3, 0, 2, 1, 5]], proof := .tail 84 }

theorem namedLeaf110_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3694)) namedLeaf110 = true :=
  by decide +kernel

def namedLeaf111 : LeafData := { rows := ![![1, 5, 2, 4, 3, 6], ![0, 6, 5, 4, 2, 3], ![5, 0, 4, 6, 1, 3], ![5, 4, 0, 6, 1, 2], ![5, 3, 0, 2, 6, 1], ![4, 3, 2, 0, 6, 1], ![0, 3, 2, 4, 5, 1]], proof := .tail 93 }

theorem namedLeaf111_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3695)) namedLeaf111 = true :=
  by decide +kernel

def namedLeaf112 : LeafData := { rows := ![![1, 5, 2, 4, 3, 6], ![0, 6, 5, 4, 2, 3], ![5, 0, 6, 4, 1, 3], ![5, 4, 0, 6, 1, 2], ![5, 3, 0, 6, 2, 1], ![4, 3, 2, 0, 6, 1], ![0, 3, 4, 2, 5, 1]], proof := .tail 90 }

theorem namedLeaf112_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3696)) namedLeaf112 = true :=
  by decide +kernel

def namedLeaf113 : LeafData := { rows := ![![1, 5, 2, 4, 6, 3], ![0, 6, 5, 4, 2, 3], ![5, 0, 4, 6, 1, 3], ![5, 4, 6, 0, 1, 2], ![5, 3, 0, 2, 6, 1], ![4, 3, 2, 0, 6, 1], ![3, 0, 2, 4, 5, 1]], proof := .tail 93 }

theorem namedLeaf113_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3697)) namedLeaf113 = true :=
  by decide +kernel

def namedLeaf114 : LeafData := { rows := ![![1, 5, 2, 4, 6, 3], ![0, 6, 5, 4, 2, 3], ![5, 0, 6, 4, 1, 3], ![5, 4, 6, 0, 1, 2], ![5, 3, 0, 6, 2, 1], ![4, 3, 2, 0, 6, 1], ![3, 0, 4, 2, 5, 1]], proof := .tail 90 }

theorem namedLeaf114_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3698)) namedLeaf114 = true :=
  by decide +kernel

def namedLeaf115 : LeafData := { rows := ![![1, 5, 2, 6, 4, 3], ![0, 6, 5, 4, 2, 3], ![5, 0, 6, 4, 1, 3], ![5, 4, 6, 0, 1, 2], ![5, 3, 6, 0, 2, 1], ![4, 3, 2, 0, 6, 1], ![3, 4, 0, 2, 5, 1]], proof := .tail 90 }

theorem namedLeaf115_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3699)) namedLeaf115 = true :=
  by decide +kernel

def namedLeaf116 : LeafData := { rows := ![![1, 5, 2, 6, 4, 3], ![0, 6, 5, 4, 2, 3], ![5, 0, 6, 4, 1, 3], ![5, 6, 4, 0, 1, 2], ![5, 6, 3, 0, 2, 1], ![4, 3, 2, 0, 6, 1], ![4, 3, 0, 2, 5, 1]], proof := .tail 37 }

theorem namedLeaf116_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3700)) namedLeaf116 = true :=
  by decide +kernel

def namedLeaf117 : LeafData := { rows := ![![1, 5, 6, 2, 4, 3], ![0, 5, 6, 4, 2, 3], ![5, 6, 0, 4, 1, 3], ![5, 4, 6, 0, 1, 2], ![5, 3, 6, 0, 2, 1], ![4, 3, 2, 0, 1, 6], ![3, 4, 2, 0, 1, 5]], proof := .tail 104 }

theorem namedLeaf117_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3701)) namedLeaf117 = true :=
  by decide +kernel

def namedLeaf118 : LeafData := { rows := ![![1, 5, 6, 2, 4, 3], ![0, 6, 5, 4, 2, 3], ![5, 6, 0, 4, 1, 3], ![5, 4, 6, 0, 1, 2], ![5, 3, 6, 0, 2, 1], ![4, 3, 2, 0, 6, 1], ![3, 4, 2, 0, 5, 1]], proof := .tail 104 }

theorem namedLeaf118_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3702)) namedLeaf118 = true :=
  by decide +kernel

def namedLeaf119 : LeafData := { rows := ![![1, 6, 5, 2, 4, 3], ![0, 6, 5, 4, 2, 3], ![5, 6, 0, 4, 1, 3], ![5, 4, 6, 0, 1, 2], ![5, 3, 6, 0, 2, 1], ![4, 3, 2, 6, 0, 1], ![3, 4, 2, 5, 0, 1]], proof := .tail 66 }

theorem namedLeaf119_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3703)) namedLeaf119 = true :=
  by decide +kernel

def namedLeaf120 : LeafData := { rows := ![![1, 6, 5, 2, 4, 3], ![0, 6, 5, 4, 2, 3], ![6, 5, 0, 4, 1, 3], ![5, 4, 6, 0, 1, 2], ![5, 3, 6, 0, 2, 1], ![4, 3, 6, 2, 0, 1], ![3, 4, 5, 2, 0, 1]], proof := .tail 113 }

theorem namedLeaf120_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3704)) namedLeaf120 = true :=
  by decide +kernel

def namedLeaf121 : LeafData := { rows := ![![1, 5, 6, 2, 4, 3], ![0, 5, 6, 4, 2, 3], ![5, 6, 0, 4, 1, 3], ![5, 6, 4, 0, 1, 2], ![5, 6, 3, 0, 2, 1], ![4, 3, 2, 0, 1, 6], ![4, 3, 2, 0, 1, 5]], proof := .tail 120 }

theorem namedLeaf121_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3705)) namedLeaf121 = true :=
  by decide +kernel

def namedLeaf122 : LeafData := { rows := ![![1, 5, 6, 2, 4, 3], ![0, 6, 5, 4, 2, 3], ![5, 6, 0, 4, 1, 3], ![5, 6, 4, 0, 1, 2], ![5, 6, 3, 0, 2, 1], ![4, 3, 2, 0, 6, 1], ![4, 3, 2, 0, 5, 1]], proof := .tail 120 }

theorem namedLeaf122_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3706)) namedLeaf122 = true :=
  by decide +kernel

def namedLeaf123 : LeafData := { rows := ![![1, 6, 5, 2, 4, 3], ![0, 6, 5, 4, 2, 3], ![5, 6, 0, 4, 1, 3], ![5, 6, 4, 0, 1, 2], ![5, 6, 3, 0, 2, 1], ![4, 3, 2, 6, 0, 1], ![4, 3, 2, 5, 0, 1]], proof := .tail 111 }

theorem namedLeaf123_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3707)) namedLeaf123 = true :=
  by decide +kernel

def namedLeaf124 : LeafData := { rows := ![![1, 6, 5, 2, 4, 3], ![0, 6, 5, 4, 2, 3], ![6, 5, 0, 4, 1, 3], ![5, 6, 4, 0, 1, 2], ![5, 6, 3, 0, 2, 1], ![4, 3, 6, 2, 0, 1], ![4, 3, 5, 2, 0, 1]], proof := .tail 113 }

theorem namedLeaf124_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3708)) namedLeaf124 = true :=
  by decide +kernel

def namedLeaf125 : LeafData := { rows := ![![1, 6, 5, 2, 4, 3], ![0, 6, 5, 4, 2, 3], ![6, 5, 0, 4, 1, 3], ![6, 5, 4, 0, 1, 2], ![5, 6, 3, 0, 2, 1], ![4, 6, 3, 2, 0, 1], ![4, 5, 3, 2, 0, 1]], proof := .tail 42 }

theorem namedLeaf125_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3709)) namedLeaf125 = true :=
  by decide +kernel

def namedLeaf126 : LeafData := { rows := ![![1, 6, 5, 2, 4, 3], ![0, 6, 5, 4, 2, 3], ![6, 5, 0, 4, 1, 3], ![6, 5, 4, 0, 1, 2], ![6, 5, 3, 0, 2, 1], ![6, 4, 3, 2, 0, 1], ![5, 4, 3, 2, 0, 1]], proof := .tail 51 }

theorem namedLeaf126_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3710)) namedLeaf126 = true :=
  by decide +kernel

def namedLeaf127 : LeafData := { rows := ![![1, 5, 2, 4, 3, 6], ![0, 5, 4, 3, 2, 6], ![5, 0, 4, 3, 1, 6], ![5, 4, 0, 2, 1, 6], ![5, 3, 0, 2, 1, 6], ![4, 3, 2, 0, 1, 6], ![0, 1, 2, 3, 4, 5]], proof := .tail 92 }

theorem namedLeaf127_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3711)) namedLeaf127 = true :=
  by decide +kernel

def fallback : LeafData := { rows := fun _ _ => 0, proof := .tail 0 }
def lookup (offset : ℕ) : LeafData :=
  if offset < 128 then (if offset < 64 then (if offset < 32 then (if offset < 16 then (if offset < 8 then (if offset < 4 then (if offset < 2 then (if offset < 1 then (namedLeaf000) else (namedLeaf001)) else (if offset < 3 then (namedLeaf002) else (namedLeaf003))) else (if offset < 6 then (if offset < 5 then (namedLeaf004) else (namedLeaf005)) else (if offset < 7 then (namedLeaf006) else (namedLeaf007)))) else (if offset < 12 then (if offset < 10 then (if offset < 9 then (namedLeaf008) else (namedLeaf009)) else (if offset < 11 then (namedLeaf010) else (namedLeaf011))) else (if offset < 14 then (if offset < 13 then (namedLeaf012) else (namedLeaf013)) else (if offset < 15 then (namedLeaf014) else (namedLeaf015))))) else (if offset < 24 then (if offset < 20 then (if offset < 18 then (if offset < 17 then (namedLeaf016) else (namedLeaf017)) else (if offset < 19 then (namedLeaf018) else (namedLeaf019))) else (if offset < 22 then (if offset < 21 then (namedLeaf020) else (namedLeaf021)) else (if offset < 23 then (namedLeaf022) else (namedLeaf023)))) else (if offset < 28 then (if offset < 26 then (if offset < 25 then (namedLeaf024) else (namedLeaf025)) else (if offset < 27 then (namedLeaf026) else (namedLeaf027))) else (if offset < 30 then (if offset < 29 then (namedLeaf028) else (namedLeaf029)) else (if offset < 31 then (namedLeaf030) else (namedLeaf031)))))) else (if offset < 48 then (if offset < 40 then (if offset < 36 then (if offset < 34 then (if offset < 33 then (namedLeaf032) else (namedLeaf033)) else (if offset < 35 then (namedLeaf034) else (namedLeaf035))) else (if offset < 38 then (if offset < 37 then (namedLeaf036) else (namedLeaf037)) else (if offset < 39 then (namedLeaf038) else (namedLeaf039)))) else (if offset < 44 then (if offset < 42 then (if offset < 41 then (namedLeaf040) else (namedLeaf041)) else (if offset < 43 then (namedLeaf042) else (namedLeaf043))) else (if offset < 46 then (if offset < 45 then (namedLeaf044) else (namedLeaf045)) else (if offset < 47 then (namedLeaf046) else (namedLeaf047))))) else (if offset < 56 then (if offset < 52 then (if offset < 50 then (if offset < 49 then (namedLeaf048) else (namedLeaf049)) else (if offset < 51 then (namedLeaf050) else (namedLeaf051))) else (if offset < 54 then (if offset < 53 then (namedLeaf052) else (namedLeaf053)) else (if offset < 55 then (namedLeaf054) else (namedLeaf055)))) else (if offset < 60 then (if offset < 58 then (if offset < 57 then (namedLeaf056) else (namedLeaf057)) else (if offset < 59 then (namedLeaf058) else (namedLeaf059))) else (if offset < 62 then (if offset < 61 then (namedLeaf060) else (namedLeaf061)) else (if offset < 63 then (namedLeaf062) else (namedLeaf063))))))) else (if offset < 96 then (if offset < 80 then (if offset < 72 then (if offset < 68 then (if offset < 66 then (if offset < 65 then (namedLeaf064) else (namedLeaf065)) else (if offset < 67 then (namedLeaf066) else (namedLeaf067))) else (if offset < 70 then (if offset < 69 then (namedLeaf068) else (namedLeaf069)) else (if offset < 71 then (namedLeaf070) else (namedLeaf071)))) else (if offset < 76 then (if offset < 74 then (if offset < 73 then (namedLeaf072) else (namedLeaf073)) else (if offset < 75 then (namedLeaf074) else (namedLeaf075))) else (if offset < 78 then (if offset < 77 then (namedLeaf076) else (namedLeaf077)) else (if offset < 79 then (namedLeaf078) else (namedLeaf079))))) else (if offset < 88 then (if offset < 84 then (if offset < 82 then (if offset < 81 then (namedLeaf080) else (namedLeaf081)) else (if offset < 83 then (namedLeaf082) else (namedLeaf083))) else (if offset < 86 then (if offset < 85 then (namedLeaf084) else (namedLeaf085)) else (if offset < 87 then (namedLeaf086) else (namedLeaf087)))) else (if offset < 92 then (if offset < 90 then (if offset < 89 then (namedLeaf088) else (namedLeaf089)) else (if offset < 91 then (namedLeaf090) else (namedLeaf091))) else (if offset < 94 then (if offset < 93 then (namedLeaf092) else (namedLeaf093)) else (if offset < 95 then (namedLeaf094) else (namedLeaf095)))))) else (if offset < 112 then (if offset < 104 then (if offset < 100 then (if offset < 98 then (if offset < 97 then (namedLeaf096) else (namedLeaf097)) else (if offset < 99 then (namedLeaf098) else (namedLeaf099))) else (if offset < 102 then (if offset < 101 then (namedLeaf100) else (namedLeaf101)) else (if offset < 103 then (namedLeaf102) else (namedLeaf103)))) else (if offset < 108 then (if offset < 106 then (if offset < 105 then (namedLeaf104) else (namedLeaf105)) else (if offset < 107 then (namedLeaf106) else (namedLeaf107))) else (if offset < 110 then (if offset < 109 then (namedLeaf108) else (namedLeaf109)) else (if offset < 111 then (namedLeaf110) else (namedLeaf111))))) else (if offset < 120 then (if offset < 116 then (if offset < 114 then (if offset < 113 then (namedLeaf112) else (namedLeaf113)) else (if offset < 115 then (namedLeaf114) else (namedLeaf115))) else (if offset < 118 then (if offset < 117 then (namedLeaf116) else (namedLeaf117)) else (if offset < 119 then (namedLeaf118) else (namedLeaf119)))) else (if offset < 124 then (if offset < 122 then (if offset < 121 then (namedLeaf120) else (namedLeaf121)) else (if offset < 123 then (namedLeaf122) else (namedLeaf123))) else (if offset < 126 then (if offset < 125 then (namedLeaf124) else (namedLeaf125)) else (if offset < 127 then (namedLeaf126) else (namedLeaf127)))))))) else fallback

theorem point_checked (j : Fin 128) :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 (3584 + j.val))) (lookup j.val) = true := by
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

theorem correct (id : Fin 24698) (hlow : 3584 ≤ id.val) (hhigh : id.val < 3712) :
    leafCheck library (N4R2WordTree.catalog id) (lookup (id.val - 3584)) = true := by
  let j : Fin 128 := ⟨id.val - 3584, by omega⟩
  have hsum : 3584 + j.val = id.val := by dsimp [j]; omega
  have hindex : Fin.ofNat 24698 (3584 + j.val) = id := by
    apply Fin.ext
    simp only [Fin.ofNat, hsum, Nat.mod_eq_of_lt id.isLt]
  have hh := point_checked j
  rw [hindex] at hh
  exact hh

#print axioms point_checked
#print axioms correct
end Jsp404.N4R2OuterLeftData.LeafShard028
