import Jsp000404.N4R2OuterLeftReplay
import Jsp000404.N4R2WordCatalog

set_option autoImplicit false
set_option pp.fullNames true
set_option maxRecDepth 8192
set_option maxHeartbeats 0
set_option Elab.async false

namespace Jsp404.N4R2OuterLeftData.LeafShard048
open N4R2OuterLeftReplay

-- Cycle fingerprint 00087287d178cb5a8d8768c8a6c4117171518fad4c05a28425d84bee68607464.
def localCycle00000 : Cycle where
  length := 8
  data := {
    node := ![.distance 3 5, .distance 2 3, .theta 2, .distance 1 2, .distance 1 4, .distance 1 3, .distance 1 6, .distance 1 5, .distance 3 5]
    constant := ![-1, -1, 3, 0, -2, 0, -2, 0]
    coefficient := ![0, 0, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true, false, true] }
  origin := ![.triangle 26 0, .corridorLower 2 3, .corridorUpper 1 2, .triangle 16 2, .gapLower 1 4, .triangle 21 2, .gapLower 1 2, .triangle 20 1]

-- Cycle fingerprint 027d544019302db6033958b49be404c8646c372300689f14be8c4fc8492cfa4e.
def localCycle00001 : Cycle where
  length := 8
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 4, .distance 4 5, .distance 0 4, .distance 0 3, .distance 3 6, .distance 2 3, .theta 2]
    constant := ![3, 0, -1, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 16 2, .triangle 22 0, .triangle 12 0, .triangle 9 1, .triangle 11 0, .triangle 27 0, .corridorLower 2 3]

-- Cycle fingerprint 04f89407b4d8b153ae53e6a7c8ad8552e728d2ed502235a86965e2b320b16b7c.
def localCycle00002 : Cycle where
  length := 6
  data := {
    node := ![.distance 1 3, .distance 3 5, .distance 2 3, .theta 2, .distance 1 2, .distance 1 4, .distance 1 3]
    constant := ![-1, -1, -1, 3, -3, 0]
    coefficient := ![0, 0, 0, 1, 0, 0]
    strict := ![false, false, false, false, false, true] }
  origin := ![.triangle 20 0, .triangle 26 0, .corridorLower 2 3, .corridorUpper 1 2, .gapLower 1 5, .triangle 19 1]

-- Cycle fingerprint 0525179cba5a28e40cdc3a75365d0f9f68257e1b4bd50ec61821129ce70b2a90.
def localCycle00003 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .theta 1, .distance 1 2, .distance 1 4, .distance 1 6, .distance 1 3, .distance 0 3, .distance 3 5, .distance 2 3, .theta 2]
    constant := ![0, 2, 0, 0, -2, 0, -1, -1, -1]
    coefficient := ![0, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![true, false, true, true, false, true, false, false, false] }
  origin := ![.thetaNext 1, .gapLower 1 6, .triangle 16 2, .triangle 23 2, .gapLower 1 3, .triangle 1 2, .triangle 10 0, .triangle 26 0, .corridorLower 2 3]

-- Cycle fingerprint 056d22a9891d7eb5a14624560d3d7551d37ba67b73bc048901769a754e6778bf.
def localCycle00004 : Cycle where
  length := 5
  data := {
    node := ![.distance 1 5, .distance 5 6, .distance 3 6, .distance 1 6, .distance 1 3, .distance 1 5]
    constant := ![2, 0, 0, -3, 0]
    coefficient := ![0, 0, 0, 0, 0]
    strict := ![true, false, false, false, true] }
  origin := ![.gapUpper 5 5, .gapLower 6 5, .gapLower 6 4, .gapLower 1 3, .triangle 20 2]

-- Cycle fingerprint 064e88219e11c798a3818d605c9ebb1afc43fb4f9b71f03a614fc787addcbdcd.
def localCycle00005 : Cycle where
  length := 13
  data := {
    node := ![.distance 2 3, .theta 2, .theta 1, .distance 1 2, .distance 0 2, .distance 2 4, .distance 4 6, .distance 4 5, .theta 4, .distance 3 4, .distance 0 3, .distance 3 6, .distance 3 5, .distance 2 3]
    constant := ![-1, 0, 2, 0, -1, -1, 0, -1, 3, -1, -1, 0, -1]
    coefficient := ![0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, true, false, false, false, false, true, false] }
  origin := ![.corridorLower 2 3, .thetaNext 1, .gapLower 1 6, .triangle 0 2, .triangle 6 0, .triangle 29 0, .triangle 34 1, .corridorLower 4 5, .corridorUpper 3 4, .triangle 9 0, .triangle 11 0, .triangle 33 1, .triangle 26 0]

-- Cycle fingerprint 0696b512db3b0f76eab19dbf19ffeff0f631a81548f0442f52463d39b576e063.
def localCycle00006 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .theta 1, .distance 1 2, .distance 1 4, .distance 1 3, .distance 1 6, .distance 0 6, .distance 3 6, .distance 2 3, .theta 2]
    constant := ![0, 2, 0, 0, -2, 0, 0, -1, -1]
    coefficient := ![0, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![true, false, true, true, false, true, true, false, false] }
  origin := ![.thetaNext 1, .gapLower 1 6, .triangle 16 2, .triangle 19 1, .gapLower 1 3, .triangle 4 2, .triangle 11 1, .triangle 27 0, .corridorLower 2 3]

-- Cycle fingerprint 08143e260dfdb348566c13f3eece02d84f61035cee9847b41dde78844c5a410b.
def localCycle00007 : Cycle where
  length := 8
  data := {
    node := ![.distance 1 3, .distance 3 5, .distance 2 3, .theta 2, .theta 1, .distance 1 2, .distance 1 4, .distance 1 6, .distance 1 3]
    constant := ![-1, -1, -1, 0, 2, 0, 0, -2]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, true, false, true, true, false] }
  origin := ![.triangle 20 0, .triangle 26 0, .corridorLower 2 3, .thetaNext 1, .gapLower 1 6, .triangle 16 2, .triangle 23 2, .gapLower 1 3]

-- Cycle fingerprint 08b4a54d2a160328e30bb09c2177dd1c228f4cce1fb5b1d338acb9ef80fa603c.
def localCycle00008 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 1 4, .distance 1 3, .distance 1 5, .distance 0 1]
    constant := ![-1, 0, 0, 3, -2, 0, 0, -2]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, false] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .gapLower 1 5, .triangle 19 1, .triangle 20 2, .gapLower 1 1]

-- Cycle fingerprint 08e0302c87d76f977fc45aba901641bd6a40867a44e8bbfd9d3a5fe842c120a5.
def localCycle00009 : Cycle where
  length := 8
  data := {
    node := ![.distance 3 4, .distance 1 3, .distance 3 5, .distance 0 3, .distance 0 1, .theta 1, .zero, .theta 4, .distance 3 4]
    constant := ![-1, -1, 0, 0, -3, 0, 0, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 1]
    strict := ![false, false, false, true, false, false, false, false] }
  origin := ![.triangle 19 0, .triangle 20 0, .gapLower 3 2, .triangle 1 1, .gapLower 1 0, .thetaLower 1, .thetaUpper 4, .corridorUpper 3 4]

-- Cycle fingerprint 09865c5377f198719fb70de14c2f2dd752bb172df83453490a21bd390f991d89.
def localCycle00010 : Cycle where
  length := 8
  data := {
    node := ![.distance 2 3, .distance 3 5, .theta 3, .theta 2, .theta 1, .distance 1 2, .distance 0 2, .distance 2 4, .distance 2 3]
    constant := ![-1, -1, 0, 0, 2, 0, -1, 0]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![false, false, true, true, false, true, false, true] }
  origin := ![.triangle 26 0, .corridorLower 3 5, .thetaNext 2, .thetaNext 1, .gapLower 1 6, .triangle 0 2, .triangle 6 0, .triangle 25 1]

-- Cycle fingerprint 0c34127664b378343e88e92821c64e47c1cb6f53a628698a6620ad82ab924b13.
def localCycle00011 : Cycle where
  length := 11
  data := {
    node := ![.distance 1 5, .distance 0 5, .distance 4 5, .distance 2 4, .distance 2 3, .theta 2, .theta 1, .distance 1 2, .distance 1 4, .distance 1 3, .distance 1 6, .distance 1 5]
    constant := ![0, 0, -1, 0, -1, 0, 2, 0, 0, 0, -2]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0]
    strict := ![true, true, false, false, false, true, false, true, true, true, false] }
  origin := ![.triangle 3 2, .triangle 12 1, .triangle 28 0, .gapLower 2 1, .corridorLower 2 3, .thetaNext 1, .gapLower 1 6, .triangle 16 2, .triangle 19 1, .triangle 21 2, .gapLower 1 2]

-- Cycle fingerprint 0c48d46f7631445603b3adafe5d9dc4be1b554d36ab13fd77becdc1bd25d242b.
def localCycle00012 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 1 3, .distance 1 6, .distance 1 5, .distance 0 1, .theta 0, .zero, .theta 4]
    constant := ![3, -1, 0, 0, -3, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 1]
    strict := ![false, false, true, true, false, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 19 0, .triangle 21 2, .triangle 24 1, .gapLower 1 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 4]

-- Cycle fingerprint 12d4e056473b37f3bf0a10ec2fba7fdb71379d667303e3429a79afbbe461499a.
def localCycle00013 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 3 4, .distance 1 3, .distance 3 5, .distance 4 5, .distance 0 4, .distance 4 6, .theta 4]
    constant := ![3, -1, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 19 0, .triangle 20 0, .triangle 31 1, .triangle 12 0, .triangle 13 0, .corridorLower 4 6]

-- Cycle fingerprint 12f734ee9d5e7116db64ce37da6b8b20395ef36f03376a85cd37a3594aafb22e.
def localCycle00014 : Cycle where
  length := 8
  data := {
    node := ![.distance 3 6, .distance 3 5, .distance 2 3, .theta 2, .theta 1, .distance 1 2, .distance 1 4, .distance 1 3, .distance 3 6]
    constant := ![0, -1, -1, 0, 2, 0, 0, -1]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![true, false, false, true, false, true, true, false] }
  origin := ![.triangle 33 1, .triangle 26 0, .corridorLower 2 3, .thetaNext 1, .gapLower 1 6, .triangle 16 2, .triangle 19 1, .triangle 21 0]

-- Cycle fingerprint 146e83e14e51ecf1d95d4638f7202bdf8e8d6cc16e76928359a2d522450967b4.
def localCycle00015 : Cycle where
  length := 9
  data := {
    node := ![.distance 3 4, .distance 1 3, .distance 1 6, .distance 1 5, .distance 0 5, .distance 3 5, .distance 2 5, .distance 4 5, .theta 4, .distance 3 4]
    constant := ![-1, -2, -2, 0, 0, 0, 0, -1, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![false, false, false, true, true, true, true, false, false] }
  origin := ![.triangle 19 0, .gapLower 1 3, .gapLower 1 2, .triangle 3 2, .triangle 10 1, .triangle 26 2, .triangle 28 1, .corridorLower 4 5, .corridorUpper 3 4]

-- Cycle fingerprint 14eaf637e0a341ba63d80b9d6a57ad309ae4abb5adab7f5e7f319d7f5aa507a4.
def localCycle00016 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 1 3, .distance 1 5, .distance 5 6, .distance 4 6, .distance 2 4, .distance 4 5, .theta 4]
    constant := ![3, -1, 0, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 19 0, .triangle 20 2, .triangle 24 0, .triangle 34 2, .triangle 29 0, .triangle 28 0, .corridorLower 4 5]

-- Cycle fingerprint 153a9be738313e2dc480af5266c3cfe73525a020495bd5ea3555834e2796011a.
def localCycle00017 : Cycle where
  length := 8
  data := {
    node := ![.distance 4 6, .distance 2 4, .theta 4, .distance 3 4, .distance 1 3, .distance 1 6, .distance 0 6, .distance 3 6, .distance 4 6]
    constant := ![-1, 0, 3, -1, -2, 0, 0, 0]
    coefficient := ![0, 0, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, true] }
  origin := ![.triangle 29 0, .gapLower 4 0, .corridorUpper 3 4, .triangle 19 0, .gapLower 1 3, .triangle 4 2, .triangle 11 1, .triangle 32 1]

-- Cycle fingerprint 17c1c3808e8f8f73a39f00a415a36244c5d16376d796384d637f5c6d22d29bc6.
def localCycle00018 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 2, .distance 1 4, .distance 1 3, .distance 1 5, .distance 3 5, .distance 2 3, .theta 2, .distance 1 2]
    constant := ![-2, 0, -2, 0, -1, -1, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, false, true, false, false, false] }
  origin := ![.gapLower 1 5, .triangle 19 1, .gapLower 1 2, .triangle 20 1, .triangle 26 0, .corridorLower 2 3, .corridorUpper 1 2]

-- Cycle fingerprint 19a3b4dbb5c7e56ba8a8efa31079b35f0204ce0c0b0434513d009eaa29f1b767.
def localCycle00019 : Cycle where
  length := 10
  data := {
    node := ![.theta 4, .distance 3 4, .distance 1 3, .distance 1 5, .distance 5 6, .distance 3 6, .distance 0 3, .distance 3 5, .distance 4 5, .distance 2 4, .theta 4]
    constant := ![3, -1, 0, -1, 0, -1, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false, true, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 19 0, .triangle 20 2, .triangle 24 0, .triangle 33 2, .triangle 11 0, .triangle 10 0, .triangle 31 1, .triangle 28 0, .gapLower 4 0]

-- Cycle fingerprint 1d9880b55e7217ce69060aaa36de45835d3a339e2b9da4accc98434745261318.
def localCycle00020 : Cycle where
  length := 8
  data := {
    node := ![.distance 4 5, .distance 2 4, .theta 4, .distance 3 4, .distance 1 3, .distance 1 6, .distance 1 5, .distance 3 5, .distance 4 5]
    constant := ![-1, 0, 3, -1, -2, -2, 0, 0]
    coefficient := ![0, 0, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, true] }
  origin := ![.triangle 28 0, .gapLower 4 0, .corridorUpper 3 4, .triangle 19 0, .gapLower 1 3, .gapLower 1 2, .triangle 20 1, .triangle 31 1]

-- Cycle fingerprint 1ed5807bef37444878d3605ad365cd9d5862a903b316534967329ebd2a168094.
def localCycle00021 : Cycle where
  length := 11
  data := {
    node := ![.distance 2 3, .distance 3 5, .distance 4 5, .theta 4, .theta 3, .theta 2, .distance 1 2, .distance 1 4, .distance 1 6, .distance 1 3, .distance 0 3, .distance 2 3]
    constant := ![-1, 0, -1, 0, 0, 3, -2, 0, -2, 0, 0]
    coefficient := ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, true, false, false, true, false, true, true] }
  origin := ![.triangle 26 0, .triangle 31 1, .corridorLower 4 5, .thetaNext 3, .thetaNext 2, .corridorUpper 1 2, .gapLower 1 5, .triangle 23 2, .gapLower 1 3, .triangle 1 2, .triangle 5 1]

-- Cycle fingerprint 1ff01974c4f031e6a8dbf8a883a8c983a67c1c851630e4f42acbb17957111887.
def localCycle00022 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 1 3, .distance 3 6, .distance 0 3, .distance 3 5, .distance 4 5, .distance 2 4, .theta 4]
    constant := ![3, -1, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 19 0, .triangle 21 0, .triangle 11 0, .triangle 10 0, .triangle 31 1, .triangle 28 0, .gapLower 4 0]

-- Cycle fingerprint 200466584042961bdc96256c5a795b88232bbb9626a3b051753303c608b2c5f7.
def localCycle00023 : Cycle where
  length := 8
  data := {
    node := ![.distance 1 5, .distance 3 5, .distance 2 3, .theta 2, .distance 1 2, .distance 1 4, .distance 1 3, .distance 1 6, .distance 1 5]
    constant := ![0, -1, -1, 3, -2, 0, 0, -2]
    coefficient := ![0, 0, 0, 1, 0, 0, 0, 0]
    strict := ![true, false, false, false, false, true, true, false] }
  origin := ![.triangle 20 1, .triangle 26 0, .corridorLower 2 3, .corridorUpper 1 2, .gapLower 1 5, .triangle 19 1, .triangle 21 2, .gapLower 1 2]

-- Cycle fingerprint 212587624ec8f7194af615ab0ce3800b22de4084460822c89ec87324f87b6000.
def localCycle00024 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .theta 1, .distance 1 2, .distance 0 2, .distance 0 4, .distance 0 3, .distance 3 6, .distance 3 5, .distance 2 3, .theta 2]
    constant := ![0, 1, 0, 0, 0, -1, 0, -1, -1]
    coefficient := ![0, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![true, false, true, true, true, false, true, false, false] }
  origin := ![.thetaNext 1, .gapLower 1 6, .triangle 0 2, .triangle 6 2, .triangle 9 1, .triangle 11 0, .triangle 33 1, .triangle 26 0, .corridorLower 2 3]

-- Cycle fingerprint 25819cc81c689c406f8bfbac533a7fa9d5b09f227d2fe8d650c0934cd41c1584.
def localCycle00025 : Cycle where
  length := 7
  data := {
    node := ![.theta 1, .distance 1 2, .distance 1 4, .distance 1 3, .distance 3 5, .distance 2 3, .theta 2, .theta 1]
    constant := ![1, 0, 0, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, false, true] }
  origin := ![.gapLower 1 6, .triangle 16 2, .triangle 19 1, .triangle 20 0, .triangle 26 0, .corridorLower 2 3, .thetaNext 1]

-- Cycle fingerprint 2637b597d26cd8484a92bce0815303e89865aa4c07e95be1caa9f4e9f77dd7c5.
def localCycle00026 : Cycle where
  length := 8
  data := {
    node := ![.distance 3 6, .distance 2 3, .theta 2, .distance 1 2, .distance 1 4, .distance 1 3, .distance 1 6, .distance 0 6, .distance 3 6]
    constant := ![-1, -1, 3, 0, -2, -2, 0, 0]
    coefficient := ![0, 0, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, true, true] }
  origin := ![.triangle 27 0, .corridorLower 2 3, .corridorUpper 1 2, .triangle 16 2, .gapLower 1 4, .gapLower 1 3, .triangle 4 2, .triangle 11 1]

-- Cycle fingerprint 266c6df5a4333c960fdf28094991de8b27a1ce4ff7a87216b74c4e1187982488.
def localCycle00027 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 3 4, .distance 0 3, .distance 3 5, .distance 2 5, .distance 5 6, .theta 5, .theta 4]
    constant := ![3, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, true] }
  origin := ![.corridorUpper 3 4, .triangle 9 0, .triangle 10 0, .triangle 26 2, .triangle 30 0, .corridorLower 5 6, .thetaNext 4]

-- Cycle fingerprint 27f8069d7a42e4ed26ed0f491ad495b8608e02fa73770e4caced313ef7480524.
def localCycle00028 : Cycle where
  length := 8
  data := {
    node := ![.distance 1 6, .distance 3 6, .distance 2 3, .theta 2, .theta 1, .distance 1 2, .distance 1 4, .distance 1 3, .distance 1 6]
    constant := ![0, -1, -1, 0, 2, 0, 0, -2]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![true, false, false, true, false, true, true, false] }
  origin := ![.triangle 21 1, .triangle 27 0, .corridorLower 2 3, .thetaNext 1, .gapLower 1 6, .triangle 16 2, .triangle 19 1, .gapLower 1 3]

-- Cycle fingerprint 2929bbfe7bac180e28acaa01529224c23e8703666b0dd5e5dcb0a6307cd07fd5.
def localCycle00029 : Cycle where
  length := 8
  data := {
    node := ![.distance 3 6, .distance 3 5, .distance 2 3, .theta 2, .distance 1 2, .distance 1 4, .distance 0 4, .distance 0 3, .distance 3 6]
    constant := ![0, -1, -1, 3, -3, 0, 0, -1]
    coefficient := ![0, 0, 0, 1, 0, 0, 0, 0]
    strict := ![true, false, false, false, false, true, true, false] }
  origin := ![.triangle 33 1, .triangle 26 0, .corridorLower 2 3, .corridorUpper 1 2, .gapLower 1 5, .triangle 2 2, .triangle 9 1, .triangle 11 0]

-- Cycle fingerprint 294cee515acbe9a47a6edc3698ea6f0aa4057fbf74426b5cfd3850e7defbfc1b.
def localCycle00030 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 6, .distance 1 3, .distance 3 5, .distance 2 3, .theta 2, .distance 1 2, .distance 1 4, .distance 1 6]
    constant := ![-2, -1, -1, -1, 3, 0, 0]
    coefficient := ![0, 0, 0, 0, 1, 0, 0]
    strict := ![false, false, false, false, false, true, true] }
  origin := ![.gapLower 1 3, .triangle 20 0, .triangle 26 0, .corridorLower 2 3, .corridorUpper 1 2, .triangle 16 2, .triangle 23 2]

-- Cycle fingerprint 297cbeba7107d70e4540b861631efe2a1bfe84933099159d09c2b6d1aae1eb5c.
def localCycle00031 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 2, .distance 1 4, .distance 1 3, .distance 3 6, .distance 3 5, .distance 2 3, .theta 2, .distance 1 2]
    constant := ![-2, 0, -1, 0, -1, -1, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, false, true, false, false, false] }
  origin := ![.gapLower 1 5, .triangle 19 1, .triangle 21 0, .triangle 33 1, .triangle 26 0, .corridorLower 2 3, .corridorUpper 1 2]

-- Cycle fingerprint 2af71584599cd2c1e4b83ae593a98fde5023d76521d423b9691ffa541464f7f1.
def localCycle00032 : Cycle where
  length := 6
  data := {
    node := ![.theta 4, .distance 3 4, .distance 1 3, .distance 1 5, .distance 5 6, .distance 4 5, .theta 4]
    constant := ![3, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 19 0, .triangle 20 2, .triangle 24 0, .triangle 34 0, .corridorLower 4 5]

-- Cycle fingerprint 2dea5766304173180c8c051b395aa46018ccb34715a9c99841c5458370460f3a.
def localCycle00033 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 4 6, .distance 1 4, .distance 0 4, .distance 0 3, .distance 3 5, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, -1, -1, 0, 0, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, false, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 32 0, .triangle 23 0, .triangle 2 2, .triangle 9 1, .triangle 10 0, .triangle 26 0, .corridorLower 2 3, .thetaLower 2]

-- Cycle fingerprint 2e5e0b1f472fe3e928c3d454d15014161b66d185197d753522f04da1cf7013e4.
def localCycle00034 : Cycle where
  length := 8
  data := {
    node := ![.theta 0, .zero, .theta 4, .distance 3 4, .distance 1 3, .distance 1 6, .distance 1 5, .distance 0 1, .theta 0]
    constant := ![0, 0, 3, -1, -2, 0, -2, -1]
    coefficient := ![0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, false] }
  origin := ![.thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 19 0, .gapLower 1 3, .triangle 24 1, .gapLower 1 1, .corridorLower 0 1]

-- Cycle fingerprint 2f9972cb9dd645b8d018bbe917217a2c77424165b5c366b49fc3e5d9be3609cb.
def localCycle00035 : Cycle where
  length := 8
  data := {
    node := ![.theta 1, .zero, .theta 2, .distance 1 2, .distance 1 4, .distance 1 6, .distance 1 3, .distance 0 1, .theta 1]
    constant := ![0, 0, 3, 0, -2, 0, -1, -2]
    coefficient := ![0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true, false, false] }
  origin := ![.thetaLower 1, .thetaUpper 2, .corridorUpper 1 2, .triangle 16 2, .gapLower 1 4, .triangle 21 1, .triangle 1 0, .gapLower 1 0]

-- Cycle fingerprint 2fb2fd1a7823a1a31ea79d941af5a5c4f133d776e33999c5e67c0528f91eb18e.
def localCycle00036 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 6, .theta 6, .theta 5, .theta 4, .distance 3 4, .distance 4 5, .distance 1 4, .distance 1 6]
    constant := ![-2, 0, 0, 3, -1, -1, 0]
    coefficient := ![-1, 0, 0, 1, 0, 0, 0]
    strict := ![true, true, true, false, false, false, true] }
  origin := ![.gapUpper 6 6, .thetaNext 5, .thetaNext 4, .corridorUpper 3 4, .triangle 31 0, .triangle 22 0, .triangle 23 2]

-- Cycle fingerprint 2fe9ef377b40c3861bbc85ac8336a267f9f823c95b0daca4997a720c75fc14f1.
def localCycle00037 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 3 4, .distance 0 3, .distance 3 6, .distance 4 6, .distance 2 4, .distance 4 5, .theta 4]
    constant := ![3, -1, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 9 0, .triangle 11 0, .triangle 32 1, .triangle 29 0, .triangle 28 0, .corridorLower 4 5]

-- Cycle fingerprint 301a095724cb3e47d6331eba71e91effe748847a4c93461df636303129097dd9.
def localCycle00038 : Cycle where
  length := 5
  data := {
    node := ![.theta 5, .distance 3 5, .distance 1 3, .distance 1 6, .theta 6, .theta 5]
    constant := ![3, -1, 0, -2, 0]
    coefficient := ![1, 0, 0, -1, 0]
    strict := ![false, false, true, true, true] }
  origin := ![.corridorUpper 3 5, .triangle 20 0, .triangle 21 2, .gapUpper 6 6, .thetaNext 5]

-- Cycle fingerprint 3145bac4a4da9f06c39c281872cf2ec95aa8896bc9cf97b68579d0f05e39cd62.
def localCycle00039 : Cycle where
  length := 6
  data := {
    node := ![.theta 4, .distance 3 4, .distance 0 3, .distance 0 5, .distance 5 6, .distance 4 5, .theta 4]
    constant := ![3, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 9 0, .triangle 10 2, .triangle 14 0, .triangle 34 0, .corridorLower 4 5]

-- Cycle fingerprint 31c2206412be8aafa78cbeead9f69e0a25752ac8f89e8fe08edf9d5aa5eaecd2.
def localCycle00040 : Cycle where
  length := 6
  data := {
    node := ![.theta 4, .distance 3 4, .distance 1 3, .distance 3 5, .distance 5 6, .distance 4 5, .theta 4]
    constant := ![3, -1, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 19 0, .triangle 20 0, .triangle 33 0, .triangle 34 0, .corridorLower 4 5]

-- Cycle fingerprint 348dc1c64e936cb256ef356e2e80a6a8f0c8dff26502e458a2ff28b859a8d3ac.
def localCycle00041 : Cycle where
  length := 6
  data := {
    node := ![.distance 1 3, .distance 3 5, .distance 2 3, .theta 2, .distance 1 2, .distance 1 4, .distance 1 3]
    constant := ![-1, -1, 0, 3, -2, 0]
    coefficient := ![0, 0, 0, 1, 0, 0]
    strict := ![false, false, false, false, false, true] }
  origin := ![.triangle 20 0, .triangle 26 0, .gapLower 2 0, .corridorUpper 1 2, .gapLower 1 5, .triangle 19 1]

-- Cycle fingerprint 34df15cfc0f1d7cf48ee787930ed3fbc5af1e735a491157edc2b3d4e6e1e7564.
def localCycle00042 : Cycle where
  length := 12
  data := {
    node := ![.distance 4 5, .theta 4, .theta 3, .theta 2, .theta 1, .distance 1 2, .distance 1 4, .distance 1 6, .distance 0 6, .distance 2 6, .distance 2 3, .distance 3 5, .distance 4 5]
    constant := ![-1, 0, 0, 0, 2, 0, -2, 0, 0, 0, -1, 0]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, true, false, true, true, true, false, true] }
  origin := ![.corridorLower 4 5, .thetaNext 3, .thetaNext 2, .thetaNext 1, .gapLower 1 6, .triangle 16 2, .gapLower 1 4, .triangle 4 2, .triangle 8 1, .triangle 27 1, .triangle 26 0, .triangle 31 1]

-- Cycle fingerprint 38c5bf27887b6677cf4539893d6dcc03c5d1d3e4dc03b84ab90a4e5075247f70.
def localCycle00043 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 3 4, .distance 1 3, .distance 3 5, .distance 4 5, .distance 2 4, .distance 4 6, .theta 4]
    constant := ![3, -1, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 19 0, .triangle 20 0, .triangle 31 1, .triangle 28 0, .triangle 29 0, .corridorLower 4 6]

-- Cycle fingerprint 3938f3a2c5f8683222e8f72064032b05ebea7511bba6545a11e6166d49bcaaaa.
def localCycle00044 : Cycle where
  length := 5
  data := {
    node := ![.distance 1 5, .distance 5 6, .distance 3 6, .distance 1 6, .distance 1 3, .distance 1 5]
    constant := ![2, 0, 0, -2, -2]
    coefficient := ![0, 0, 0, 0, 0]
    strict := ![true, false, true, false, false] }
  origin := ![.gapUpper 5 5, .gapLower 6 5, .triangle 21 2, .gapLower 1 3, .gapLower 1 2]

-- Cycle fingerprint 3d7b2fa2f25ec25608ae92480fcefc4e24835d29b2b972fd4239ea6a7519c872.
def localCycle00045 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 3, .distance 3 5, .distance 2 3, .theta 2, .theta 1, .distance 1 2, .distance 0 2, .distance 0 4, .distance 0 3]
    constant := ![-1, -1, -1, 0, 2, 0, 0, 0]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, true, false, true, true, true] }
  origin := ![.triangle 10 0, .triangle 26 0, .corridorLower 2 3, .thetaNext 1, .gapLower 1 6, .triangle 0 2, .triangle 6 2, .triangle 9 1]

-- Cycle fingerprint 40021d45dec0aa8397663f90d50480528ddbfa508bda9cab49e8ce33cd0ed977.
def localCycle00046 : Cycle where
  length := 12
  data := {
    node := ![.distance 4 5, .theta 4, .theta 3, .theta 2, .theta 1, .distance 1 2, .distance 1 4, .distance 1 6, .distance 1 3, .distance 0 3, .distance 2 3, .distance 3 5, .distance 4 5]
    constant := ![-1, 0, 0, 0, 2, 0, 0, -2, 0, 0, -1, 0]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, true, true, false, true, true, false, true] }
  origin := ![.corridorLower 4 5, .thetaNext 3, .thetaNext 2, .thetaNext 1, .gapLower 1 6, .triangle 16 2, .triangle 23 2, .gapLower 1 3, .triangle 1 2, .triangle 5 1, .triangle 26 0, .triangle 31 1]

-- Cycle fingerprint 4229a1f996d6bdd3bb0aac43090dd88808ce5f23bc4ad2081f0139b4d6f06522.
def localCycle00047 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 3 4, .distance 0 3, .distance 3 6, .distance 2 3, .distance 3 5, .distance 4 5, .theta 4]
    constant := ![3, -1, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 9 0, .triangle 11 0, .triangle 27 0, .triangle 26 0, .triangle 31 1, .corridorLower 4 5]

-- Cycle fingerprint 4279cb9192a095a75946ef7ff8a247af8d538a78ec922dd4ebfb260011806430.
def localCycle00048 : Cycle where
  length := 8
  data := {
    node := ![.distance 3 5, .distance 2 3, .theta 2, .distance 1 2, .distance 1 4, .distance 1 3, .distance 0 3, .distance 3 6, .distance 3 5]
    constant := ![-1, -1, 3, 0, -2, 0, -1, 0]
    coefficient := ![0, 0, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true, false, true] }
  origin := ![.triangle 26 0, .corridorLower 2 3, .corridorUpper 1 2, .triangle 16 2, .gapLower 1 4, .triangle 1 2, .triangle 11 0, .triangle 33 1]

-- Cycle fingerprint 43888e828a20874a6e2791402ec43f1eb3ab60633adbab07a5c921898d0e4eff.
def localCycle00049 : Cycle where
  length := 8
  data := {
    node := ![.distance 3 5, .distance 2 3, .theta 2, .distance 1 2, .distance 1 4, .distance 1 6, .distance 1 3, .distance 0 3, .distance 3 5]
    constant := ![-1, -1, 3, 0, -2, -2, 0, -1]
    coefficient := ![0, 0, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, true, false] }
  origin := ![.triangle 26 0, .corridorLower 2 3, .corridorUpper 1 2, .triangle 16 2, .gapLower 1 4, .gapLower 1 3, .triangle 1 2, .triangle 10 0]

-- Cycle fingerprint 44375e4f4f104d8e6069ee562b8660ddfa30a1cdddbe8d00289e5987f7e5f5c8.
def localCycle00050 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 3 4, .distance 0 3, .distance 3 5, .distance 2 5, .distance 5 6, .distance 4 5, .theta 4]
    constant := ![3, -1, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 9 0, .triangle 10 0, .triangle 26 2, .triangle 30 0, .triangle 34 0, .corridorLower 4 5]

-- Cycle fingerprint 4539eaf93e98229e3ef26b33ac0bc629e976c2f8772359a6d4ec4f03fd69934f.
def localCycle00051 : Cycle where
  length := 8
  data := {
    node := ![.distance 2 3, .theta 2, .distance 1 2, .distance 1 4, .distance 1 6, .distance 1 3, .distance 0 3, .distance 3 5, .distance 2 3]
    constant := ![-1, 3, 0, 0, -2, 0, -1, -1]
    coefficient := ![0, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, true, false, false] }
  origin := ![.corridorLower 2 3, .corridorUpper 1 2, .triangle 16 2, .triangle 23 2, .gapLower 1 3, .triangle 1 2, .triangle 10 0, .triangle 26 0]

-- Cycle fingerprint 459f336ef917660098e7e314e47969bc583fe9eef008a2b8d280baa8c6613b54.
def localCycle00052 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 5, .distance 0 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 1 3, .distance 1 5]
    constant := ![-3, -1, 0, 0, 3, -1, 0]
    coefficient := ![0, 0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, false, false, false, true] }
  origin := ![.gapLower 1 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 19 0, .triangle 20 2]

-- Cycle fingerprint 45f3d493fab275677b2e82d860b588b2bb138fdb5b6c567df161056fc1316d27.
def localCycle00053 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 4, .distance 1 3, .distance 1 6, .distance 1 5, .distance 0 5, .distance 3 5, .distance 2 3, .theta 2]
    constant := ![3, -2, 0, 0, -2, 0, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, true, true, false, false] }
  origin := ![.corridorUpper 1 2, .gapLower 1 5, .triangle 19 1, .triangle 21 2, .gapLower 1 2, .triangle 3 2, .triangle 10 1, .triangle 26 0, .corridorLower 2 3]

-- Cycle fingerprint 4a61c52d9b644304f2d00784d4c75079e7ca2732b683f16bf5eea4d08d8dae87.
def localCycle00054 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 4 6, .distance 1 4, .distance 1 3, .distance 3 5, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, -1, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 32 0, .triangle 23 0, .triangle 19 1, .triangle 20 0, .triangle 26 0, .corridorLower 2 3, .thetaLower 2]

-- Cycle fingerprint 4e15553d791b78dcfde12ecbd58057e1319c417945ca4c8007bc5ec438f3a641.
def localCycle00055 : Cycle where
  length := 3
  data := {
    node := ![.distance 3 6, .distance 1 3, .distance 1 6, .distance 3 6]
    constant := ![2, -3, 0]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.gapUpper 3 4, .gapLower 1 3, .triangle 21 1]

-- Cycle fingerprint 51b14c48b48dbb846984c5a31ed77dbad6e80a6fad99d7bc728785777f61b82d.
def localCycle00056 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 3 4, .distance 0 3, .distance 3 5, .distance 2 3, .distance 3 6, .distance 4 6, .theta 4]
    constant := ![3, -1, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 9 0, .triangle 10 0, .triangle 26 0, .triangle 27 0, .triangle 32 1, .corridorLower 4 6]

-- Cycle fingerprint 53b5adc57da5eb3d2122dcb7545064aa2335427b7a31139b6ba70c32d8f5e676.
def localCycle00057 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 1 3, .distance 3 5, .distance 4 5, .distance 5 6, .distance 2 5, .distance 2 4, .theta 4]
    constant := ![3, -1, -1, 0, -1, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 19 0, .triangle 20 0, .triangle 31 1, .triangle 34 0, .triangle 30 0, .gapLower 2 2, .gapLower 4 0]

-- Cycle fingerprint 55934910b99eea73eaeefd5b2ed65129696baa6ff551b09723a6da224e3a9129.
def localCycle00058 : Cycle where
  length := 3
  data := {
    node := ![.theta 2, .theta 1, .distance 1 2, .theta 2]
    constant := ![0, 1, -2]
    coefficient := ![0, 1, -1]
    strict := ![true, false, true] }
  origin := ![.thetaNext 1, .gapLower 1 6, .gapUpper 2 6]

-- Cycle fingerprint 5711364f0cf51eb6a352b98b42addcae67aae3eb4908c90dfcd5a6476614152d.
def localCycle00059 : Cycle where
  length := 11
  data := {
    node := ![.distance 2 4, .distance 2 3, .theta 2, .zero, .theta 4, .distance 3 4, .distance 4 6, .distance 0 4, .distance 0 3, .distance 3 5, .distance 4 5, .distance 2 4]
    constant := ![0, -1, 0, 0, 3, -1, -1, 0, -1, 0, -1]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![true, false, false, false, false, false, false, false, false, true, false] }
  origin := ![.triangle 25 1, .corridorLower 2 3, .thetaLower 2, .thetaUpper 4, .corridorUpper 3 4, .triangle 32 0, .triangle 13 0, .gapLower 0 3, .triangle 10 0, .triangle 31 1, .triangle 28 0]

-- Cycle fingerprint 5800878a300e76336860d606043be84a2c4893c582fb01454be960788a557337.
def localCycle00060 : Cycle where
  length := 12
  data := {
    node := ![.theta 1, .zero, .theta 2, .distance 1 2, .distance 1 4, .distance 1 6, .distance 1 3, .distance 3 5, .distance 4 5, .distance 0 4, .distance 0 3, .distance 0 1, .theta 1]
    constant := ![0, 0, 3, 0, -2, 0, -1, 0, -1, 0, 0, -2]
    coefficient := ![0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true, false, true, false, false, true, false] }
  origin := ![.thetaLower 1, .thetaUpper 2, .corridorUpper 1 2, .triangle 16 2, .gapLower 1 4, .triangle 21 1, .triangle 20 0, .triangle 31 1, .triangle 12 0, .gapLower 0 2, .triangle 1 1, .gapLower 1 0]

-- Cycle fingerprint 59a87d343d92694e6652c58f9890d2b4105a54bc9e0eeded036b9408233061f2.
def localCycle00061 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 2, .distance 1 4, .distance 1 3, .distance 1 6, .distance 0 6, .distance 4 6, .distance 2 4, .distance 2 3, .theta 2, .distance 1 2]
    constant := ![0, -2, -2, 0, 0, -1, 0, -1, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![true, false, false, true, true, false, false, false, false] }
  origin := ![.triangle 16 2, .gapLower 1 4, .gapLower 1 3, .triangle 4 2, .triangle 13 1, .triangle 29 0, .gapLower 2 1, .corridorLower 2 3, .corridorUpper 1 2]

-- Cycle fingerprint 5a36f4fb7b9291b42c093e35545d60e5c9430173988a9d63af88958c79ae4a47.
def localCycle00062 : Cycle where
  length := 11
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 4, .distance 4 6, .distance 2 4, .distance 4 5, .theta 4, .distance 3 4, .distance 1 3, .distance 3 5, .distance 2 3, .theta 2]
    constant := ![3, 0, -1, -1, -1, -1, 3, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false, false, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 16 2, .triangle 23 0, .triangle 29 0, .triangle 28 0, .corridorLower 4 5, .corridorUpper 3 4, .triangle 19 0, .triangle 20 0, .triangle 26 0, .corridorLower 2 3]

-- Cycle fingerprint 5b854807b5ec35d42dfe7fe82e82cdb03fd07b35dc6b8f9179ce902322ac1467.
def localCycle00063 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .theta 1, .distance 1 2, .distance 1 4, .distance 1 6, .distance 0 6, .distance 0 3, .distance 3 5, .distance 2 3, .theta 2]
    constant := ![0, 2, 0, -2, 0, 0, -1, -1, -1]
    coefficient := ![0, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![true, false, true, false, true, true, false, false, false] }
  origin := ![.thetaNext 1, .gapLower 1 6, .triangle 16 2, .gapLower 1 4, .triangle 4 2, .triangle 11 1, .triangle 10 0, .triangle 26 0, .corridorLower 2 3]

-- Cycle fingerprint 5e29f29680339a5164dc989c89d8022feaa528ba15801bee92dcc6b4bd323934.
def localCycle00064 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 1 4, .distance 4 5, .distance 2 4, .distance 4 6, .distance 5 6, .theta 5, .theta 4]
    constant := ![3, 0, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, true, false, true] }
  origin := ![.corridorUpper 3 4, .triangle 19 2, .triangle 22 0, .triangle 28 0, .triangle 29 0, .triangle 34 1, .corridorLower 5 6, .thetaNext 4]

-- Cycle fingerprint 5e9eeed7049bf0b7421585e30291886acd00c537f3ef53e84e76578468f19bc0.
def localCycle00065 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 1 3, .distance 0 3, .distance 3 6, .distance 2 3, .distance 3 5, .distance 4 5, .theta 4]
    constant := ![3, -1, 0, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 19 0, .triangle 1 2, .triangle 11 0, .triangle 27 0, .triangle 26 0, .triangle 31 1, .corridorLower 4 5]

-- Cycle fingerprint 5ecdb076cc5ac968f8dc1c64411aabecb72a681005fa136ccbb3856c1c2dc3ad.
def localCycle00066 : Cycle where
  length := 8
  data := {
    node := ![.theta 0, .zero, .theta 2, .distance 1 2, .distance 1 4, .distance 1 6, .distance 1 5, .distance 0 1, .theta 0]
    constant := ![0, 0, 3, 0, -2, 0, -2, -1]
    coefficient := ![0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true, false, false] }
  origin := ![.thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 16 2, .gapLower 1 4, .triangle 24 1, .gapLower 1 1, .corridorLower 0 1]

-- Cycle fingerprint 5f314ddc1a4749b294d482e4a7b36ce657e32046523454e2f023bbe536e93c96.
def localCycle00067 : Cycle where
  length := 11
  data := {
    node := ![.distance 3 5, .distance 4 5, .theta 4, .theta 3, .theta 2, .distance 1 2, .distance 1 4, .distance 1 6, .distance 0 6, .distance 2 6, .distance 2 3, .distance 3 5]
    constant := ![0, -1, 0, 0, 3, 0, -3, 0, 0, 0, -1]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0]
    strict := ![true, false, true, true, false, true, false, true, true, true, false] }
  origin := ![.triangle 31 1, .corridorLower 4 5, .thetaNext 3, .thetaNext 2, .corridorUpper 1 2, .triangle 16 2, .gapLower 1 4, .triangle 4 2, .triangle 8 1, .triangle 27 1, .triangle 26 0]

-- Cycle fingerprint 5fe643747ad66ead08adda477ade93c7976aaadce7576cbeaeae5dfb389202c0.
def localCycle00068 : Cycle where
  length := 3
  data := {
    node := ![.distance 5 6, .distance 1 6, .distance 1 5, .distance 5 6]
    constant := ![0, -3, 2]
    coefficient := ![0, 0, 0]
    strict := ![false, false, true] }
  origin := ![.gapLower 6 5, .gapLower 1 2, .gapUpper 5 5]

-- Cycle fingerprint 606f80c6986522f11386f83a10c460605436274a27d8ac0f80485c921dc12df0.
def localCycle00069 : Cycle where
  length := 11
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 2, .distance 0 4, .distance 4 6, .distance 2 4, .distance 2 3, .distance 3 5, .distance 4 5, .theta 4, .theta 3, .theta 2]
    constant := ![3, 0, 0, -1, -1, 0, -1, 0, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, false, false, true, false, true, true] }
  origin := ![.corridorUpper 1 2, .triangle 0 2, .triangle 6 2, .triangle 13 0, .triangle 29 0, .gapLower 2 2, .triangle 26 0, .triangle 31 1, .corridorLower 4 5, .thetaNext 3, .thetaNext 2]

-- Cycle fingerprint 608c85bbf544360dbe495203b9fca58fee848914ebb2834b430c6975471a0daf.
def localCycle00070 : Cycle where
  length := 9
  data := {
    node := ![.distance 3 4, .distance 1 3, .distance 1 6, .distance 0 6, .distance 3 6, .distance 2 6, .distance 4 6, .distance 4 5, .theta 4, .distance 3 4]
    constant := ![-1, -3, 0, 0, 0, 0, 0, -1, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![false, false, true, true, true, true, true, false, false] }
  origin := ![.triangle 19 0, .gapLower 1 3, .triangle 4 2, .triangle 11 1, .triangle 27 2, .triangle 29 1, .triangle 34 1, .corridorLower 4 5, .corridorUpper 3 4]

-- Cycle fingerprint 61dcfcb9c2f2986b66a9d111a66c0f1fe297ebf0f3de64796242be9200f9dab2.
def localCycle00071 : Cycle where
  length := 4
  data := {
    node := ![.distance 5 6, .distance 3 6, .distance 1 3, .distance 1 5, .distance 5 6]
    constant := ![0, -1, -2, 2]
    coefficient := ![0, 0, 0, 0]
    strict := ![true, false, false, true] }
  origin := ![.triangle 33 2, .triangle 21 0, .gapLower 1 2, .gapUpper 5 5]

-- Cycle fingerprint 621b8614f3336e2e332b9f6b0d42777b3efb58a451f42c0ba9dda312ade7757e.
def localCycle00072 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 4, .distance 1 3, .distance 1 6, .distance 0 6, .distance 4 6, .distance 2 4, .distance 2 3, .theta 2]
    constant := ![3, -2, 0, -2, 0, 0, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, true, false, false, false] }
  origin := ![.corridorUpper 1 2, .gapLower 1 5, .triangle 19 1, .gapLower 1 3, .triangle 4 2, .triangle 13 1, .triangle 29 0, .gapLower 2 1, .corridorLower 2 3]

-- Cycle fingerprint 629c89657a5a430557e53e3d624c85571149347f037d89733a8ccfec3ff92dcb.
def localCycle00073 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 1 3, .distance 1 5, .distance 5 6, .distance 3 6, .distance 2 3, .distance 3 5, .distance 4 5, .theta 4]
    constant := ![3, -1, 0, -1, 0, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 19 0, .triangle 20 2, .triangle 24 0, .triangle 33 2, .triangle 27 0, .triangle 26 0, .triangle 31 1, .corridorLower 4 5]

-- Cycle fingerprint 63bfd8de33f3379d77cbb17525b750c145f7824c14afce6c81cc0d735bc1301a.
def localCycle00074 : Cycle where
  length := 8
  data := {
    node := ![.distance 3 6, .distance 3 5, .distance 2 3, .theta 2, .theta 1, .distance 1 2, .distance 1 4, .distance 1 3, .distance 3 6]
    constant := ![0, -1, -1, 0, 2, 0, -2, -1]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![true, false, false, true, false, true, false, false] }
  origin := ![.triangle 33 1, .triangle 26 0, .corridorLower 2 3, .thetaNext 1, .gapLower 1 6, .triangle 16 2, .gapLower 1 4, .triangle 21 0]

-- Cycle fingerprint 644ef80455c45f08ac425c63f1e9a44d5fff0361b5c1efbbac1382b7c92a4a64.
def localCycle00075 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 2, .distance 1 4, .distance 1 3, .distance 3 6, .distance 3 5, .distance 2 3, .theta 2, .distance 1 2]
    constant := ![-3, 0, -1, 0, -1, -1, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, false, true, false, false, false] }
  origin := ![.gapLower 1 5, .triangle 19 1, .triangle 21 0, .triangle 33 1, .triangle 26 0, .corridorLower 2 3, .corridorUpper 1 2]

-- Cycle fingerprint 64bd5d57567cdef23915eaaae806dcf07c28028324e5283522a08d066467114e.
def localCycle00076 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 1 3, .distance 1 6, .distance 1 5, .distance 0 1, .theta 1, .zero]
    constant := ![0, 3, -1, 0, -2, -1, -2, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 19 0, .triangle 21 2, .gapLower 1 2, .triangle 3 0, .gapLower 1 0, .thetaLower 1]

-- Cycle fingerprint 6505b47572efde2019b9928c74feb9bdebb6a177c7170c247d99de707f01fb79.
def localCycle00077 : Cycle where
  length := 9
  data := {
    node := ![.distance 3 4, .distance 1 3, .distance 1 6, .distance 1 5, .distance 0 5, .distance 3 5, .distance 4 5, .distance 2 4, .theta 4, .distance 3 4]
    constant := ![-1, -2, -2, 0, 0, 0, -1, 0, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![false, false, false, true, true, true, false, false, false] }
  origin := ![.triangle 19 0, .gapLower 1 3, .gapLower 1 2, .triangle 3 2, .triangle 10 1, .triangle 31 1, .triangle 28 0, .gapLower 4 0, .corridorUpper 3 4]

-- Cycle fingerprint 65de18ae97778e4aeeeefa70ee8ae18c43a4bbd6ff104cc2608c7cb7b18e939f.
def localCycle00078 : Cycle where
  length := 3
  data := {
    node := ![.distance 0 1, .theta 1, .distance 1 2, .distance 0 1]
    constant := ![-2, 2, -1]
    coefficient := ![0, 1, 0]
    strict := ![false, false, false] }
  origin := ![.gapLower 1 0, .gapLower 1 6, .triangle 0 0]

-- Cycle fingerprint 67dc154b0030cc1ba36bb48612cb900aa6c89895f945c1edd38eaccd4e990dd2.
def localCycle00079 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 2, .distance 1 4, .distance 1 3, .distance 3 6, .distance 3 5, .distance 2 3, .theta 2, .distance 1 2]
    constant := ![-2, -2, -1, 0, -1, 0, 4]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![false, false, false, true, false, false, false] }
  origin := ![.gapLower 1 5, .gapLower 1 4, .triangle 21 0, .triangle 33 1, .triangle 26 0, .gapLower 2 0, .gapLower 2 6]

-- Cycle fingerprint 69842bc0977675beddbf7949981e1b9473fa4c515cea5503f6976c90f674e8cf.
def localCycle00080 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 0 3, .distance 3 5, .distance 4 5, .distance 5 6, .distance 2 5, .distance 2 4, .theta 4]
    constant := ![3, -1, -1, 0, -1, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 9 0, .triangle 10 0, .triangle 31 1, .triangle 34 0, .triangle 30 0, .gapLower 2 2, .gapLower 4 0]

-- Cycle fingerprint 6a663c36c5ded82e3deb491c8fffe572260607db100fa2ebc613a05c4b77d963.
def localCycle00081 : Cycle where
  length := 5
  data := {
    node := ![.distance 1 3, .distance 1 5, .distance 5 6, .distance 4 6, .distance 3 4, .distance 1 3]
    constant := ![0, 2, 0, -1, -1]
    coefficient := ![0, 0, 0, 0, 0]
    strict := ![true, true, true, false, false] }
  origin := ![.triangle 20 2, .gapUpper 5 5, .triangle 34 2, .triangle 32 0, .triangle 19 0]

-- Cycle fingerprint 6d690b29568898f143b537ae877158d020b5dd7fbc2d95c29f65efa87bb6dc2b.
def localCycle00082 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 2, .distance 1 4, .distance 1 6, .distance 1 3, .distance 3 5, .distance 2 3, .theta 2, .distance 1 2]
    constant := ![-2, -2, 0, -1, -1, -1, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![false, false, true, false, false, false, false] }
  origin := ![.gapLower 1 5, .gapLower 1 4, .triangle 21 1, .triangle 20 0, .triangle 26 0, .corridorLower 2 3, .corridorUpper 1 2]

-- Cycle fingerprint 6d83ccabe2fc2b444e831be17fa95ef31ce72a091c580abf41e0232afff12732.
def localCycle00083 : Cycle where
  length := 3
  data := {
    node := ![.distance 4 6, .distance 1 4, .distance 1 6, .distance 4 6]
    constant := ![2, -3, 0]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.gapUpper 4 4, .gapLower 1 4, .triangle 23 1]

-- Cycle fingerprint 6ed2008c4ea0d199e8236621d40e4e4e17e141bf5f258c8e6feed9df6dc3ac24.
def localCycle00084 : Cycle where
  length := 8
  data := {
    node := ![.distance 3 6, .distance 3 5, .distance 2 3, .theta 2, .distance 1 2, .distance 1 4, .distance 0 4, .distance 0 3, .distance 3 6]
    constant := ![0, -1, -1, 3, -2, 0, 0, -1]
    coefficient := ![0, 0, 0, 1, 0, 0, 0, 0]
    strict := ![true, false, false, false, false, true, true, false] }
  origin := ![.triangle 33 1, .triangle 26 0, .corridorLower 2 3, .corridorUpper 1 2, .gapLower 1 5, .triangle 2 2, .triangle 9 1, .triangle 11 0]

-- Cycle fingerprint 7299896991a8d60f06e2e584a75bb1c4a4a765e2f01c7cacb6d87fa102668d85.
def localCycle00085 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 3 4, .distance 1 4, .distance 0 4, .distance 4 6, .distance 2 4, .distance 4 5, .theta 4]
    constant := ![3, 0, 0, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 19 2, .triangle 2 2, .triangle 13 0, .triangle 29 0, .triangle 28 0, .corridorLower 4 5]

-- Cycle fingerprint 749da69e16b75100e696b68d313d628d1316f966ac86a0678517de32fa0969a5.
def localCycle00086 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 3 4, .distance 1 3, .distance 3 5, .distance 2 3, .distance 3 6, .distance 4 6, .theta 4]
    constant := ![3, -1, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 19 0, .triangle 20 0, .triangle 26 0, .triangle 27 0, .triangle 32 1, .corridorLower 4 6]

-- Cycle fingerprint 74a8bc8d290876050273cb7929f9c67eb25daa44e3c6e1c714d5f123839f9765.
def localCycle00087 : Cycle where
  length := 8
  data := {
    node := ![.distance 2 3, .distance 3 5, .theta 3, .theta 2, .distance 1 2, .distance 1 4, .distance 0 4, .distance 2 4, .distance 2 3]
    constant := ![-1, -1, 0, 3, -3, 0, 0, 0]
    coefficient := ![0, 0, 0, 1, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, true, true] }
  origin := ![.triangle 26 0, .corridorLower 3 5, .thetaNext 2, .corridorUpper 1 2, .gapLower 1 5, .triangle 2 2, .triangle 6 1, .triangle 25 1]

-- Cycle fingerprint 7ac154fb16880fe42776032844b4d887f8777e329709cd0e2646a3c50b884859.
def localCycle00088 : Cycle where
  length := 8
  data := {
    node := ![.distance 4 5, .distance 2 4, .theta 4, .distance 3 4, .distance 1 3, .distance 1 6, .distance 1 5, .distance 0 5, .distance 4 5]
    constant := ![-1, 0, 3, -1, -2, -2, 0, 0]
    coefficient := ![0, 0, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, true] }
  origin := ![.triangle 28 0, .gapLower 4 0, .corridorUpper 3 4, .triangle 19 0, .gapLower 1 3, .gapLower 1 2, .triangle 3 2, .triangle 12 1]

-- Cycle fingerprint 7d7e1d0dd5386a159baaf94400caa63ea3a1e0ff348a02de9a6c21d6a2999beb.
def localCycle00089 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 2, .distance 2 4, .distance 4 5, .distance 5 6, .theta 5, .theta 4, .theta 3, .theta 2]
    constant := ![3, 0, -1, -1, -1, -1, 0, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, true, true, true] }
  origin := ![.corridorUpper 1 2, .triangle 0 2, .triangle 6 0, .triangle 28 0, .triangle 34 0, .corridorLower 5 6, .thetaNext 4, .thetaNext 3, .thetaNext 2]

-- Cycle fingerprint 7ec0e5d3990881c654b885f7b154c822df277b6174dd2113306d6265c8740271.
def localCycle00090 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 3, .distance 3 5, .distance 0 3, .distance 0 1, .theta 1, .zero, .theta 2, .distance 1 2, .distance 1 4, .distance 1 6, .distance 1 3]
    constant := ![-1, -1, 0, -2, 0, 0, 3, 0, -2, 0]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, true, false, true] }
  origin := ![.triangle 20 0, .triangle 10 0, .triangle 1 1, .gapLower 1 0, .thetaLower 1, .thetaUpper 2, .corridorUpper 1 2, .triangle 16 2, .gapLower 1 4, .triangle 21 1]

-- Cycle fingerprint 7f28bd0bfffee3d611804742072dc4fea62d7a7c28118b5c911f62c1aba4acb1.
def localCycle00091 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 3, .distance 1 6, .distance 1 5, .distance 0 5, .distance 4 5, .distance 2 4, .distance 2 3, .theta 2, .distance 1 2, .distance 1 4, .distance 1 3]
    constant := ![0, -2, 0, 0, -1, 0, -1, 3, -2, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0]
    strict := ![true, false, true, true, false, false, false, false, false, true] }
  origin := ![.triangle 21 2, .gapLower 1 2, .triangle 3 2, .triangle 12 1, .triangle 28 0, .gapLower 2 1, .corridorLower 2 3, .corridorUpper 1 2, .gapLower 1 5, .triangle 19 1]

-- Cycle fingerprint 7f428fb3816f5b9be4fb67083b0a88de75d8f143a9e935ce6d35312f598c45d1.
def localCycle00092 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 4, .distance 0 4, .distance 2 4, .distance 2 3, .distance 3 5, .distance 4 5, .theta 4, .zero, .theta 1, .distance 1 2, .distance 1 4]
    constant := ![0, 0, 0, -1, 0, -1, 0, 0, 2, -2]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![true, true, true, false, true, false, false, false, false, false] }
  origin := ![.triangle 2 2, .triangle 6 1, .triangle 25 1, .triangle 26 0, .triangle 31 1, .corridorLower 4 5, .thetaLower 4, .thetaUpper 1, .gapLower 1 6, .gapLower 1 5]

-- Cycle fingerprint 819e3fedb27125ceccb89efb6ddc1ba3ce97cccbf1352d09b488a707118ab1b4.
def localCycle00093 : Cycle where
  length := 8
  data := {
    node := ![.distance 4 6, .distance 2 4, .theta 4, .distance 3 4, .distance 1 3, .distance 1 6, .distance 0 6, .distance 3 6, .distance 4 6]
    constant := ![-1, 0, 3, -1, -3, 0, 0, 0]
    coefficient := ![0, 0, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, true] }
  origin := ![.triangle 29 0, .gapLower 4 0, .corridorUpper 3 4, .triangle 19 0, .gapLower 1 3, .triangle 4 2, .triangle 11 1, .triangle 32 1]

-- Cycle fingerprint 81fb1f1d292a68c0eb70867b0d46c7e192ea11c103cb04ef31b4ba0a8781094b.
def localCycle00094 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 6, .distance 1 5, .distance 0 5, .distance 4 5, .distance 2 4, .distance 2 3, .theta 2, .distance 1 2, .distance 1 4, .distance 1 3, .distance 1 6]
    constant := ![-2, 0, 0, -1, 0, -1, 3, 0, -2, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![false, true, true, false, false, false, false, true, false, true] }
  origin := ![.gapLower 1 2, .triangle 3 2, .triangle 12 1, .triangle 28 0, .gapLower 2 1, .corridorLower 2 3, .corridorUpper 1 2, .triangle 16 2, .gapLower 1 4, .triangle 21 2]

-- Cycle fingerprint 82e0da35539be79c0853ebaebc23d97d81c88beb95020e5fed40af353d3cb5ba.
def localCycle00095 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .theta 1, .zero, .theta 4, .distance 3 4, .distance 1 3, .distance 1 5, .distance 0 1]
    constant := ![-3, 0, 0, 3, -1, 0, -1]
    coefficient := ![0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false] }
  origin := ![.gapLower 1 0, .thetaLower 1, .thetaUpper 4, .corridorUpper 3 4, .triangle 19 0, .triangle 20 2, .triangle 3 0]

-- Cycle fingerprint 83147c986730ee1be8a5a42ef1f8a398511746709605173943ecd2c0e2f2ad82.
def localCycle00096 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 1 3, .distance 3 5, .distance 0 3, .distance 3 6, .distance 2 6, .distance 5 6, .distance 4 5, .theta 4]
    constant := ![3, -1, -1, -1, -1, 0, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 19 0, .triangle 20 0, .triangle 10 0, .triangle 11 0, .triangle 27 2, .triangle 30 1, .triangle 34 0, .corridorLower 4 5]

-- Cycle fingerprint 8322caa1bedbd69bca637ed6bc5ce073f8d4c51de6c6293c6f4647bf307dd838.
def localCycle00097 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 6, .distance 3 6, .distance 2 3, .theta 2, .distance 1 2, .distance 1 4, .distance 1 3, .distance 1 6, .distance 0 6]
    constant := ![0, -1, -1, 3, -2, 0, -2, 0]
    coefficient := ![0, 0, 0, 1, 0, 0, 0, 0]
    strict := ![true, false, false, false, false, true, false, true] }
  origin := ![.triangle 11 1, .triangle 27 0, .corridorLower 2 3, .corridorUpper 1 2, .gapLower 1 5, .triangle 19 1, .gapLower 1 3, .triangle 4 2]

-- Cycle fingerprint 864796e1e1359bf6550f0a21904eaf943591ceb6d0898ddabc75c623b7806578.
def localCycle00098 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 3 4, .distance 1 3, .distance 3 6, .distance 2 3, .distance 3 5, .distance 4 5, .theta 4]
    constant := ![3, -1, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 19 0, .triangle 21 0, .triangle 27 0, .triangle 26 0, .triangle 31 1, .corridorLower 4 5]

-- Cycle fingerprint 86bef04538bb77a1fcd2dc42b2226703e9269b3a876a8a89aa4047fd85954e1b.
def localCycle00099 : Cycle where
  length := 5
  data := {
    node := ![.theta 4, .distance 3 4, .distance 4 5, .distance 0 4, .distance 4 6, .theta 4]
    constant := ![3, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 31 0, .triangle 12 0, .triangle 13 0, .corridorLower 4 6]

-- Cycle fingerprint 8a3489ed51beaa30feedd483fdd98f222763ad0fc1d21779f79611419d77c2e5.
def localCycle00100 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .theta 1, .distance 1 2, .distance 1 4, .distance 1 3, .distance 0 3, .distance 3 6, .distance 3 5, .distance 2 3, .theta 2]
    constant := ![0, 2, 0, -2, 0, -1, 0, -1, -1]
    coefficient := ![0, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![true, false, true, false, true, false, true, false, false] }
  origin := ![.thetaNext 1, .gapLower 1 6, .triangle 16 2, .gapLower 1 4, .triangle 1 2, .triangle 11 0, .triangle 33 1, .triangle 26 0, .corridorLower 2 3]

-- Cycle fingerprint 8dd2cefce276102763bb645f09c053f3fa592a2faeaaddfe5c0201a883ab548f.
def localCycle00101 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 3, .distance 1 5, .distance 0 5, .distance 4 5, .distance 2 4, .distance 2 3, .theta 2, .distance 1 2, .distance 1 4, .distance 1 6, .distance 1 3]
    constant := ![-2, 0, 0, -1, 0, -1, 3, 0, -2, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![false, true, true, false, false, false, false, true, false, true] }
  origin := ![.gapLower 1 2, .triangle 3 2, .triangle 12 1, .triangle 28 0, .gapLower 2 1, .corridorLower 2 3, .corridorUpper 1 2, .triangle 16 2, .gapLower 1 4, .triangle 21 1]

-- Cycle fingerprint 8f41da585eaa3d7ba26cccad5be60c76dd5aebe871d8749d6576703b9a60724a.
def localCycle00102 : Cycle where
  length := 8
  data := {
    node := ![.distance 2 4, .theta 4, .distance 3 4, .distance 1 3, .distance 1 6, .distance 1 5, .distance 0 5, .distance 4 5, .distance 2 4]
    constant := ![0, 3, -1, 0, -2, 0, 0, -1]
    coefficient := ![0, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true, true, false] }
  origin := ![.gapLower 4 0, .corridorUpper 3 4, .triangle 19 0, .triangle 21 2, .gapLower 1 2, .triangle 3 2, .triangle 12 1, .triangle 28 0]

-- Cycle fingerprint 8f7e01df937a00ba4f4398625dc911a309c991b35a2037d427d693e4cf8d4994.
def localCycle00103 : Cycle where
  length := 11
  data := {
    node := ![.distance 3 5, .distance 4 5, .theta 4, .theta 3, .theta 2, .distance 1 2, .distance 1 4, .distance 1 6, .distance 1 3, .distance 0 3, .distance 2 3, .distance 3 5]
    constant := ![0, -1, 0, 0, 3, 0, -2, -2, 0, 0, -1]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0]
    strict := ![true, false, true, true, false, true, false, false, true, true, false] }
  origin := ![.triangle 31 1, .corridorLower 4 5, .thetaNext 3, .thetaNext 2, .corridorUpper 1 2, .triangle 16 2, .gapLower 1 4, .gapLower 1 3, .triangle 1 2, .triangle 5 1, .triangle 26 0]

-- Cycle fingerprint 9044c132d02c068eab56c8823774dcea518f495d0beee3b66a46589a9466374a.
def localCycle00104 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 4, .distance 1 6, .distance 1 3, .distance 3 5, .distance 2 3, .theta 2, .distance 1 2, .distance 1 4]
    constant := ![-3, 0, -1, -1, -1, 3, 0]
    coefficient := ![0, 0, 0, 0, 0, 1, 0]
    strict := ![false, true, false, false, false, false, true] }
  origin := ![.gapLower 1 4, .triangle 21 1, .triangle 20 0, .triangle 26 0, .corridorLower 2 3, .corridorUpper 1 2, .triangle 16 2]

-- Cycle fingerprint 9109aa63ae82e9c93b5b658bad35af80f0c23e841645ddd6875d55930d556dc8.
def localCycle00105 : Cycle where
  length := 7
  data := {
    node := ![.theta 1, .distance 1 2, .distance 1 4, .distance 1 3, .distance 3 5, .distance 2 3, .theta 2, .theta 1]
    constant := ![2, 0, 0, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, false, true] }
  origin := ![.gapLower 1 6, .triangle 16 2, .triangle 19 1, .triangle 20 0, .triangle 26 0, .corridorLower 2 3, .thetaNext 1]

-- Cycle fingerprint 92c0bbee726c30a8ad8cf47337d9a50f7506e3d8175afdf310048ce147c2abcc.
def localCycle00106 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 3, .distance 3 5, .distance 2 3, .theta 2, .distance 1 2, .distance 1 4, .distance 1 6, .distance 1 3, .distance 0 3]
    constant := ![-1, -1, -1, 3, -2, 0, -2, 0]
    coefficient := ![0, 0, 0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, true] }
  origin := ![.triangle 10 0, .triangle 26 0, .corridorLower 2 3, .corridorUpper 1 2, .gapLower 1 5, .triangle 23 2, .gapLower 1 3, .triangle 1 2]

-- Cycle fingerprint 95957bc5512b4b4a0238d04bfd5b89516e61825cdf29dec29557eedfd74f5a27.
def localCycle00107 : Cycle where
  length := 3
  data := {
    node := ![.distance 3 5, .distance 1 3, .distance 1 5, .distance 3 5]
    constant := ![2, -3, 0]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.gapUpper 3 3, .gapLower 1 2, .triangle 20 1]

-- Cycle fingerprint 989330d8efbe1553a929831f920556404c75bffd62ed8a98c5ae517da38eca08.
def localCycle00108 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 4, .distance 1 6, .distance 1 3, .distance 3 5, .distance 2 3, .theta 2, .distance 1 2, .distance 1 4]
    constant := ![-2, -2, -1, -1, -1, 3, 0]
    coefficient := ![0, 0, 0, 0, 0, 1, 0]
    strict := ![false, false, false, false, false, false, true] }
  origin := ![.gapLower 1 4, .gapLower 1 3, .triangle 20 0, .triangle 26 0, .corridorLower 2 3, .corridorUpper 1 2, .triangle 16 2]

-- Cycle fingerprint 98b543c5f51c1096a01358bc3e330aa59aae1bb216e71f2d1627de3e3332f509.
def localCycle00109 : Cycle where
  length := 10
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 4, .distance 4 6, .distance 2 4, .distance 2 3, .distance 3 5, .distance 4 5, .theta 4, .theta 3, .theta 2]
    constant := ![3, 0, -1, -1, 0, -1, 0, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, true, false, true, true] }
  origin := ![.corridorUpper 1 2, .triangle 16 2, .triangle 23 0, .triangle 29 0, .gapLower 2 2, .triangle 26 0, .triangle 31 1, .corridorLower 4 5, .thetaNext 3, .thetaNext 2]

-- Cycle fingerprint 990ee65cf38669c176e154c788c7d271f68c677af818e509d07ecb0c0c2ff59b.
def localCycle00110 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 2, .distance 1 4, .distance 1 3, .distance 1 6, .distance 3 6, .distance 2 3, .theta 2, .distance 1 2]
    constant := ![-2, 0, -2, 0, -1, -1, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, false, true, false, false, false] }
  origin := ![.gapLower 1 5, .triangle 19 1, .gapLower 1 3, .triangle 21 1, .triangle 27 0, .corridorLower 2 3, .corridorUpper 1 2]

-- Cycle fingerprint 99c53c3d4b8e84ae241eac252606126641fab4925f26633c943c33ec57bf5f5c.
def localCycle00111 : Cycle where
  length := 8
  data := {
    node := ![.distance 3 6, .distance 3 5, .distance 2 3, .theta 2, .theta 1, .distance 1 2, .distance 1 4, .distance 1 3, .distance 3 6]
    constant := ![0, -1, -1, 0, 1, 0, 0, -1]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![true, false, false, true, false, true, true, false] }
  origin := ![.triangle 33 1, .triangle 26 0, .corridorLower 2 3, .thetaNext 1, .gapLower 1 6, .triangle 16 2, .triangle 19 1, .triangle 21 0]

-- Cycle fingerprint 9a05ec3c9c4b75c5623b2a8fe0b34fc48c934105ff6c50d481e085ca51103f12.
def localCycle00112 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 1 3, .distance 3 5, .distance 2 3, .distance 3 6, .distance 5 6, .distance 4 5, .theta 4]
    constant := ![4, -1, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, false] }
  origin := ![.gapLower 4 6, .triangle 19 0, .triangle 20 0, .triangle 26 0, .triangle 27 0, .triangle 33 1, .triangle 34 0, .gapLower 4 0]

-- Cycle fingerprint 9c1d9b1b35c4637b32bbd96cf911e7ffce88b7670fc40eab09eebdab069049c3.
def localCycle00113 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 2, .distance 1 4, .distance 1 3, .distance 3 6, .distance 3 5, .distance 2 3, .theta 2, .distance 1 2]
    constant := ![-2, 0, -1, 0, -1, 0, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, false, true, false, false, false] }
  origin := ![.gapLower 1 5, .triangle 19 1, .triangle 21 0, .triangle 33 1, .triangle 26 0, .gapLower 2 0, .corridorUpper 1 2]

-- Cycle fingerprint 9d68f914dcca57797d05c8d2f0bf80153aa4d215b7df03b2a4c99b9edc485153.
def localCycle00114 : Cycle where
  length := 8
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 4, .distance 4 6, .distance 0 4, .distance 0 3, .distance 3 5, .distance 2 3, .theta 2]
    constant := ![3, 0, -1, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 16 2, .triangle 23 0, .triangle 13 0, .triangle 9 1, .triangle 10 0, .triangle 26 0, .corridorLower 2 3]

-- Cycle fingerprint a006500a93c03d43cef84177300fffb6af743652055fead774895029880ce7ee.
def localCycle00115 : Cycle where
  length := 8
  data := {
    node := ![.distance 3 5, .distance 2 3, .theta 2, .distance 1 2, .distance 1 4, .distance 1 6, .distance 1 3, .distance 1 5, .distance 3 5]
    constant := ![-1, -1, 3, 0, -2, 0, -2, 0]
    coefficient := ![0, 0, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true, false, true] }
  origin := ![.triangle 26 0, .corridorLower 2 3, .corridorUpper 1 2, .triangle 16 2, .gapLower 1 4, .triangle 21 1, .gapLower 1 2, .triangle 20 1]

-- Cycle fingerprint a02cde57ee5470eba11e6bc08660a7dc78ba95d481b5b086fdd2051217d015d3.
def localCycle00116 : Cycle where
  length := 4
  data := {
    node := ![.distance 1 3, .distance 1 5, .distance 5 6, .distance 3 6, .distance 1 3]
    constant := ![-3, 2, 0, -1]
    coefficient := ![0, 0, 0, 0]
    strict := ![false, true, true, false] }
  origin := ![.gapLower 1 2, .gapUpper 5 5, .triangle 33 2, .triangle 21 0]

-- Cycle fingerprint a2ef511ab6bd370d560ba8fafbf679f87291bc0faa30d0a0aa5c333a11c9c375.
def localCycle00117 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 3, .distance 1 5, .distance 0 1, .theta 1, .zero, .theta 4, .distance 3 4, .distance 1 3]
    constant := ![-2, -1, -2, 0, 0, 3, -1]
    coefficient := ![0, 0, 0, 0, 1, 1, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 1 2, .triangle 3 0, .gapLower 1 0, .thetaLower 1, .thetaUpper 4, .corridorUpper 3 4, .triangle 19 0]

-- Cycle fingerprint a3b917a4a99cd4666779e753d3b98a55a1ef1ab1861a5386ece6b1506f45a55e.
def localCycle00118 : Cycle where
  length := 8
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 4, .distance 0 3, .distance 3 6, .distance 2 6, .distance 4 6, .distance 5 6, .theta 5]
    constant := ![3, -1, -1, -1, 0, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, true, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 0, .triangle 9 0, .triangle 11 0, .triangle 27 2, .triangle 29 1, .triangle 34 1, .corridorLower 5 6]

-- Cycle fingerprint a3f8b248247f6c084c120882762fd998af0f3e192cdf83d052745aa4c6e67592.
def localCycle00119 : Cycle where
  length := 4
  data := {
    node := ![.distance 1 4, .distance 1 3, .distance 3 6, .distance 4 6, .distance 1 4]
    constant := ![-3, -1, 0, 2]
    coefficient := ![0, 0, 0, 0]
    strict := ![false, false, true, true] }
  origin := ![.gapLower 1 4, .triangle 21 0, .triangle 32 1, .gapUpper 4 4]

-- Cycle fingerprint a3fbaf19533daecb3a0cbad918d986a31ffd450a8adc19b2aca5f5379683001b.
def localCycle00120 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 3, .distance 3 5, .distance 2 3, .theta 2, .distance 1 2, .distance 1 4, .distance 1 6, .distance 0 6, .distance 0 3]
    constant := ![-1, -1, -1, 3, -2, -2, 0, 0]
    coefficient := ![0, 0, 0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, true] }
  origin := ![.triangle 10 0, .triangle 26 0, .corridorLower 2 3, .corridorUpper 1 2, .gapLower 1 5, .gapLower 1 4, .triangle 4 2, .triangle 11 1]

-- Cycle fingerprint a4d59dca89427417b5004e4c0c9518fb3a490191da337a4b2b99444f89ea721d.
def localCycle00121 : Cycle where
  length := 8
  data := {
    node := ![.distance 3 5, .distance 2 3, .theta 2, .distance 1 2, .distance 1 4, .distance 1 6, .distance 0 6, .distance 0 3, .distance 3 5]
    constant := ![-1, -1, 3, 0, -3, 0, 0, -1]
    coefficient := ![0, 0, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true, true, false] }
  origin := ![.triangle 26 0, .corridorLower 2 3, .corridorUpper 1 2, .triangle 16 2, .gapLower 1 4, .triangle 4 2, .triangle 11 1, .triangle 10 0]

-- Cycle fingerprint a6a32800c0d29f62dbeb82dc62653ee5ba1640d44b915d6f17307f3ce952a4dc.
def localCycle00122 : Cycle where
  length := 4
  data := {
    node := ![.distance 1 3, .distance 1 5, .distance 5 6, .distance 3 6, .distance 1 3]
    constant := ![-2, 2, 0, -1]
    coefficient := ![0, 0, 0, 0]
    strict := ![false, true, false, false] }
  origin := ![.gapLower 1 2, .gapUpper 5 5, .gapLower 6 5, .triangle 21 0]

-- Cycle fingerprint a70914663e8c843dd2f6d8444da0bc45d08d8ccd8faf316563acd91bbc9c4369.
def localCycle00123 : Cycle where
  length := 4
  data := {
    node := ![.distance 1 4, .distance 1 3, .distance 3 6, .distance 4 6, .distance 1 4]
    constant := ![-2, -1, 0, 2]
    coefficient := ![0, 0, 0, 0]
    strict := ![false, false, true, true] }
  origin := ![.gapLower 1 4, .triangle 21 0, .triangle 32 1, .gapUpper 4 4]

-- Cycle fingerprint a9b09bba3affd18d5d24be35a4f2ed2c6a16fe9f977dd0ba6e9c6d55d04bd589.
def localCycle00124 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 2, .distance 1 4, .distance 1 3, .distance 1 6, .distance 1 5, .distance 0 5, .distance 3 5, .distance 2 3, .theta 2, .distance 1 2]
    constant := ![0, -2, 0, -2, 0, 0, -1, -1, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![true, false, true, false, true, true, false, false, false] }
  origin := ![.triangle 16 2, .gapLower 1 4, .triangle 21 2, .gapLower 1 2, .triangle 3 2, .triangle 10 1, .triangle 26 0, .corridorLower 2 3, .corridorUpper 1 2]

-- Cycle fingerprint a9d0160d0b86d6ee8f1e9da403804da31941e724d7175b7e80255ff4119a4d58.
def localCycle00125 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 4, .distance 1 3, .distance 1 6, .distance 1 5, .distance 0 5, .distance 3 5, .distance 2 3, .theta 2, .theta 1, .distance 1 2, .distance 1 4]
    constant := ![0, 0, -2, 0, 0, -1, -1, 0, 2, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0]
    strict := ![true, true, false, true, true, false, false, true, false, true] }
  origin := ![.triangle 19 1, .triangle 21 2, .gapLower 1 2, .triangle 3 2, .triangle 10 1, .triangle 26 0, .corridorLower 2 3, .thetaNext 1, .gapLower 1 6, .triangle 16 2]

-- Cycle fingerprint ac63858f3405cc256e61c4819b2774f7602cc4684f9bf5ae68e3cce2fcc99651.
def localCycle00126 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 4, .distance 1 6, .distance 1 3, .distance 1 5, .distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 1 4]
    constant := ![0, -2, 0, -2, -1, 0, 0, 3, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![true, false, true, false, false, false, false, false, true] }
  origin := ![.triangle 23 2, .gapLower 1 3, .triangle 20 2, .gapLower 1 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 16 2]

-- Cycle fingerprint ad84e992d12c601d8aef6f91070aa08c78028c10c27823d83680ee55d004fe11.
def localCycle00127 : Cycle where
  length := 3
  data := {
    node := ![.distance 3 4, .distance 1 4, .distance 1 3, .distance 3 4]
    constant := ![0, -3, 2]
    coefficient := ![0, 0, 0]
    strict := ![false, false, true] }
  origin := ![.gapLower 4 5, .gapLower 1 4, .gapUpper 3 5]

-- Cycle fingerprint b0b5749a630f0ec269c964cdda0959968693f5918becda483fe343c925463745.
def localCycle00128 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 3 4, .distance 1 3, .distance 3 5, .distance 0 3, .distance 3 6, .distance 2 3, .theta 3]
    constant := ![4, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 3 6, .triangle 19 0, .triangle 20 0, .triangle 10 0, .triangle 11 0, .triangle 27 0, .gapLower 3 0]

-- Cycle fingerprint b13e3ca157dc9975e2f6bf16ad8cb4724aaff257cc75fd092f40bf224a3562ca.
def localCycle00129 : Cycle where
  length := 8
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 4, .distance 4 5, .distance 0 4, .distance 4 6, .distance 2 4, .distance 2 3, .theta 2]
    constant := ![3, 0, -1, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 16 2, .triangle 22 0, .triangle 12 0, .triangle 13 0, .triangle 29 0, .gapLower 2 1, .corridorLower 2 3]

-- Cycle fingerprint b735dd640d017b14231a392853dc6e6e967ebe3d785838b0aab31cd903c13de3.
def localCycle00130 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 3, .distance 1 6, .distance 1 5, .distance 0 5, .distance 3 5, .distance 4 5, .distance 2 4, .theta 4, .distance 3 4, .distance 1 3]
    constant := ![0, -2, 0, 0, 0, -1, 0, 3, -1]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1, 0]
    strict := ![true, false, true, true, true, false, false, false, false] }
  origin := ![.triangle 21 2, .gapLower 1 2, .triangle 3 2, .triangle 10 1, .triangle 31 1, .triangle 28 0, .gapLower 4 0, .corridorUpper 3 4, .triangle 19 0]

-- Cycle fingerprint b873b128e5cdd2c84f9e26e5dafaae6325c12cbc010bab213569d3a17f0540a2.
def localCycle00131 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 4, .distance 1 3, .distance 3 6, .distance 3 5, .distance 2 3, .theta 2, .distance 1 2, .distance 1 4]
    constant := ![-2, -1, 0, -1, -1, 3, 0]
    coefficient := ![0, 0, 0, 0, 0, 1, 0]
    strict := ![false, false, true, false, false, false, true] }
  origin := ![.gapLower 1 4, .triangle 21 0, .triangle 33 1, .triangle 26 0, .corridorLower 2 3, .corridorUpper 1 2, .triangle 16 2]

-- Cycle fingerprint b940089494e7dd26676028559a5fa3a8806944d646b096ff811dcc2f0d4a8242.
def localCycle00132 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 2, .distance 1 4, .distance 1 6, .distance 0 6, .distance 2 6, .distance 2 3, .theta 2, .distance 1 2]
    constant := ![-2, -2, 0, 0, 0, -1, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![false, false, true, true, true, false, false] }
  origin := ![.gapLower 1 5, .gapLower 1 4, .triangle 4 2, .triangle 8 1, .triangle 27 1, .corridorLower 2 3, .corridorUpper 1 2]

-- Cycle fingerprint b951451f7644054e9dfeea183fe00dccd698bb43d2e49551a305fdea9bed0f6c.
def localCycle00133 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 1 3, .distance 3 6, .distance 0 3, .distance 3 5, .distance 4 5, .distance 2 4, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, -1, -1, -1, -1, 0, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, false, true, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 19 0, .triangle 21 0, .triangle 11 0, .triangle 10 0, .triangle 31 1, .triangle 28 0, .triangle 25 1, .corridorLower 2 3, .thetaLower 2]

-- Cycle fingerprint b9aa3f909124bc1d950cb22a7bd6b2b98f840a0b874e01a143dde92fc8ce1f1e.
def localCycle00134 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 3, .distance 0 1, .theta 1, .zero, .theta 4, .distance 3 4, .distance 1 3, .distance 3 6, .distance 3 5, .distance 0 3]
    constant := ![0, -3, 0, 0, 3, -1, -1, 0, 0]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![true, false, false, false, false, false, false, true, false] }
  origin := ![.triangle 1 1, .gapLower 1 0, .thetaLower 1, .thetaUpper 4, .corridorUpper 3 4, .triangle 19 0, .triangle 21 0, .triangle 33 1, .gapLower 3 2]

-- Cycle fingerprint b9d2940b6c1ce459daa71a91967245b8defa22d531124eba43cdbc86fec79ada.
def localCycle00135 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .theta 1, .distance 1 2, .distance 1 4, .distance 1 3, .distance 1 6, .distance 1 5, .distance 3 5, .distance 2 3, .theta 2]
    constant := ![0, 2, 0, 0, 0, -2, 0, -1, -1]
    coefficient := ![0, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![true, false, true, true, true, false, true, false, false] }
  origin := ![.thetaNext 1, .gapLower 1 6, .triangle 16 2, .triangle 19 1, .triangle 21 2, .gapLower 1 2, .triangle 20 1, .triangle 26 0, .corridorLower 2 3]

-- Cycle fingerprint ba2ab68dc563a8ee57ca6aee19bf58c53d22f717d40e93ff174b90c86f869cc2.
def localCycle00136 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 4, .distance 1 3, .distance 1 5, .distance 0 5, .distance 4 5, .distance 2 4, .distance 2 3, .theta 2]
    constant := ![3, -2, 0, -2, 0, 0, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, true, false, false, false] }
  origin := ![.corridorUpper 1 2, .gapLower 1 5, .triangle 19 1, .gapLower 1 2, .triangle 3 2, .triangle 12 1, .triangle 28 0, .gapLower 2 1, .corridorLower 2 3]

-- Cycle fingerprint ba5ee3b60488eff67ac4acfaab6969b98daf392ae7a68868f63a3ce4e25cab27.
def localCycle00137 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 2, .distance 1 4, .distance 1 6, .distance 1 3, .distance 3 5, .distance 2 3, .theta 2, .distance 1 2]
    constant := ![-2, 0, -2, -1, -1, -1, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, false, false, false, false, false] }
  origin := ![.gapLower 1 5, .triangle 23 2, .gapLower 1 3, .triangle 20 0, .triangle 26 0, .corridorLower 2 3, .corridorUpper 1 2]

-- Cycle fingerprint bbc01e1a3028ab5ec491b5fbef63861bd36f628df8e538f618c4b16ba51bfec4.
def localCycle00138 : Cycle where
  length := 8
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 4, .distance 4 6, .distance 0 4, .distance 4 5, .distance 2 4, .distance 2 3, .theta 2]
    constant := ![3, 0, -1, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 16 2, .triangle 23 0, .triangle 13 0, .triangle 12 0, .triangle 28 0, .gapLower 2 1, .corridorLower 2 3]

-- Cycle fingerprint bc2f4802fc86aa15e4170c701374d2de1fe22f08e25a6b703507e24f952a7d4b.
def localCycle00139 : Cycle where
  length := 8
  data := {
    node := ![.distance 3 6, .distance 3 5, .distance 2 3, .theta 2, .theta 1, .distance 1 2, .distance 1 4, .distance 1 3, .distance 3 6]
    constant := ![0, -1, -1, 0, 2, -2, 0, -1]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![true, false, false, true, false, false, true, false] }
  origin := ![.triangle 33 1, .triangle 26 0, .corridorLower 2 3, .thetaNext 1, .gapLower 1 6, .gapLower 1 5, .triangle 19 1, .triangle 21 0]

-- Cycle fingerprint bd226e0c629ad0797a9bae6805b15a478cc526faab269775dbe6bc49bd1d1f09.
def localCycle00140 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 1 3, .distance 1 6, .distance 1 5, .distance 0 1, .theta 1, .zero, .theta 4]
    constant := ![3, -1, 0, 0, -2, -2, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 1]
    strict := ![false, false, true, true, false, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 19 0, .triangle 21 2, .triangle 24 1, .gapLower 1 1, .gapLower 1 0, .thetaLower 1, .thetaUpper 4]

-- Cycle fingerprint befeea78a22b5da7cc8bd6f5e14cf11dffd62d3508ecb5d3d5d1187c80539511.
def localCycle00141 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 3 4, .distance 1 3, .distance 3 6, .distance 4 6, .distance 2 4, .distance 4 5, .theta 4]
    constant := ![3, -1, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 19 0, .triangle 21 0, .triangle 32 1, .triangle 29 0, .triangle 28 0, .corridorLower 4 5]

-- Cycle fingerprint bfbc5a7a8e9b96b69cbbd56824058a3bb0697599af65e25edf7e97c5b6e42026.
def localCycle00142 : Cycle where
  length := 8
  data := {
    node := ![.distance 2 5, .distance 4 5, .theta 4, .distance 3 4, .distance 1 3, .distance 1 6, .distance 1 5, .distance 0 5, .distance 2 5]
    constant := ![0, -1, 3, -1, -2, -2, 0, 0]
    coefficient := ![0, 0, 1, 0, 0, 0, 0, 0]
    strict := ![true, false, false, false, false, false, true, true] }
  origin := ![.triangle 28 1, .corridorLower 4 5, .corridorUpper 3 4, .triangle 19 0, .gapLower 1 3, .gapLower 1 2, .triangle 3 2, .triangle 7 1]

-- Cycle fingerprint bfd53a76f5c21cb30975ea53f8fa26c5fd34862762e3bc75828923492eaef3cb.
def localCycle00143 : Cycle where
  length := 12
  data := {
    node := ![.distance 1 3, .distance 3 5, .distance 2 3, .theta 2, .theta 1, .distance 1 2, .distance 0 2, .distance 2 4, .distance 4 6, .distance 4 5, .theta 4, .distance 3 4, .distance 1 3]
    constant := ![-1, -1, -1, 0, 2, 0, -1, -1, 0, -1, 3, -1]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0]
    strict := ![false, false, false, true, false, true, false, false, true, false, false, false] }
  origin := ![.triangle 20 0, .triangle 26 0, .corridorLower 2 3, .thetaNext 1, .gapLower 1 6, .triangle 0 2, .triangle 6 0, .triangle 29 0, .triangle 34 1, .corridorLower 4 5, .corridorUpper 3 4, .triangle 19 0]

-- Cycle fingerprint c55cdfe2403613308600deaf75f6517b3e5e972797fb4f295adc5be4ea85375f.
def localCycle00144 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 0 3, .distance 3 5, .distance 2 3, .distance 3 6, .distance 5 6, .distance 4 5, .theta 4]
    constant := ![4, -1, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, false] }
  origin := ![.gapLower 4 6, .triangle 9 0, .triangle 10 0, .triangle 26 0, .triangle 27 0, .triangle 33 1, .triangle 34 0, .gapLower 4 0]

-- Cycle fingerprint c85c6bea968ac02d980e541ca3e36edb578c4fa58ff2f6587c0f5343647342aa.
def localCycle00145 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 1 3, .distance 1 5, .distance 5 6, .distance 3 5, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, -1, 0, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 19 0, .triangle 20 2, .triangle 24 0, .triangle 33 0, .triangle 26 0, .corridorLower 2 3, .thetaLower 2]

-- Cycle fingerprint c9d9af8e914a26bde4c08f1afa6371c53364da399775b07a8c39ea9b7c51f6a9.
def localCycle00146 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 3 4, .distance 0 3, .distance 3 5, .distance 4 5, .distance 2 4, .distance 4 6, .theta 4]
    constant := ![3, -1, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 9 0, .triangle 10 0, .triangle 31 1, .triangle 28 0, .triangle 29 0, .corridorLower 4 6]

-- Cycle fingerprint cbe8ea30f2b29688614bf2c6dde7e8d36c50564539b51048daad9bba1b79d719.
def localCycle00147 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 3 4, .distance 0 3, .distance 3 6, .distance 2 6, .distance 5 6, .distance 4 5, .theta 4]
    constant := ![3, -1, -1, 0, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 9 0, .triangle 11 0, .triangle 27 2, .triangle 30 1, .triangle 34 0, .corridorLower 4 5]

-- Cycle fingerprint cc4579050269b39f0e089780f2d4111bf98665f3cbbf99a84a90800cd25ed6cd.
def localCycle00148 : Cycle where
  length := 7
  data := {
    node := ![.theta 1, .distance 1 2, .distance 1 4, .distance 1 3, .distance 3 5, .distance 2 3, .theta 2, .theta 1]
    constant := ![2, -2, 0, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, true] }
  origin := ![.gapLower 1 6, .gapLower 1 5, .triangle 19 1, .triangle 20 0, .triangle 26 0, .corridorLower 2 3, .thetaNext 1]

-- Cycle fingerprint cd347d011a179f334acfb955da8f44241c64093598793bdf518070ac9a6d8c0e.
def localCycle00149 : Cycle where
  length := 8
  data := {
    node := ![.distance 2 4, .theta 4, .distance 3 4, .distance 1 3, .distance 1 6, .distance 1 5, .distance 3 5, .distance 4 5, .distance 2 4]
    constant := ![0, 3, -1, 0, -2, 0, 0, -1]
    coefficient := ![0, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true, true, false] }
  origin := ![.gapLower 4 0, .corridorUpper 3 4, .triangle 19 0, .triangle 21 2, .gapLower 1 2, .triangle 20 1, .triangle 31 1, .triangle 28 0]

-- Cycle fingerprint cee643d2db74fb9f6be9d9a6a2910ce0d716edd4bda9b28ecaf47f3c8f861d0d.
def localCycle00150 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 1 3, .distance 1 6, .distance 1 5, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, -1, 0, -2, -2, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 19 0, .triangle 21 2, .gapLower 1 2, .gapLower 1 1, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint d19730be4109e47c78ad47c6f556a9d1333d65e89898e3874e0b261a4c101a21.
def localCycle00151 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 4, .distance 1 3, .distance 3 6, .distance 3 5, .distance 2 3, .theta 2, .distance 1 2, .distance 1 4]
    constant := ![-2, -1, 0, -1, 0, 3, 0]
    coefficient := ![0, 0, 0, 0, 0, 1, 0]
    strict := ![false, false, true, false, false, false, true] }
  origin := ![.gapLower 1 4, .triangle 21 0, .triangle 33 1, .triangle 26 0, .gapLower 2 0, .corridorUpper 1 2, .triangle 16 2]

-- Cycle fingerprint d255c17b146930edecc4973a373da07091da41ab8e206fc62728107ae4d9bfc9.
def localCycle00152 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .theta 1, .distance 1 2, .distance 1 4, .distance 0 4, .distance 0 3, .distance 3 6, .distance 3 5, .distance 2 3, .theta 2]
    constant := ![0, 2, -2, 0, 0, -1, 0, -1, -1]
    coefficient := ![0, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![true, false, false, true, true, false, true, false, false] }
  origin := ![.thetaNext 1, .gapLower 1 6, .gapLower 1 5, .triangle 2 2, .triangle 9 1, .triangle 11 0, .triangle 33 1, .triangle 26 0, .corridorLower 2 3]

-- Cycle fingerprint d3b8cc55428da299d85fa76623f9d2a5975999196bbb382c8fedc295e381a0de.
def localCycle00153 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 2, .distance 1 4, .distance 1 3, .distance 3 6, .distance 3 5, .distance 2 3, .theta 2, .distance 1 2]
    constant := ![-2, -2, -1, 0, -1, -1, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![false, false, false, true, false, false, false] }
  origin := ![.gapLower 1 5, .gapLower 1 4, .triangle 21 0, .triangle 33 1, .triangle 26 0, .corridorLower 2 3, .corridorUpper 1 2]

-- Cycle fingerprint d4636b5ba2139c7532652b440af0e31e666407bd9be6a65f3461eef521efcf97.
def localCycle00154 : Cycle where
  length := 12
  data := {
    node := ![.distance 0 3, .distance 3 5, .distance 2 3, .theta 2, .theta 1, .distance 1 2, .distance 0 2, .distance 2 4, .distance 4 6, .distance 4 5, .theta 4, .distance 3 4, .distance 0 3]
    constant := ![-1, -1, -1, 0, 2, 0, -1, -1, 0, -1, 3, -1]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0]
    strict := ![false, false, false, true, false, true, false, false, true, false, false, false] }
  origin := ![.triangle 10 0, .triangle 26 0, .corridorLower 2 3, .thetaNext 1, .gapLower 1 6, .triangle 0 2, .triangle 6 0, .triangle 29 0, .triangle 34 1, .corridorLower 4 5, .corridorUpper 3 4, .triangle 9 0]

-- Cycle fingerprint d7ec84da5800cfc84971d43c5e07360e008ce90d5b12657cb5f80dda1a514484.
def localCycle00155 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 1 3, .distance 3 5, .distance 0 3, .distance 3 6, .distance 5 6, .distance 4 5, .theta 4]
    constant := ![3, -1, -1, -1, -1, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 19 0, .triangle 20 0, .triangle 10 0, .triangle 11 0, .triangle 33 1, .triangle 34 0, .corridorLower 4 5]

-- Cycle fingerprint d960fc50837c2796b2ef58024ed05b635ff8831c6fa9ecd3a8e9ecb7b229b742.
def localCycle00156 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 4, .distance 1 3, .distance 1 6, .distance 3 6, .distance 2 3, .theta 2, .distance 1 2, .distance 1 4]
    constant := ![-2, -2, 0, -1, -1, 3, 0]
    coefficient := ![0, 0, 0, 0, 0, 1, 0]
    strict := ![false, false, true, false, false, false, true] }
  origin := ![.gapLower 1 4, .gapLower 1 3, .triangle 21 1, .triangle 27 0, .corridorLower 2 3, .corridorUpper 1 2, .triangle 16 2]

-- Cycle fingerprint da8104f05aedbe4ed1f580c12cfb91b59a10631a5564952788f87b6a5034a31c.
def localCycle00157 : Cycle where
  length := 6
  data := {
    node := ![.theta 4, .distance 3 4, .distance 0 3, .distance 3 5, .distance 5 6, .distance 4 5, .theta 4]
    constant := ![3, -1, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 9 0, .triangle 10 0, .triangle 33 0, .triangle 34 0, .corridorLower 4 5]

-- Cycle fingerprint dd0ff7313879b2eafa3f9f66052f13236ec4bb628389f6170bd4e5af2ef9ca1e.
def localCycle00158 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 1 3, .distance 3 5, .distance 2 5, .distance 4 5, .distance 5 6, .theta 5, .theta 4]
    constant := ![3, -1, -1, 0, 0, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false, false, true] }
  origin := ![.corridorUpper 3 4, .triangle 19 0, .triangle 20 0, .triangle 26 2, .triangle 28 1, .triangle 34 0, .corridorLower 5 6, .thetaNext 4]

-- Cycle fingerprint de6e01895cd473fba04a3114b047e9eecaa24ac8ef902fafbec62dc25e029a50.
def localCycle00159 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 2, .distance 1 4, .distance 0 4, .distance 0 3, .distance 3 5, .distance 2 3, .theta 2, .distance 1 2]
    constant := ![-3, 0, 0, -1, -1, -1, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, true, false, false, false, false] }
  origin := ![.gapLower 1 5, .triangle 2 2, .triangle 9 1, .triangle 10 0, .triangle 26 0, .corridorLower 2 3, .corridorUpper 1 2]

-- Cycle fingerprint deb393382ee3b0ca7b8043743f5cb5372a96066e8985bba225acccf0c8a24f4d.
def localCycle00160 : Cycle where
  length := 7
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 4, .distance 0 3, .distance 3 6, .distance 4 6, .distance 5 6, .theta 5]
    constant := ![3, -1, -1, -1, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 0, .triangle 9 0, .triangle 11 0, .triangle 32 1, .triangle 34 1, .corridorLower 5 6]

-- Cycle fingerprint e1731dee42e49bea2648620de756e9be8521c3f046f9554a5ca8a77c874b6ba0.
def localCycle00161 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 3 4, .distance 1 3, .distance 3 5, .distance 2 5, .distance 5 6, .theta 5, .theta 4]
    constant := ![3, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, true] }
  origin := ![.corridorUpper 3 4, .triangle 19 0, .triangle 20 0, .triangle 26 2, .triangle 30 0, .corridorLower 5 6, .thetaNext 4]

-- Cycle fingerprint e1f7e979d1aeee0123054de85cbf96b22a9c3290ba44afcb017f1043708f2ae0.
def localCycle00162 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 0 3, .distance 0 5, .distance 5 6, .distance 3 6, .distance 2 3, .distance 3 5, .distance 4 5, .theta 4]
    constant := ![3, -1, 0, -1, 0, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 9 0, .triangle 10 2, .triangle 14 0, .triangle 33 2, .triangle 27 0, .triangle 26 0, .triangle 31 1, .corridorLower 4 5]

-- Cycle fingerprint e244521a55a43a674d54ba366c596d09973fe6ec7d5a007ecc11abec71bfe704.
def localCycle00163 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 5, .distance 0 1, .theta 1, .zero, .theta 4, .distance 3 4, .distance 1 3, .distance 1 5]
    constant := ![-2, -2, 0, 0, 3, -1, 0]
    coefficient := ![0, 0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, false, false, false, true] }
  origin := ![.gapLower 1 1, .gapLower 1 0, .thetaLower 1, .thetaUpper 4, .corridorUpper 3 4, .triangle 19 0, .triangle 20 2]

-- Cycle fingerprint e2d457c596d16d7496a918c423fae6d02f116068b34f739c2bba7c5af770c325.
def localCycle00164 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 3, .distance 3 5, .distance 2 3, .theta 2, .theta 1, .distance 1 2, .distance 0 2, .distance 0 4, .distance 0 3]
    constant := ![-1, -1, -1, 0, 1, 0, 0, 0]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, true, false, true, true, true] }
  origin := ![.triangle 10 0, .triangle 26 0, .corridorLower 2 3, .thetaNext 1, .gapLower 1 6, .triangle 0 2, .triangle 6 2, .triangle 9 1]

-- Cycle fingerprint e4006fcdc0f6f4483d67032eb593c94cea2ea67fa2793edd38bb96ae161213cf.
def localCycle00165 : Cycle where
  length := 13
  data := {
    node := ![.distance 2 3, .theta 2, .theta 1, .distance 1 2, .distance 0 2, .distance 2 4, .distance 4 6, .distance 4 5, .theta 4, .distance 3 4, .distance 1 3, .distance 3 6, .distance 3 5, .distance 2 3]
    constant := ![-1, 0, 2, 0, -1, -1, 0, -1, 3, -1, -1, 0, -1]
    coefficient := ![0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, true, false, false, false, false, true, false] }
  origin := ![.corridorLower 2 3, .thetaNext 1, .gapLower 1 6, .triangle 0 2, .triangle 6 0, .triangle 29 0, .triangle 34 1, .corridorLower 4 5, .corridorUpper 3 4, .triangle 19 0, .triangle 21 0, .triangle 33 1, .triangle 26 0]

-- Cycle fingerprint e5a76f38a1f17286db17cc3fa11e710957b1e912d2da0d70f39e49793502886d.
def localCycle00166 : Cycle where
  length := 6
  data := {
    node := ![.distance 1 3, .distance 3 5, .distance 2 3, .theta 2, .distance 1 2, .distance 1 4, .distance 1 3]
    constant := ![-1, -1, -1, 3, -2, 0]
    coefficient := ![0, 0, 0, 1, 0, 0]
    strict := ![false, false, false, false, false, true] }
  origin := ![.triangle 20 0, .triangle 26 0, .corridorLower 2 3, .corridorUpper 1 2, .gapLower 1 5, .triangle 19 1]

-- Cycle fingerprint e5e751b4ee20c6b55ab3a0e1bdf422b9c30004ebca914ef2ebdb4370c4714da5.
def localCycle00167 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 3, .distance 3 5, .distance 2 3, .theta 2, .theta 1, .distance 1 2, .distance 1 4, .distance 0 4, .distance 0 3]
    constant := ![-1, -1, -1, 0, 2, -2, 0, 0]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, true, false, false, true, true] }
  origin := ![.triangle 10 0, .triangle 26 0, .corridorLower 2 3, .thetaNext 1, .gapLower 1 6, .gapLower 1 5, .triangle 2 2, .triangle 9 1]

-- Cycle fingerprint e639920ee2e2b85d4257a2361307c5d0a1a571b2079095e17feb3d3ade621548.
def localCycle00168 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 0 3, .distance 0 5, .distance 5 6, .distance 4 6, .distance 2 4, .distance 4 5, .theta 4]
    constant := ![3, -1, 0, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 9 0, .triangle 10 2, .triangle 14 0, .triangle 34 2, .triangle 29 0, .triangle 28 0, .corridorLower 4 5]

-- Cycle fingerprint e67657616e3e494d71853a3b756483478e62198129a837a09ec60a3727713538.
def localCycle00169 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .theta 1, .zero, .theta 2, .distance 1 2, .distance 1 4, .distance 0 1]
    constant := ![-2, 0, 0, 3, -2, -1]
    coefficient := ![0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 1 0, .thetaLower 1, .thetaUpper 2, .corridorUpper 1 2, .gapLower 1 5, .triangle 2 0]

-- Cycle fingerprint e95c5d396b6023bb059bae9028e1fca08c78f58a31a330f7f39b94aa725c09f7.
def localCycle00170 : Cycle where
  length := 8
  data := {
    node := ![.distance 3 4, .distance 1 3, .distance 1 6, .distance 1 5, .distance 0 1, .theta 1, .zero, .theta 4, .distance 3 4]
    constant := ![-1, 0, 0, -1, -3, 0, 0, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 1]
    strict := ![false, true, true, false, false, false, false, false] }
  origin := ![.triangle 19 0, .triangle 21 2, .triangle 24 1, .triangle 3 0, .gapLower 1 0, .thetaLower 1, .thetaUpper 4, .corridorUpper 3 4]

-- Cycle fingerprint ea3fa1b915c306da88c49093aa182d2ff9d6cd27f6044e8da7f076129d52c4ec.
def localCycle00171 : Cycle where
  length := 12
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 2, .distance 2 4, .distance 4 5, .distance 5 6, .theta 5, .theta 4, .distance 3 4, .distance 0 3, .distance 3 6, .distance 2 3, .theta 2]
    constant := ![3, 0, -1, -1, -1, -1, 0, 3, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, true, false, false, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 0 2, .triangle 6 0, .triangle 28 0, .triangle 34 0, .corridorLower 5 6, .thetaNext 4, .corridorUpper 3 4, .triangle 9 0, .triangle 11 0, .triangle 27 0, .corridorLower 2 3]

-- Cycle fingerprint eadf81ca082d433c693938a608104a4ac93421e082a10332f128520bdcba4ebc.
def localCycle00172 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 1 3, .distance 3 5, .distance 4 5, .distance 0 4, .distance 4 6, .distance 2 4, .theta 4]
    constant := ![3, -1, -1, 0, 0, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 19 0, .triangle 20 0, .triangle 31 1, .gapLower 4 3, .triangle 13 0, .triangle 29 0, .gapLower 4 0]

-- Cycle fingerprint ec6106683d7baa41d0a1b4ff9c85e8dfa5b8aa247c3b6d8874759e9a0bb1530d.
def localCycle00173 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 3 4, .distance 1 3, .distance 1 5, .distance 5 6, .distance 4 5, .distance 2 4, .theta 4]
    constant := ![3, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 19 0, .triangle 20 2, .triangle 24 0, .triangle 34 0, .triangle 28 0, .gapLower 4 0]

-- Cycle fingerprint ed82dc2635422fcc7bdebd2f3dae2009d608d9dcfda19b702837694905a4c00f.
def localCycle00174 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .theta 1, .distance 1 2, .distance 0 2, .distance 0 4, .distance 0 3, .distance 3 6, .distance 3 5, .distance 2 3, .theta 2]
    constant := ![0, 2, 0, 0, 0, -1, 0, -1, -1]
    coefficient := ![0, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![true, false, true, true, true, false, true, false, false] }
  origin := ![.thetaNext 1, .gapLower 1 6, .triangle 0 2, .triangle 6 2, .triangle 9 1, .triangle 11 0, .triangle 33 1, .triangle 26 0, .corridorLower 2 3]

-- Cycle fingerprint ee95785255b16eef7a4d51f0463e31264c6551abaac1d5c69eea3c87a4e0b4f3.
def localCycle00175 : Cycle where
  length := 6
  data := {
    node := ![.theta 4, .distance 3 4, .distance 0 3, .distance 3 6, .distance 5 6, .distance 4 5, .theta 4]
    constant := ![3, -1, -1, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 9 0, .triangle 11 0, .triangle 33 1, .triangle 34 0, .corridorLower 4 5]

-- Cycle fingerprint f01ddb9ed9e0ef123439082d143bc9ed908dc9dd11535963030e7d83a7d95edf.
def localCycle00176 : Cycle where
  length := 9
  data := {
    node := ![.distance 3 4, .distance 4 6, .distance 1 4, .distance 1 3, .distance 3 5, .distance 2 3, .theta 2, .zero, .theta 4, .distance 3 4]
    constant := ![-1, -1, 0, -1, -1, -1, 0, 0, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1, 1]
    strict := ![false, false, false, false, false, false, false, false, false] }
  origin := ![.triangle 32 0, .triangle 23 0, .gapLower 1 3, .triangle 20 0, .triangle 26 0, .corridorLower 2 3, .thetaLower 2, .thetaUpper 4, .corridorUpper 3 4]

-- Cycle fingerprint f0d230c19d647462804039d5e115fca0a8d3d91e9e892c3a265be4e340cc20d0.
def localCycle00177 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 0 3, .distance 3 5, .distance 2 5, .distance 4 5, .distance 5 6, .theta 5, .theta 4]
    constant := ![3, -1, -1, 0, 0, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false, false, true] }
  origin := ![.corridorUpper 3 4, .triangle 9 0, .triangle 10 0, .triangle 26 2, .triangle 28 1, .triangle 34 0, .corridorLower 5 6, .thetaNext 4]

-- Cycle fingerprint f17c951c418aaedeb4bde9e4bcc4a53d9c62bcd4149df665eebf7a36f8876811.
def localCycle00178 : Cycle where
  length := 8
  data := {
    node := ![.distance 3 5, .distance 2 3, .theta 2, .distance 1 2, .distance 1 4, .distance 1 6, .distance 0 6, .distance 0 3, .distance 3 5]
    constant := ![-1, -1, 3, 0, -2, 0, 0, -1]
    coefficient := ![0, 0, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true, true, false] }
  origin := ![.triangle 26 0, .corridorLower 2 3, .corridorUpper 1 2, .triangle 16 2, .gapLower 1 4, .triangle 4 2, .triangle 11 1, .triangle 10 0]

-- Cycle fingerprint f1e12fa949d00357cb5ff1a964799eae1817cb416a27e1d41660c7240cb0bb0b.
def localCycle00179 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 3, .distance 1 6, .distance 0 6, .distance 4 6, .distance 2 4, .theta 4, .distance 3 4, .distance 1 3]
    constant := ![-2, 0, 0, -1, 0, 3, -1]
    coefficient := ![0, 0, 0, 0, 0, 1, 0]
    strict := ![false, true, true, false, false, false, false] }
  origin := ![.gapLower 1 3, .triangle 4 2, .triangle 13 1, .triangle 29 0, .gapLower 4 0, .corridorUpper 3 4, .triangle 19 0]

-- Cycle fingerprint f1fe5eb40e8773fcd289b7918ac94bab2207b400706e0659d3ddb69ace4c4a2c.
def localCycle00180 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 4 6, .distance 1 4, .distance 0 4, .distance 2 4, .distance 2 3, .distance 3 5, .distance 4 5, .theta 4]
    constant := ![3, -1, -1, 0, 0, 0, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, true, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 32 0, .triangle 23 0, .triangle 2 2, .triangle 6 1, .triangle 25 1, .triangle 26 0, .triangle 31 1, .corridorLower 4 5]

-- Cycle fingerprint f372f289f648366fe2a447275a1eb39df440fa6b21ca4b1409ca1c320a870d04.
def localCycle00181 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 4, .distance 1 3, .distance 3 5, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, 0, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 0, .triangle 19 0, .triangle 20 0, .triangle 26 0, .corridorLower 2 3, .thetaLower 2]

-- Cycle fingerprint f40e303c3664d44cc3309f99ecf9f63c6e784072d7de68abb819437d2c2f4e7c.
def localCycle00182 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 1 3, .distance 3 6, .distance 4 6, .distance 0 4, .distance 4 5, .distance 2 4, .theta 4]
    constant := ![3, -1, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 19 0, .triangle 21 0, .triangle 32 1, .triangle 13 0, .triangle 12 0, .triangle 28 0, .gapLower 4 0]

-- Cycle fingerprint f501a8ab2fd761ebc36c662faf824874cee681aaa284ee225e95a65716db0f24.
def localCycle00183 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 4, .distance 1 6, .distance 1 3, .distance 3 5, .distance 2 3, .theta 2, .distance 1 2, .distance 1 4]
    constant := ![-2, 0, -1, -1, -1, 3, 0]
    coefficient := ![0, 0, 0, 0, 0, 1, 0]
    strict := ![false, true, false, false, false, false, true] }
  origin := ![.gapLower 1 4, .triangle 21 1, .triangle 20 0, .triangle 26 0, .corridorLower 2 3, .corridorUpper 1 2, .triangle 16 2]

-- Cycle fingerprint f526263cfd9c4dc8f6e75977d7c2ea2126187628f0cf17a03e84e7dc768b3118.
def localCycle00184 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 2, .distance 1 2, .distance 1 4, .distance 1 6, .distance 1 3, .distance 0 1, .theta 1, .zero]
    constant := ![0, 3, 0, 0, -2, -1, -2, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, false] }
  origin := ![.thetaUpper 2, .corridorUpper 1 2, .triangle 16 2, .triangle 23 2, .gapLower 1 3, .triangle 1 0, .gapLower 1 0, .thetaLower 1]

-- Cycle fingerprint f5f8146a4b8285c1f22b6b13c6ea977204bde18e07fa0a7b8fcbc4b324b1fcb3.
def localCycle00185 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 5, .distance 3 5, .distance 2 3, .theta 2, .distance 1 2, .distance 1 4, .distance 1 3, .distance 1 5, .distance 0 5]
    constant := ![0, -1, -1, 3, -2, 0, -2, 0]
    coefficient := ![0, 0, 0, 1, 0, 0, 0, 0]
    strict := ![true, false, false, false, false, true, false, true] }
  origin := ![.triangle 10 1, .triangle 26 0, .corridorLower 2 3, .corridorUpper 1 2, .gapLower 1 5, .triangle 19 1, .gapLower 1 2, .triangle 3 2]

-- Cycle fingerprint f6257621e448b0c6ddc8388c5a09948054b43c92f1aa39c3be3e806fcb0c3134.
def localCycle00186 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 2, .distance 1 4, .distance 1 6, .distance 1 3, .distance 1 5, .distance 0 5, .distance 3 5, .distance 2 3, .theta 2, .distance 1 2]
    constant := ![0, -2, 0, -2, 0, 0, -1, -1, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![true, false, true, false, true, true, false, false, false] }
  origin := ![.triangle 16 2, .gapLower 1 4, .triangle 21 1, .gapLower 1 2, .triangle 3 2, .triangle 10 1, .triangle 26 0, .corridorLower 2 3, .corridorUpper 1 2]

-- Cycle fingerprint f753e12f8cc512227c32bafb952080bb8efdc1c77f6d26814ff1b33992a27ca7.
def localCycle00187 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 3, .distance 1 6, .distance 3 6, .distance 4 6, .distance 2 4, .theta 4, .distance 3 4, .distance 1 3]
    constant := ![-2, 0, 0, -1, 0, 3, -1]
    coefficient := ![0, 0, 0, 0, 0, 1, 0]
    strict := ![false, true, true, false, false, false, false] }
  origin := ![.gapLower 1 3, .triangle 21 1, .triangle 32 1, .triangle 29 0, .gapLower 4 0, .corridorUpper 3 4, .triangle 19 0]

-- Cycle fingerprint f79d4a892dc62784ce0766a3555398f00eaffbb2d7dc1a9a8efe52e97a20276e.
def localCycle00188 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 4, .distance 1 3, .distance 1 6, .distance 0 6, .distance 4 6, .distance 2 4, .distance 2 3, .theta 2, .theta 1, .distance 1 2, .distance 1 4]
    constant := ![0, -2, 0, 0, -1, 0, -1, 0, 2, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0]
    strict := ![true, false, true, true, false, false, false, true, false, true] }
  origin := ![.triangle 19 1, .gapLower 1 3, .triangle 4 2, .triangle 13 1, .triangle 29 0, .gapLower 2 1, .corridorLower 2 3, .thetaNext 1, .gapLower 1 6, .triangle 16 2]

-- Cycle fingerprint f867fe0ae390251565815951b1def631df85e1fbddca52ebc5341912634d4a5e.
def localCycle00189 : Cycle where
  length := 12
  data := {
    node := ![.theta 2, .zero, .theta 4, .distance 3 4, .distance 4 6, .distance 1 4, .distance 1 3, .distance 3 5, .distance 4 5, .distance 0 4, .distance 2 4, .distance 2 3, .theta 2]
    constant := ![0, 0, 3, -1, -1, 0, -1, 0, -1, 0, 0, -1]
    coefficient := ![0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, true, false, true, true, false] }
  origin := ![.thetaLower 2, .thetaUpper 4, .corridorUpper 3 4, .triangle 32 0, .triangle 23 0, .gapLower 1 3, .triangle 20 0, .triangle 31 1, .triangle 12 0, .triangle 6 1, .triangle 25 1, .corridorLower 2 3]

-- Cycle fingerprint f9d98cc6efcd710320f1ac47fee71d6f2345ffea9769bb159e85f8eb551d7e2d.
def localCycle00190 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 3, .distance 1 6, .distance 0 1, .theta 1, .zero, .theta 4, .distance 3 4, .distance 1 3]
    constant := ![-2, -1, -2, 0, 0, 3, -1]
    coefficient := ![0, 0, 0, 0, 1, 1, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 1 3, .triangle 4 0, .gapLower 1 0, .thetaLower 1, .thetaUpper 4, .corridorUpper 3 4, .triangle 19 0]

-- Cycle fingerprint fa7fb3d4b3df7e906a011c891d1a904ef86b73285e75c1eb5c8adf1052fa7595.
def localCycle00191 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 1 3, .distance 3 6, .distance 0 3, .distance 3 5, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, -1, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 19 0, .triangle 21 0, .triangle 11 0, .triangle 10 0, .triangle 26 0, .corridorLower 2 3, .thetaLower 2]

-- Cycle fingerprint faa80b8a59605ac5701eb8f850fafe4ee9c55d2bffea57cd3526671da5b99158.
def localCycle00192 : Cycle where
  length := 8
  data := {
    node := ![.theta 1, .zero, .theta 4, .distance 3 4, .distance 1 3, .distance 1 6, .distance 1 5, .distance 0 1, .theta 1]
    constant := ![0, 0, 3, -1, -2, 0, -1, -2]
    coefficient := ![0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, false] }
  origin := ![.thetaLower 1, .thetaUpper 4, .corridorUpper 3 4, .triangle 19 0, .gapLower 1 3, .triangle 24 1, .triangle 3 0, .gapLower 1 0]

-- Cycle fingerprint fb2d2e68d25458fea35bab3311f004694a2ecb22413953a771d339531b9e31bd.
def localCycle00193 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 1 3, .distance 3 5, .distance 0 3, .distance 3 6, .distance 2 6, .distance 4 6, .theta 4]
    constant := ![3, -1, -1, -1, -1, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 19 0, .triangle 20 0, .triangle 10 0, .triangle 11 0, .triangle 27 2, .triangle 29 1, .corridorLower 4 6]

-- Cycle fingerprint fc025a242b51ec0103af12f67cae693ba7874750b922c547daebab6046064290.
def localCycle00194 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 1 4, .distance 0 4, .distance 4 5, .distance 2 4, .distance 4 6, .distance 5 6, .theta 5, .theta 4]
    constant := ![3, 0, 0, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, false, true, false, true] }
  origin := ![.corridorUpper 3 4, .triangle 19 2, .triangle 2 2, .triangle 12 0, .triangle 28 0, .triangle 29 0, .triangle 34 1, .corridorLower 5 6, .thetaNext 4]

-- Cycle fingerprint fc34d8fdf765480a9d55d9077087f8377017ed0bd33bb84f32b5a21d00c744b7.
def localCycle00195 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 2, .distance 1 4, .distance 0 4, .distance 0 3, .distance 3 5, .distance 2 3, .theta 2, .distance 1 2]
    constant := ![-2, 0, 0, -1, -1, -1, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, true, false, false, false, false] }
  origin := ![.gapLower 1 5, .triangle 2 2, .triangle 9 1, .triangle 10 0, .triangle 26 0, .corridorLower 2 3, .corridorUpper 1 2]

-- Cycle fingerprint fc6f840cd95eb8b456ee5714e067a72a91ae9745b11ff04c7443f9a61726e7d2.
def localCycle00196 : Cycle where
  length := 8
  data := {
    node := ![.distance 3 6, .distance 3 5, .distance 2 3, .theta 2, .distance 1 2, .distance 1 4, .distance 1 3, .distance 0 3, .distance 3 6]
    constant := ![0, -1, -1, 3, -2, -2, 0, -1]
    coefficient := ![0, 0, 0, 1, 0, 0, 0, 0]
    strict := ![true, false, false, false, false, false, true, false] }
  origin := ![.triangle 33 1, .triangle 26 0, .corridorLower 2 3, .corridorUpper 1 2, .gapLower 1 5, .gapLower 1 4, .triangle 1 2, .triangle 11 0]

-- Cycle fingerprint fcc05507e86fb5fb9b00bd5a0ed2838ac217d9ecd50995938b680fa8892688ec.
def localCycle00197 : Cycle where
  length := 8
  data := {
    node := ![.distance 1 3, .distance 3 5, .distance 2 3, .theta 2, .theta 1, .distance 1 2, .distance 1 4, .distance 1 6, .distance 1 3]
    constant := ![-1, -1, -1, 0, 2, 0, -2, 0]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, true, false, true, false, true] }
  origin := ![.triangle 20 0, .triangle 26 0, .corridorLower 2 3, .thetaNext 1, .gapLower 1 6, .triangle 16 2, .gapLower 1 4, .triangle 21 1]

-- Cycle fingerprint fd230dfed9510385af7cbea56e1ccff3e49576fbb5fdffd37448285663315c4c.
def localCycle00198 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 3 4, .distance 1 3, .distance 3 5, .distance 2 5, .distance 5 6, .distance 4 5, .theta 4]
    constant := ![3, -1, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 19 0, .triangle 20 0, .triangle 26 2, .triangle 30 0, .triangle 34 0, .corridorLower 4 5]

-- Cycle fingerprint fe3efefc404c86886680f9dbe12a24353a5d408c01ba9f192488067612de522a.
def localCycle00199 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 3 4, .distance 1 3, .distance 3 5, .distance 5 6, .distance 4 5, .distance 2 4, .theta 4]
    constant := ![3, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 19 0, .triangle 20 0, .triangle 33 0, .triangle 34 0, .triangle 28 0, .gapLower 4 0]

def library : Library := fun id => if id < 100 then (if id < 50 then (if id < 25 then (if id < 12 then (if id < 6 then (if id < 3 then (if id < 1 then (if id = 0 then some localCycle00000 else none) else (if id < 2 then (if id = 1 then some localCycle00001 else none) else (if id = 2 then some localCycle00002 else none))) else (if id < 4 then (if id = 3 then some localCycle00003 else none) else (if id < 5 then (if id = 4 then some localCycle00004 else none) else (if id = 5 then some localCycle00005 else none)))) else (if id < 9 then (if id < 7 then (if id = 6 then some localCycle00006 else none) else (if id < 8 then (if id = 7 then some localCycle00007 else none) else (if id = 8 then some localCycle00008 else none))) else (if id < 10 then (if id = 9 then some localCycle00009 else none) else (if id < 11 then (if id = 10 then some localCycle00010 else none) else (if id = 11 then some localCycle00011 else none))))) else (if id < 18 then (if id < 15 then (if id < 13 then (if id = 12 then some localCycle00012 else none) else (if id < 14 then (if id = 13 then some localCycle00013 else none) else (if id = 14 then some localCycle00014 else none))) else (if id < 16 then (if id = 15 then some localCycle00015 else none) else (if id < 17 then (if id = 16 then some localCycle00016 else none) else (if id = 17 then some localCycle00017 else none)))) else (if id < 21 then (if id < 19 then (if id = 18 then some localCycle00018 else none) else (if id < 20 then (if id = 19 then some localCycle00019 else none) else (if id = 20 then some localCycle00020 else none))) else (if id < 23 then (if id < 22 then (if id = 21 then some localCycle00021 else none) else (if id = 22 then some localCycle00022 else none)) else (if id < 24 then (if id = 23 then some localCycle00023 else none) else (if id = 24 then some localCycle00024 else none)))))) else (if id < 37 then (if id < 31 then (if id < 28 then (if id < 26 then (if id = 25 then some localCycle00025 else none) else (if id < 27 then (if id = 26 then some localCycle00026 else none) else (if id = 27 then some localCycle00027 else none))) else (if id < 29 then (if id = 28 then some localCycle00028 else none) else (if id < 30 then (if id = 29 then some localCycle00029 else none) else (if id = 30 then some localCycle00030 else none)))) else (if id < 34 then (if id < 32 then (if id = 31 then some localCycle00031 else none) else (if id < 33 then (if id = 32 then some localCycle00032 else none) else (if id = 33 then some localCycle00033 else none))) else (if id < 35 then (if id = 34 then some localCycle00034 else none) else (if id < 36 then (if id = 35 then some localCycle00035 else none) else (if id = 36 then some localCycle00036 else none))))) else (if id < 43 then (if id < 40 then (if id < 38 then (if id = 37 then some localCycle00037 else none) else (if id < 39 then (if id = 38 then some localCycle00038 else none) else (if id = 39 then some localCycle00039 else none))) else (if id < 41 then (if id = 40 then some localCycle00040 else none) else (if id < 42 then (if id = 41 then some localCycle00041 else none) else (if id = 42 then some localCycle00042 else none)))) else (if id < 46 then (if id < 44 then (if id = 43 then some localCycle00043 else none) else (if id < 45 then (if id = 44 then some localCycle00044 else none) else (if id = 45 then some localCycle00045 else none))) else (if id < 48 then (if id < 47 then (if id = 46 then some localCycle00046 else none) else (if id = 47 then some localCycle00047 else none)) else (if id < 49 then (if id = 48 then some localCycle00048 else none) else (if id = 49 then some localCycle00049 else none))))))) else (if id < 75 then (if id < 62 then (if id < 56 then (if id < 53 then (if id < 51 then (if id = 50 then some localCycle00050 else none) else (if id < 52 then (if id = 51 then some localCycle00051 else none) else (if id = 52 then some localCycle00052 else none))) else (if id < 54 then (if id = 53 then some localCycle00053 else none) else (if id < 55 then (if id = 54 then some localCycle00054 else none) else (if id = 55 then some localCycle00055 else none)))) else (if id < 59 then (if id < 57 then (if id = 56 then some localCycle00056 else none) else (if id < 58 then (if id = 57 then some localCycle00057 else none) else (if id = 58 then some localCycle00058 else none))) else (if id < 60 then (if id = 59 then some localCycle00059 else none) else (if id < 61 then (if id = 60 then some localCycle00060 else none) else (if id = 61 then some localCycle00061 else none))))) else (if id < 68 then (if id < 65 then (if id < 63 then (if id = 62 then some localCycle00062 else none) else (if id < 64 then (if id = 63 then some localCycle00063 else none) else (if id = 64 then some localCycle00064 else none))) else (if id < 66 then (if id = 65 then some localCycle00065 else none) else (if id < 67 then (if id = 66 then some localCycle00066 else none) else (if id = 67 then some localCycle00067 else none)))) else (if id < 71 then (if id < 69 then (if id = 68 then some localCycle00068 else none) else (if id < 70 then (if id = 69 then some localCycle00069 else none) else (if id = 70 then some localCycle00070 else none))) else (if id < 73 then (if id < 72 then (if id = 71 then some localCycle00071 else none) else (if id = 72 then some localCycle00072 else none)) else (if id < 74 then (if id = 73 then some localCycle00073 else none) else (if id = 74 then some localCycle00074 else none)))))) else (if id < 87 then (if id < 81 then (if id < 78 then (if id < 76 then (if id = 75 then some localCycle00075 else none) else (if id < 77 then (if id = 76 then some localCycle00076 else none) else (if id = 77 then some localCycle00077 else none))) else (if id < 79 then (if id = 78 then some localCycle00078 else none) else (if id < 80 then (if id = 79 then some localCycle00079 else none) else (if id = 80 then some localCycle00080 else none)))) else (if id < 84 then (if id < 82 then (if id = 81 then some localCycle00081 else none) else (if id < 83 then (if id = 82 then some localCycle00082 else none) else (if id = 83 then some localCycle00083 else none))) else (if id < 85 then (if id = 84 then some localCycle00084 else none) else (if id < 86 then (if id = 85 then some localCycle00085 else none) else (if id = 86 then some localCycle00086 else none))))) else (if id < 93 then (if id < 90 then (if id < 88 then (if id = 87 then some localCycle00087 else none) else (if id < 89 then (if id = 88 then some localCycle00088 else none) else (if id = 89 then some localCycle00089 else none))) else (if id < 91 then (if id = 90 then some localCycle00090 else none) else (if id < 92 then (if id = 91 then some localCycle00091 else none) else (if id = 92 then some localCycle00092 else none)))) else (if id < 96 then (if id < 94 then (if id = 93 then some localCycle00093 else none) else (if id < 95 then (if id = 94 then some localCycle00094 else none) else (if id = 95 then some localCycle00095 else none))) else (if id < 98 then (if id < 97 then (if id = 96 then some localCycle00096 else none) else (if id = 97 then some localCycle00097 else none)) else (if id < 99 then (if id = 98 then some localCycle00098 else none) else (if id = 99 then some localCycle00099 else none)))))))) else (if id < 150 then (if id < 125 then (if id < 112 then (if id < 106 then (if id < 103 then (if id < 101 then (if id = 100 then some localCycle00100 else none) else (if id < 102 then (if id = 101 then some localCycle00101 else none) else (if id = 102 then some localCycle00102 else none))) else (if id < 104 then (if id = 103 then some localCycle00103 else none) else (if id < 105 then (if id = 104 then some localCycle00104 else none) else (if id = 105 then some localCycle00105 else none)))) else (if id < 109 then (if id < 107 then (if id = 106 then some localCycle00106 else none) else (if id < 108 then (if id = 107 then some localCycle00107 else none) else (if id = 108 then some localCycle00108 else none))) else (if id < 110 then (if id = 109 then some localCycle00109 else none) else (if id < 111 then (if id = 110 then some localCycle00110 else none) else (if id = 111 then some localCycle00111 else none))))) else (if id < 118 then (if id < 115 then (if id < 113 then (if id = 112 then some localCycle00112 else none) else (if id < 114 then (if id = 113 then some localCycle00113 else none) else (if id = 114 then some localCycle00114 else none))) else (if id < 116 then (if id = 115 then some localCycle00115 else none) else (if id < 117 then (if id = 116 then some localCycle00116 else none) else (if id = 117 then some localCycle00117 else none)))) else (if id < 121 then (if id < 119 then (if id = 118 then some localCycle00118 else none) else (if id < 120 then (if id = 119 then some localCycle00119 else none) else (if id = 120 then some localCycle00120 else none))) else (if id < 123 then (if id < 122 then (if id = 121 then some localCycle00121 else none) else (if id = 122 then some localCycle00122 else none)) else (if id < 124 then (if id = 123 then some localCycle00123 else none) else (if id = 124 then some localCycle00124 else none)))))) else (if id < 137 then (if id < 131 then (if id < 128 then (if id < 126 then (if id = 125 then some localCycle00125 else none) else (if id < 127 then (if id = 126 then some localCycle00126 else none) else (if id = 127 then some localCycle00127 else none))) else (if id < 129 then (if id = 128 then some localCycle00128 else none) else (if id < 130 then (if id = 129 then some localCycle00129 else none) else (if id = 130 then some localCycle00130 else none)))) else (if id < 134 then (if id < 132 then (if id = 131 then some localCycle00131 else none) else (if id < 133 then (if id = 132 then some localCycle00132 else none) else (if id = 133 then some localCycle00133 else none))) else (if id < 135 then (if id = 134 then some localCycle00134 else none) else (if id < 136 then (if id = 135 then some localCycle00135 else none) else (if id = 136 then some localCycle00136 else none))))) else (if id < 143 then (if id < 140 then (if id < 138 then (if id = 137 then some localCycle00137 else none) else (if id < 139 then (if id = 138 then some localCycle00138 else none) else (if id = 139 then some localCycle00139 else none))) else (if id < 141 then (if id = 140 then some localCycle00140 else none) else (if id < 142 then (if id = 141 then some localCycle00141 else none) else (if id = 142 then some localCycle00142 else none)))) else (if id < 146 then (if id < 144 then (if id = 143 then some localCycle00143 else none) else (if id < 145 then (if id = 144 then some localCycle00144 else none) else (if id = 145 then some localCycle00145 else none))) else (if id < 148 then (if id < 147 then (if id = 146 then some localCycle00146 else none) else (if id = 147 then some localCycle00147 else none)) else (if id < 149 then (if id = 148 then some localCycle00148 else none) else (if id = 149 then some localCycle00149 else none))))))) else (if id < 175 then (if id < 162 then (if id < 156 then (if id < 153 then (if id < 151 then (if id = 150 then some localCycle00150 else none) else (if id < 152 then (if id = 151 then some localCycle00151 else none) else (if id = 152 then some localCycle00152 else none))) else (if id < 154 then (if id = 153 then some localCycle00153 else none) else (if id < 155 then (if id = 154 then some localCycle00154 else none) else (if id = 155 then some localCycle00155 else none)))) else (if id < 159 then (if id < 157 then (if id = 156 then some localCycle00156 else none) else (if id < 158 then (if id = 157 then some localCycle00157 else none) else (if id = 158 then some localCycle00158 else none))) else (if id < 160 then (if id = 159 then some localCycle00159 else none) else (if id < 161 then (if id = 160 then some localCycle00160 else none) else (if id = 161 then some localCycle00161 else none))))) else (if id < 168 then (if id < 165 then (if id < 163 then (if id = 162 then some localCycle00162 else none) else (if id < 164 then (if id = 163 then some localCycle00163 else none) else (if id = 164 then some localCycle00164 else none))) else (if id < 166 then (if id = 165 then some localCycle00165 else none) else (if id < 167 then (if id = 166 then some localCycle00166 else none) else (if id = 167 then some localCycle00167 else none)))) else (if id < 171 then (if id < 169 then (if id = 168 then some localCycle00168 else none) else (if id < 170 then (if id = 169 then some localCycle00169 else none) else (if id = 170 then some localCycle00170 else none))) else (if id < 173 then (if id < 172 then (if id = 171 then some localCycle00171 else none) else (if id = 172 then some localCycle00172 else none)) else (if id < 174 then (if id = 173 then some localCycle00173 else none) else (if id = 174 then some localCycle00174 else none)))))) else (if id < 187 then (if id < 181 then (if id < 178 then (if id < 176 then (if id = 175 then some localCycle00175 else none) else (if id < 177 then (if id = 176 then some localCycle00176 else none) else (if id = 177 then some localCycle00177 else none))) else (if id < 179 then (if id = 178 then some localCycle00178 else none) else (if id < 180 then (if id = 179 then some localCycle00179 else none) else (if id = 180 then some localCycle00180 else none)))) else (if id < 184 then (if id < 182 then (if id = 181 then some localCycle00181 else none) else (if id < 183 then (if id = 182 then some localCycle00182 else none) else (if id = 183 then some localCycle00183 else none))) else (if id < 185 then (if id = 184 then some localCycle00184 else none) else (if id < 186 then (if id = 185 then some localCycle00185 else none) else (if id = 186 then some localCycle00186 else none))))) else (if id < 193 then (if id < 190 then (if id < 188 then (if id = 187 then some localCycle00187 else none) else (if id < 189 then (if id = 188 then some localCycle00188 else none) else (if id = 189 then some localCycle00189 else none))) else (if id < 191 then (if id = 190 then some localCycle00190 else none) else (if id < 192 then (if id = 191 then some localCycle00191 else none) else (if id = 192 then some localCycle00192 else none)))) else (if id < 196 then (if id < 194 then (if id = 193 then some localCycle00193 else none) else (if id < 195 then (if id = 194 then some localCycle00194 else none) else (if id = 195 then some localCycle00195 else none))) else (if id < 198 then (if id < 197 then (if id = 196 then some localCycle00196 else none) else (if id = 197 then some localCycle00197 else none)) else (if id < 199 then (if id = 198 then some localCycle00198 else none) else (if id = 199 then some localCycle00199 else none))))))))

def namedLeaf000 : LeafData := { rows := ![![1, 6, 3, 4, 5, 2], ![0, 6, 3, 5, 4, 2], ![3, 4, 6, 5, 0, 1], ![2, 6, 0, 1, 5, 4], ![2, 6, 0, 5, 1, 3], ![6, 2, 0, 4, 1, 3], ![5, 2, 4, 3, 0, 1]], proof := .tail 129 }

theorem namedLeaf000_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6144)) namedLeaf000 = true :=
  by decide +kernel

def namedLeaf001 : LeafData := { rows := ![![1, 6, 3, 5, 4, 2], ![0, 6, 3, 5, 4, 2], ![3, 4, 6, 5, 0, 1], ![2, 6, 0, 1, 5, 4], ![2, 6, 5, 0, 1, 3], ![6, 2, 4, 0, 1, 3], ![5, 2, 4, 3, 0, 1]], proof := .tail 38 }

theorem namedLeaf001_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6145)) namedLeaf001 = true :=
  by decide +kernel

def namedLeaf002 : LeafData := { rows := ![![1, 6, 3, 5, 4, 2], ![0, 6, 3, 5, 4, 2], ![3, 5, 6, 4, 0, 1], ![2, 6, 0, 1, 5, 4], ![5, 6, 2, 0, 1, 3], ![4, 2, 6, 0, 1, 3], ![4, 2, 5, 3, 0, 1]], proof := .tail 175 }

theorem namedLeaf002_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6146)) namedLeaf002 = true :=
  by decide +kernel

def namedLeaf003 : LeafData := { rows := ![![1, 6, 3, 4, 5, 2], ![0, 6, 3, 4, 5, 2], ![3, 6, 4, 5, 0, 1], ![2, 6, 0, 1, 4, 5], ![6, 2, 0, 1, 3, 5], ![6, 2, 0, 1, 3, 4], ![5, 4, 2, 3, 0, 1]], proof := .tail 118 }

theorem namedLeaf003_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6147)) namedLeaf003 = true :=
  by decide +kernel

def namedLeaf004 : LeafData := { rows := ![![1, 6, 3, 4, 5, 2], ![0, 6, 3, 4, 5, 2], ![3, 6, 4, 5, 0, 1], ![2, 6, 0, 1, 5, 4], ![6, 2, 0, 1, 5, 3], ![6, 2, 0, 1, 4, 3], ![5, 4, 2, 3, 0, 1]], proof := .tail 36 }

theorem namedLeaf004_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6148)) namedLeaf004 = true :=
  by decide +kernel

def namedLeaf005 : LeafData := { rows := ![![1, 6, 3, 4, 5, 2], ![0, 6, 3, 5, 4, 2], ![3, 6, 4, 5, 0, 1], ![2, 6, 0, 1, 5, 4], ![6, 2, 0, 5, 1, 3], ![6, 2, 0, 4, 1, 3], ![5, 4, 2, 3, 0, 1]], proof := .tail 1 }

theorem namedLeaf005_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6149)) namedLeaf005 = true :=
  by decide +kernel

def namedLeaf006 : LeafData := { rows := ![![1, 6, 3, 5, 4, 2], ![0, 6, 3, 5, 4, 2], ![3, 6, 4, 5, 0, 1], ![2, 6, 0, 1, 5, 4], ![6, 2, 5, 0, 1, 3], ![6, 2, 4, 0, 1, 3], ![5, 4, 2, 3, 0, 1]], proof := .tail 194 }

theorem namedLeaf006_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6150)) namedLeaf006 = true :=
  by decide +kernel

def namedLeaf007 : LeafData := { rows := ![![1, 6, 3, 5, 4, 2], ![0, 6, 3, 5, 4, 2], ![3, 6, 5, 4, 0, 1], ![2, 6, 0, 1, 5, 4], ![5, 6, 2, 0, 1, 3], ![4, 6, 2, 0, 1, 3], ![4, 5, 2, 3, 0, 1]], proof := .tail 147 }

theorem namedLeaf007_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6151)) namedLeaf007 = true :=
  by decide +kernel

def namedLeaf008 : LeafData := { rows := ![![1, 6, 3, 5, 4, 2], ![0, 6, 3, 5, 4, 2], ![3, 6, 5, 4, 0, 1], ![2, 6, 0, 1, 5, 4], ![6, 5, 2, 0, 1, 3], ![6, 4, 2, 0, 1, 3], ![5, 4, 2, 3, 0, 1]], proof := .tail 171 }

theorem namedLeaf008_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6152)) namedLeaf008 = true :=
  by decide +kernel

def namedLeaf009 : LeafData := { rows := ![![1, 6, 3, 4, 5, 2], ![0, 6, 3, 4, 5, 2], ![6, 3, 4, 5, 0, 1], ![6, 2, 0, 1, 4, 5], ![6, 2, 0, 1, 3, 5], ![6, 2, 0, 1, 3, 4], ![5, 4, 3, 2, 0, 1]], proof := .tail 160 }

theorem namedLeaf009_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6153)) namedLeaf009 = true :=
  by decide +kernel

def namedLeaf010 : LeafData := { rows := ![![1, 6, 3, 4, 5, 2], ![0, 6, 3, 4, 5, 2], ![6, 3, 4, 5, 0, 1], ![6, 2, 0, 1, 5, 4], ![6, 2, 0, 1, 5, 3], ![6, 2, 0, 1, 4, 3], ![5, 4, 3, 2, 0, 1]], proof := .tail 99 }

theorem namedLeaf010_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6154)) namedLeaf010 = true :=
  by decide +kernel

def namedLeaf011 : LeafData := { rows := ![![1, 6, 3, 4, 5, 2], ![0, 6, 3, 5, 4, 2], ![6, 3, 4, 5, 0, 1], ![6, 2, 0, 1, 5, 4], ![6, 2, 0, 5, 1, 3], ![6, 2, 0, 4, 1, 3], ![5, 4, 3, 2, 0, 1]], proof := .tail 64 }

theorem namedLeaf011_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6155)) namedLeaf011 = true :=
  by decide +kernel

def namedLeaf012 : LeafData := { rows := ![![1, 6, 3, 5, 4, 2], ![0, 6, 3, 5, 4, 2], ![6, 3, 4, 5, 0, 1], ![6, 2, 0, 1, 5, 4], ![6, 2, 5, 0, 1, 3], ![6, 2, 4, 0, 1, 3], ![5, 4, 3, 2, 0, 1]], proof := .tail 194 }

theorem namedLeaf012_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6156)) namedLeaf012 = true :=
  by decide +kernel

def namedLeaf013 : LeafData := { rows := ![![1, 6, 3, 5, 4, 2], ![0, 6, 3, 5, 4, 2], ![6, 3, 5, 4, 0, 1], ![6, 2, 0, 1, 5, 4], ![5, 6, 2, 0, 1, 3], ![4, 6, 2, 0, 1, 3], ![4, 5, 3, 2, 0, 1]], proof := .tail 175 }

theorem namedLeaf013_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6157)) namedLeaf013 = true :=
  by decide +kernel

def namedLeaf014 : LeafData := { rows := ![![1, 6, 3, 5, 4, 2], ![0, 6, 3, 5, 4, 2], ![6, 3, 5, 4, 0, 1], ![6, 2, 0, 1, 5, 4], ![6, 5, 2, 0, 1, 3], ![6, 4, 2, 0, 1, 3], ![5, 4, 3, 2, 0, 1]], proof := .tail 89 }

theorem namedLeaf014_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6158)) namedLeaf014 = true :=
  by decide +kernel

def namedLeaf015 : LeafData := { rows := ![![1, 3, 4, 5, 6, 2], ![0, 5, 3, 4, 6, 2], ![3, 4, 5, 6, 0, 1], ![2, 0, 5, 1, 4, 6], ![2, 0, 5, 1, 3, 6], ![2, 0, 4, 3, 1, 6], ![2, 0, 1, 3, 4, 5]], proof := .tail 81 }

theorem namedLeaf015_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6159)) namedLeaf015 = true :=
  by decide +kernel

def namedLeaf016 : LeafData := { rows := ![![1, 3, 4, 5, 6, 2], ![0, 5, 3, 4, 6, 2], ![3, 4, 5, 6, 0, 1], ![2, 0, 5, 1, 6, 4], ![2, 0, 5, 1, 6, 3], ![2, 0, 4, 3, 1, 6], ![2, 0, 1, 4, 3, 5]], proof := .tail 189 }

theorem namedLeaf016_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6160)) namedLeaf016 = true :=
  by decide +kernel

def namedLeaf017 : LeafData := { rows := ![![1, 3, 4, 5, 6, 2], ![0, 5, 3, 6, 4, 2], ![3, 4, 5, 6, 0, 1], ![2, 0, 5, 1, 6, 4], ![2, 0, 5, 6, 1, 3], ![2, 0, 4, 3, 1, 6], ![2, 0, 4, 1, 3, 5]], proof := .low (![9, 52, 107, 4, 83, 2, 25, 163, 117, 30, 60, 41, 78, 122, 30, 183, 166, 105, 44, 115, 18, 122, 108, 137, 7, 82, 197, 148]) }

theorem namedLeaf017_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6161)) namedLeaf017 = true :=
  by decide +kernel

def namedLeaf018 : LeafData := { rows := ![![1, 3, 4, 5, 6, 2], ![0, 5, 6, 3, 4, 2], ![3, 4, 5, 6, 0, 1], ![2, 0, 5, 6, 1, 4], ![2, 0, 5, 6, 1, 3], ![2, 0, 4, 3, 1, 6], ![2, 0, 4, 3, 1, 5]], proof := .low (![134, 12, 68, 55, 119, 75, 111, 140, 76, 190, 123, 113, 78, 149, 187, 123, 31, 14, 20, 123, 23, 135, 123, 110, 28, 79, 123, 139]) }

theorem namedLeaf018_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6162)) namedLeaf018 = true :=
  by decide +kernel

def namedLeaf019 : LeafData := { rows := ![![1, 3, 4, 5, 6, 2], ![0, 6, 5, 3, 4, 2], ![3, 4, 5, 6, 0, 1], ![2, 0, 5, 6, 1, 4], ![2, 0, 5, 6, 1, 3], ![2, 0, 4, 3, 6, 1], ![2, 0, 4, 3, 5, 1]], proof := .tail 32 }

theorem namedLeaf019_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6163)) namedLeaf019 = true :=
  by decide +kernel

def namedLeaf020 : LeafData := { rows := ![![1, 3, 4, 5, 6, 2], ![0, 6, 5, 3, 4, 2], ![3, 4, 5, 6, 0, 1], ![2, 0, 6, 5, 1, 4], ![2, 0, 5, 6, 1, 3], ![2, 0, 4, 6, 3, 1], ![2, 0, 4, 5, 3, 1]], proof := .tail 40 }

theorem namedLeaf020_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6164)) namedLeaf020 = true :=
  by decide +kernel

def namedLeaf021 : LeafData := { rows := ![![1, 3, 4, 5, 6, 2], ![0, 6, 5, 3, 4, 2], ![3, 4, 5, 6, 0, 1], ![2, 0, 6, 5, 1, 4], ![2, 0, 6, 5, 1, 3], ![2, 0, 6, 4, 3, 1], ![2, 0, 5, 4, 3, 1]], proof := .tail 57 }

theorem namedLeaf021_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6165)) namedLeaf021 = true :=
  by decide +kernel

def namedLeaf022 : LeafData := { rows := ![![1, 3, 4, 6, 5, 2], ![0, 6, 5, 3, 4, 2], ![3, 4, 5, 6, 0, 1], ![2, 0, 6, 5, 1, 4], ![2, 0, 6, 5, 1, 3], ![2, 6, 0, 4, 3, 1], ![2, 5, 0, 4, 3, 1]], proof := .tail 57 }

theorem namedLeaf022_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6166)) namedLeaf022 = true :=
  by decide +kernel

def namedLeaf023 : LeafData := { rows := ![![1, 3, 4, 6, 5, 2], ![0, 6, 5, 3, 4, 2], ![3, 4, 6, 5, 0, 1], ![2, 0, 6, 5, 1, 4], ![2, 0, 6, 5, 1, 3], ![6, 2, 0, 4, 3, 1], ![5, 2, 0, 4, 3, 1]], proof := .tail 161 }

theorem namedLeaf023_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6167)) namedLeaf023 = true :=
  by decide +kernel

def namedLeaf024 : LeafData := { rows := ![![1, 3, 6, 4, 5, 2], ![0, 6, 5, 3, 4, 2], ![3, 4, 5, 6, 0, 1], ![2, 0, 6, 5, 1, 4], ![2, 6, 0, 5, 1, 3], ![2, 6, 0, 4, 3, 1], ![2, 5, 4, 0, 3, 1]], proof := .tail 172 }

theorem namedLeaf024_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6168)) namedLeaf024 = true :=
  by decide +kernel

def namedLeaf025 : LeafData := { rows := ![![1, 3, 6, 4, 5, 2], ![0, 6, 5, 3, 4, 2], ![3, 4, 6, 5, 0, 1], ![2, 0, 6, 5, 1, 4], ![2, 6, 0, 5, 1, 3], ![6, 2, 0, 4, 3, 1], ![5, 2, 4, 0, 3, 1]], proof := .tail 172 }

theorem namedLeaf025_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6169)) namedLeaf025 = true :=
  by decide +kernel

def namedLeaf026 : LeafData := { rows := ![![1, 3, 6, 4, 5, 2], ![0, 6, 5, 3, 4, 2], ![3, 6, 4, 5, 0, 1], ![2, 0, 6, 5, 1, 4], ![6, 2, 0, 5, 1, 3], ![6, 2, 0, 4, 3, 1], ![5, 4, 2, 0, 3, 1]], proof := .tail 13 }

theorem namedLeaf026_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6170)) namedLeaf026 = true :=
  by decide +kernel

def namedLeaf027 : LeafData := { rows := ![![1, 6, 3, 4, 5, 2], ![0, 6, 5, 3, 4, 2], ![3, 4, 5, 6, 0, 1], ![2, 6, 0, 5, 1, 4], ![2, 6, 0, 5, 1, 3], ![2, 6, 0, 4, 3, 1], ![2, 5, 4, 3, 0, 1]], proof := .tail 172 }

theorem namedLeaf027_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6171)) namedLeaf027 = true :=
  by decide +kernel

def namedLeaf028 : LeafData := { rows := ![![1, 6, 3, 4, 5, 2], ![0, 6, 5, 3, 4, 2], ![3, 4, 6, 5, 0, 1], ![2, 6, 0, 5, 1, 4], ![2, 6, 0, 5, 1, 3], ![6, 2, 0, 4, 3, 1], ![5, 2, 4, 3, 0, 1]], proof := .tail 172 }

theorem namedLeaf028_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6172)) namedLeaf028 = true :=
  by decide +kernel

def namedLeaf029 : LeafData := { rows := ![![1, 6, 3, 4, 5, 2], ![0, 6, 5, 3, 4, 2], ![3, 6, 4, 5, 0, 1], ![2, 6, 0, 5, 1, 4], ![6, 2, 0, 5, 1, 3], ![6, 2, 0, 4, 3, 1], ![5, 4, 2, 3, 0, 1]], proof := .tail 43 }

theorem namedLeaf029_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6173)) namedLeaf029 = true :=
  by decide +kernel

def namedLeaf030 : LeafData := { rows := ![![1, 6, 3, 4, 5, 2], ![0, 6, 5, 3, 4, 2], ![6, 3, 4, 5, 0, 1], ![6, 2, 0, 5, 1, 4], ![6, 2, 0, 5, 1, 3], ![6, 2, 0, 4, 3, 1], ![5, 4, 3, 2, 0, 1]], proof := .tail 86 }

theorem namedLeaf030_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6174)) namedLeaf030 = true :=
  by decide +kernel

def namedLeaf031 : LeafData := { rows := ![![1, 3, 5, 4, 6, 2], ![0, 5, 3, 4, 6, 2], ![3, 4, 5, 6, 0, 1], ![2, 0, 5, 1, 4, 6], ![2, 5, 0, 1, 3, 6], ![2, 4, 0, 3, 1, 6], ![2, 0, 1, 3, 4, 5]], proof := .tail 181 }

theorem namedLeaf031_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6175)) namedLeaf031 = true :=
  by decide +kernel

def namedLeaf032 : LeafData := { rows := ![![1, 3, 5, 4, 6, 2], ![0, 5, 3, 4, 6, 2], ![3, 4, 5, 6, 0, 1], ![2, 0, 5, 1, 6, 4], ![2, 5, 0, 1, 6, 3], ![2, 4, 0, 3, 1, 6], ![2, 0, 1, 4, 3, 5]], proof := .tail 176 }

theorem namedLeaf032_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6176)) namedLeaf032 = true :=
  by decide +kernel

def namedLeaf033 : LeafData := { rows := ![![1, 3, 5, 4, 6, 2], ![0, 5, 3, 6, 4, 2], ![3, 4, 5, 6, 0, 1], ![2, 0, 5, 1, 6, 4], ![2, 5, 0, 6, 1, 3], ![2, 4, 0, 3, 1, 6], ![2, 0, 4, 1, 3, 5]], proof := .tail 138 }

theorem namedLeaf033_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6177)) namedLeaf033 = true :=
  by decide +kernel

def namedLeaf034 : LeafData := { rows := ![![1, 3, 5, 6, 4, 2], ![0, 5, 3, 6, 4, 2], ![3, 4, 5, 6, 0, 1], ![2, 0, 5, 1, 6, 4], ![2, 5, 6, 0, 1, 3], ![2, 4, 0, 3, 1, 6], ![2, 4, 0, 1, 3, 5]], proof := .low (![9, 52, 107, 4, 104, 2, 25, 163, 117, 30, 90, 41, 78, 122, 30, 183, 166, 105, 44, 101, 136, 122, 108, 137, 7, 82, 197, 148]) }

theorem namedLeaf034_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6178)) namedLeaf034 = true :=
  by decide +kernel

def namedLeaf035 : LeafData := { rows := ![![1, 3, 5, 4, 6, 2], ![0, 5, 6, 3, 4, 2], ![3, 4, 5, 6, 0, 1], ![2, 0, 5, 6, 1, 4], ![2, 5, 0, 6, 1, 3], ![2, 4, 0, 3, 1, 6], ![2, 0, 4, 3, 1, 5]], proof := .tail 182 }

theorem namedLeaf035_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6179)) namedLeaf035 = true :=
  by decide +kernel

def namedLeaf036 : LeafData := { rows := ![![1, 3, 5, 4, 6, 2], ![0, 6, 5, 3, 4, 2], ![3, 4, 5, 6, 0, 1], ![2, 0, 5, 6, 1, 4], ![2, 5, 0, 6, 1, 3], ![2, 4, 0, 3, 6, 1], ![2, 0, 4, 3, 5, 1]], proof := .tail 173 }

theorem namedLeaf036_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6180)) namedLeaf036 = true :=
  by decide +kernel

def namedLeaf037 : LeafData := { rows := ![![1, 3, 5, 4, 6, 2], ![0, 6, 5, 3, 4, 2], ![3, 4, 5, 6, 0, 1], ![2, 0, 6, 5, 1, 4], ![2, 5, 0, 6, 1, 3], ![2, 4, 0, 6, 3, 1], ![2, 0, 4, 5, 3, 1]], proof := .tail 199 }

theorem namedLeaf037_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6181)) namedLeaf037 = true :=
  by decide +kernel

def namedLeaf038 : LeafData := { rows := ![![1, 3, 5, 6, 4, 2], ![0, 5, 6, 3, 4, 2], ![3, 4, 5, 6, 0, 1], ![2, 0, 5, 6, 1, 4], ![2, 5, 6, 0, 1, 3], ![2, 4, 0, 3, 1, 6], ![2, 4, 0, 3, 1, 5]], proof := .low (![134, 12, 68, 55, 127, 75, 111, 140, 76, 190, 151, 113, 78, 102, 179, 131, 31, 14, 88, 94, 91, 11, 61, 72, 188, 153, 74, 139]) }

theorem namedLeaf038_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6182)) namedLeaf038 = true :=
  by decide +kernel

def namedLeaf039 : LeafData := { rows := ![![1, 3, 5, 6, 4, 2], ![0, 6, 5, 3, 4, 2], ![3, 4, 5, 6, 0, 1], ![2, 0, 5, 6, 1, 4], ![2, 5, 6, 0, 1, 3], ![2, 4, 0, 3, 6, 1], ![2, 4, 0, 3, 5, 1]], proof := .tail 173 }

theorem namedLeaf039_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6183)) namedLeaf039 = true :=
  by decide +kernel

def namedLeaf040 : LeafData := { rows := ![![1, 3, 5, 6, 4, 2], ![0, 6, 5, 3, 4, 2], ![3, 4, 5, 6, 0, 1], ![2, 0, 6, 5, 1, 4], ![2, 5, 6, 0, 1, 3], ![2, 4, 0, 6, 3, 1], ![2, 4, 0, 5, 3, 1]], proof := .tail 40 }

theorem namedLeaf040_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6184)) namedLeaf040 = true :=
  by decide +kernel

def namedLeaf041 : LeafData := { rows := ![![1, 3, 6, 5, 4, 2], ![0, 6, 5, 3, 4, 2], ![3, 4, 5, 6, 0, 1], ![2, 0, 6, 5, 1, 4], ![2, 5, 6, 0, 1, 3], ![2, 4, 6, 0, 3, 1], ![2, 4, 5, 0, 3, 1]], proof := .tail 40 }

theorem namedLeaf041_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6185)) namedLeaf041 = true :=
  by decide +kernel

def namedLeaf042 : LeafData := { rows := ![![1, 3, 6, 5, 4, 2], ![0, 6, 5, 3, 4, 2], ![3, 4, 5, 6, 0, 1], ![2, 0, 6, 5, 1, 4], ![2, 6, 5, 0, 1, 3], ![2, 6, 4, 0, 3, 1], ![2, 5, 4, 0, 3, 1]], proof := .tail 57 }

theorem namedLeaf042_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6186)) namedLeaf042 = true :=
  by decide +kernel

def namedLeaf043 : LeafData := { rows := ![![1, 3, 6, 5, 4, 2], ![0, 6, 5, 3, 4, 2], ![3, 4, 6, 5, 0, 1], ![2, 0, 6, 5, 1, 4], ![2, 6, 5, 0, 1, 3], ![6, 2, 4, 0, 3, 1], ![5, 2, 4, 0, 3, 1]], proof := .tail 161 }

theorem namedLeaf043_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6187)) namedLeaf043 = true :=
  by decide +kernel

def namedLeaf044 : LeafData := { rows := ![![1, 3, 6, 5, 4, 2], ![0, 6, 5, 3, 4, 2], ![3, 6, 4, 5, 0, 1], ![2, 0, 6, 5, 1, 4], ![6, 2, 5, 0, 1, 3], ![6, 2, 4, 0, 3, 1], ![5, 4, 2, 0, 3, 1]], proof := .tail 43 }

theorem namedLeaf044_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6188)) namedLeaf044 = true :=
  by decide +kernel

def namedLeaf045 : LeafData := { rows := ![![1, 6, 3, 5, 4, 2], ![0, 6, 5, 3, 4, 2], ![3, 4, 5, 6, 0, 1], ![2, 6, 0, 5, 1, 4], ![2, 5, 6, 0, 1, 3], ![2, 4, 6, 0, 3, 1], ![2, 4, 5, 3, 0, 1]], proof := .tail 155 }

theorem namedLeaf045_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6189)) namedLeaf045 = true :=
  by decide +kernel

def namedLeaf046 : LeafData := { rows := ![![1, 6, 3, 5, 4, 2], ![0, 6, 5, 3, 4, 2], ![3, 4, 5, 6, 0, 1], ![2, 6, 0, 5, 1, 4], ![2, 6, 5, 0, 1, 3], ![2, 6, 4, 0, 3, 1], ![2, 5, 4, 3, 0, 1]], proof := .tail 128 }

theorem namedLeaf046_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6190)) namedLeaf046 = true :=
  by decide +kernel

def namedLeaf047 : LeafData := { rows := ![![1, 6, 3, 5, 4, 2], ![0, 6, 5, 3, 4, 2], ![3, 4, 6, 5, 0, 1], ![2, 6, 0, 5, 1, 4], ![2, 6, 5, 0, 1, 3], ![6, 2, 4, 0, 3, 1], ![5, 2, 4, 3, 0, 1]], proof := .tail 128 }

theorem namedLeaf047_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6191)) namedLeaf047 = true :=
  by decide +kernel

def namedLeaf048 : LeafData := { rows := ![![1, 6, 3, 5, 4, 2], ![0, 6, 5, 3, 4, 2], ![3, 6, 4, 5, 0, 1], ![2, 6, 0, 5, 1, 4], ![6, 2, 5, 0, 1, 3], ![6, 2, 4, 0, 3, 1], ![5, 4, 2, 3, 0, 1]], proof := .tail 43 }

theorem namedLeaf048_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6192)) namedLeaf048 = true :=
  by decide +kernel

def namedLeaf049 : LeafData := { rows := ![![1, 6, 3, 5, 4, 2], ![0, 6, 5, 3, 4, 2], ![6, 3, 4, 5, 0, 1], ![6, 2, 0, 5, 1, 4], ![6, 2, 5, 0, 1, 3], ![6, 2, 4, 0, 3, 1], ![5, 4, 3, 2, 0, 1]], proof := .tail 86 }

theorem namedLeaf049_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6193)) namedLeaf049 = true :=
  by decide +kernel

def namedLeaf050 : LeafData := { rows := ![![1, 3, 5, 4, 6, 2], ![0, 5, 3, 4, 6, 2], ![3, 5, 4, 6, 0, 1], ![2, 0, 5, 1, 4, 6], ![5, 2, 0, 1, 3, 6], ![4, 2, 0, 3, 1, 6], ![2, 0, 1, 3, 4, 5]], proof := .tail 81 }

theorem namedLeaf050_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6194)) namedLeaf050 = true :=
  by decide +kernel

def namedLeaf051 : LeafData := { rows := ![![1, 3, 5, 4, 6, 2], ![0, 5, 3, 4, 6, 2], ![3, 5, 4, 6, 0, 1], ![2, 0, 5, 1, 6, 4], ![5, 2, 0, 1, 6, 3], ![4, 2, 0, 3, 1, 6], ![2, 0, 1, 4, 3, 5]], proof := .tail 54 }

theorem namedLeaf051_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6195)) namedLeaf051 = true :=
  by decide +kernel

def namedLeaf052 : LeafData := { rows := ![![1, 3, 5, 4, 6, 2], ![0, 5, 3, 6, 4, 2], ![3, 5, 4, 6, 0, 1], ![2, 0, 5, 1, 6, 4], ![5, 2, 0, 6, 1, 3], ![4, 2, 0, 3, 1, 6], ![2, 0, 4, 1, 3, 5]], proof := .tail 62 }

theorem namedLeaf052_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6196)) namedLeaf052 = true :=
  by decide +kernel

def namedLeaf053 : LeafData := { rows := ![![1, 3, 5, 6, 4, 2], ![0, 5, 3, 6, 4, 2], ![3, 5, 4, 6, 0, 1], ![2, 0, 5, 1, 6, 4], ![5, 2, 6, 0, 1, 3], ![4, 2, 0, 3, 1, 6], ![2, 4, 0, 1, 3, 5]], proof := .tail 85 }

theorem namedLeaf053_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6197)) namedLeaf053 = true :=
  by decide +kernel

def namedLeaf054 : LeafData := { rows := ![![1, 3, 5, 6, 4, 2], ![0, 5, 3, 6, 4, 2], ![3, 5, 6, 4, 0, 1], ![2, 0, 5, 1, 6, 4], ![5, 6, 2, 0, 1, 3], ![4, 2, 0, 3, 1, 6], ![4, 2, 0, 1, 3, 5]], proof := .low (![9, 52, 107, 4, 104, 2, 25, 163, 117, 30, 90, 41, 78, 122, 30, 183, 166, 143, 44, 115, 18, 122, 108, 137, 7, 82, 197, 148]) }

theorem namedLeaf054_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6198)) namedLeaf054 = true :=
  by decide +kernel

def namedLeaf055 : LeafData := { rows := ![![1, 3, 5, 4, 6, 2], ![0, 5, 6, 3, 4, 2], ![3, 5, 4, 6, 0, 1], ![2, 0, 5, 6, 1, 4], ![5, 2, 0, 6, 1, 3], ![4, 2, 0, 3, 1, 6], ![2, 0, 4, 3, 1, 5]], proof := .tail 141 }

theorem namedLeaf055_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6199)) namedLeaf055 = true :=
  by decide +kernel

def namedLeaf056 : LeafData := { rows := ![![1, 3, 5, 4, 6, 2], ![0, 6, 5, 3, 4, 2], ![3, 5, 4, 6, 0, 1], ![2, 0, 5, 6, 1, 4], ![5, 2, 0, 6, 1, 3], ![4, 2, 0, 3, 6, 1], ![2, 0, 4, 3, 5, 1]], proof := .tail 16 }

theorem namedLeaf056_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6200)) namedLeaf056 = true :=
  by decide +kernel

def namedLeaf057 : LeafData := { rows := ![![1, 3, 5, 4, 6, 2], ![0, 6, 5, 3, 4, 2], ![3, 5, 4, 6, 0, 1], ![2, 0, 6, 5, 1, 4], ![5, 2, 0, 6, 1, 3], ![4, 2, 0, 6, 3, 1], ![2, 0, 4, 5, 3, 1]], proof := .tail 40 }

theorem namedLeaf057_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6201)) namedLeaf057 = true :=
  by decide +kernel

def namedLeaf058 : LeafData := { rows := ![![1, 3, 5, 6, 4, 2], ![0, 5, 6, 3, 4, 2], ![3, 5, 4, 6, 0, 1], ![2, 0, 5, 6, 1, 4], ![5, 2, 6, 0, 1, 3], ![4, 2, 0, 3, 1, 6], ![2, 4, 0, 3, 1, 5]], proof := .tail 141 }

theorem namedLeaf058_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6202)) namedLeaf058 = true :=
  by decide +kernel

def namedLeaf059 : LeafData := { rows := ![![1, 3, 5, 6, 4, 2], ![0, 6, 5, 3, 4, 2], ![3, 5, 4, 6, 0, 1], ![2, 0, 5, 6, 1, 4], ![5, 2, 6, 0, 1, 3], ![4, 2, 0, 3, 6, 1], ![2, 4, 0, 3, 5, 1]], proof := .tail 16 }

theorem namedLeaf059_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6203)) namedLeaf059 = true :=
  by decide +kernel

def namedLeaf060 : LeafData := { rows := ![![1, 3, 5, 6, 4, 2], ![0, 6, 5, 3, 4, 2], ![3, 5, 4, 6, 0, 1], ![2, 0, 6, 5, 1, 4], ![5, 2, 6, 0, 1, 3], ![4, 2, 0, 6, 3, 1], ![2, 4, 0, 5, 3, 1]], proof := .tail 40 }

theorem namedLeaf060_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6204)) namedLeaf060 = true :=
  by decide +kernel

def namedLeaf061 : LeafData := { rows := ![![1, 3, 6, 5, 4, 2], ![0, 6, 5, 3, 4, 2], ![3, 5, 4, 6, 0, 1], ![2, 0, 6, 5, 1, 4], ![5, 2, 6, 0, 1, 3], ![4, 2, 6, 0, 3, 1], ![2, 4, 5, 0, 3, 1]], proof := .tail 40 }

theorem namedLeaf061_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6205)) namedLeaf061 = true :=
  by decide +kernel

def namedLeaf062 : LeafData := { rows := ![![1, 3, 5, 6, 4, 2], ![0, 5, 6, 3, 4, 2], ![3, 5, 6, 4, 0, 1], ![2, 0, 5, 6, 1, 4], ![5, 6, 2, 0, 1, 3], ![4, 2, 0, 3, 1, 6], ![4, 2, 0, 3, 1, 5]], proof := .low (![134, 12, 68, 55, 127, 75, 111, 140, 76, 190, 151, 113, 78, 150, 34, 131, 31, 165, 142, 0, 23, 135, 156, 110, 28, 153, 74, 139]) }

theorem namedLeaf062_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6206)) namedLeaf062 = true :=
  by decide +kernel

def namedLeaf063 : LeafData := { rows := ![![1, 3, 5, 6, 4, 2], ![0, 6, 5, 3, 4, 2], ![3, 5, 6, 4, 0, 1], ![2, 0, 5, 6, 1, 4], ![5, 6, 2, 0, 1, 3], ![4, 2, 0, 3, 6, 1], ![4, 2, 0, 3, 5, 1]], proof := .tail 32 }

theorem namedLeaf063_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6207)) namedLeaf063 = true :=
  by decide +kernel

def namedLeaf064 : LeafData := { rows := ![![1, 3, 5, 6, 4, 2], ![0, 6, 5, 3, 4, 2], ![3, 5, 6, 4, 0, 1], ![2, 0, 6, 5, 1, 4], ![5, 6, 2, 0, 1, 3], ![4, 2, 0, 6, 3, 1], ![4, 2, 0, 5, 3, 1]], proof := .tail 40 }

theorem namedLeaf064_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6208)) namedLeaf064 = true :=
  by decide +kernel

def namedLeaf065 : LeafData := { rows := ![![1, 3, 6, 5, 4, 2], ![0, 6, 5, 3, 4, 2], ![3, 5, 6, 4, 0, 1], ![2, 0, 6, 5, 1, 4], ![5, 6, 2, 0, 1, 3], ![4, 2, 6, 0, 3, 1], ![4, 2, 5, 0, 3, 1]], proof := .tail 40 }

theorem namedLeaf065_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6209)) namedLeaf065 = true :=
  by decide +kernel

def namedLeaf066 : LeafData := { rows := ![![1, 3, 6, 5, 4, 2], ![0, 6, 5, 3, 4, 2], ![3, 6, 5, 4, 0, 1], ![2, 0, 6, 5, 1, 4], ![5, 6, 2, 0, 1, 3], ![4, 6, 2, 0, 3, 1], ![4, 5, 2, 0, 3, 1]], proof := .tail 198 }

theorem namedLeaf066_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6210)) namedLeaf066 = true :=
  by decide +kernel

def namedLeaf067 : LeafData := { rows := ![![1, 3, 6, 5, 4, 2], ![0, 6, 5, 3, 4, 2], ![3, 6, 5, 4, 0, 1], ![2, 0, 6, 5, 1, 4], ![6, 5, 2, 0, 1, 3], ![6, 4, 2, 0, 3, 1], ![5, 4, 2, 0, 3, 1]], proof := .tail 158 }

theorem namedLeaf067_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6211)) namedLeaf067 = true :=
  by decide +kernel

def namedLeaf068 : LeafData := { rows := ![![1, 6, 3, 5, 4, 2], ![0, 6, 5, 3, 4, 2], ![3, 5, 4, 6, 0, 1], ![2, 6, 0, 5, 1, 4], ![5, 2, 6, 0, 1, 3], ![4, 2, 6, 0, 3, 1], ![2, 4, 5, 3, 0, 1]], proof := .tail 155 }

theorem namedLeaf068_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6212)) namedLeaf068 = true :=
  by decide +kernel

def namedLeaf069 : LeafData := { rows := ![![1, 6, 3, 5, 4, 2], ![0, 6, 5, 3, 4, 2], ![3, 5, 6, 4, 0, 1], ![2, 6, 0, 5, 1, 4], ![5, 6, 2, 0, 1, 3], ![4, 2, 6, 0, 3, 1], ![4, 2, 5, 3, 0, 1]], proof := .tail 155 }

theorem namedLeaf069_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6213)) namedLeaf069 = true :=
  by decide +kernel

def namedLeaf070 : LeafData := { rows := ![![1, 6, 3, 5, 4, 2], ![0, 6, 5, 3, 4, 2], ![3, 6, 5, 4, 0, 1], ![2, 6, 0, 5, 1, 4], ![5, 6, 2, 0, 1, 3], ![4, 6, 2, 0, 3, 1], ![4, 5, 2, 3, 0, 1]], proof := .tail 96 }

theorem namedLeaf070_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6214)) namedLeaf070 = true :=
  by decide +kernel

def namedLeaf071 : LeafData := { rows := ![![1, 6, 3, 5, 4, 2], ![0, 6, 5, 3, 4, 2], ![3, 6, 5, 4, 0, 1], ![2, 6, 0, 5, 1, 4], ![6, 5, 2, 0, 1, 3], ![6, 4, 2, 0, 3, 1], ![5, 4, 2, 3, 0, 1]], proof := .tail 193 }

theorem namedLeaf071_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6215)) namedLeaf071 = true :=
  by decide +kernel

def namedLeaf072 : LeafData := { rows := ![![1, 6, 3, 5, 4, 2], ![0, 6, 5, 3, 4, 2], ![6, 3, 5, 4, 0, 1], ![6, 2, 0, 5, 1, 4], ![5, 6, 2, 0, 1, 3], ![4, 6, 2, 0, 3, 1], ![4, 5, 3, 2, 0, 1]], proof := .tail 112 }

theorem namedLeaf072_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6216)) namedLeaf072 = true :=
  by decide +kernel

def namedLeaf073 : LeafData := { rows := ![![1, 6, 3, 5, 4, 2], ![0, 6, 5, 3, 4, 2], ![6, 3, 5, 4, 0, 1], ![6, 2, 0, 5, 1, 4], ![6, 5, 2, 0, 1, 3], ![6, 4, 2, 0, 3, 1], ![5, 4, 3, 2, 0, 1]], proof := .tail 86 }

theorem namedLeaf073_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6217)) namedLeaf073 = true :=
  by decide +kernel

def namedLeaf074 : LeafData := { rows := ![![1, 5, 3, 4, 6, 2], ![0, 5, 3, 4, 6, 2], ![3, 4, 5, 6, 0, 1], ![2, 5, 0, 1, 4, 6], ![2, 5, 0, 1, 3, 6], ![2, 4, 3, 0, 1, 6], ![2, 0, 1, 3, 4, 5]], proof := .tail 81 }

theorem namedLeaf074_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6218)) namedLeaf074 = true :=
  by decide +kernel

def namedLeaf075 : LeafData := { rows := ![![1, 5, 3, 4, 6, 2], ![0, 5, 3, 4, 6, 2], ![3, 4, 5, 6, 0, 1], ![2, 5, 0, 1, 6, 4], ![2, 5, 0, 1, 6, 3], ![2, 4, 3, 0, 1, 6], ![2, 0, 1, 4, 3, 5]], proof := .tail 59 }

theorem namedLeaf075_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6219)) namedLeaf075 = true :=
  by decide +kernel

def namedLeaf076 : LeafData := { rows := ![![1, 5, 3, 4, 6, 2], ![0, 5, 3, 6, 4, 2], ![3, 4, 5, 6, 0, 1], ![2, 5, 0, 1, 6, 4], ![2, 5, 0, 6, 1, 3], ![2, 4, 3, 0, 1, 6], ![2, 0, 4, 1, 3, 5]], proof := .tail 114 }

theorem namedLeaf076_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6220)) namedLeaf076 = true :=
  by decide +kernel

def namedLeaf077 : LeafData := { rows := ![![1, 5, 3, 4, 6, 2], ![0, 5, 6, 3, 4, 2], ![3, 4, 5, 6, 0, 1], ![2, 5, 0, 6, 1, 4], ![2, 5, 0, 6, 1, 3], ![2, 4, 3, 0, 1, 6], ![2, 0, 4, 3, 1, 5]], proof := .tail 22 }

theorem namedLeaf077_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6221)) namedLeaf077 = true :=
  by decide +kernel

def namedLeaf078 : LeafData := { rows := ![![1, 5, 3, 4, 6, 2], ![0, 6, 5, 3, 4, 2], ![3, 4, 5, 6, 0, 1], ![2, 5, 0, 6, 1, 4], ![2, 5, 0, 6, 1, 3], ![2, 4, 3, 0, 6, 1], ![2, 0, 4, 3, 5, 1]], proof := .tail 19 }

theorem namedLeaf078_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6222)) namedLeaf078 = true :=
  by decide +kernel

def namedLeaf079 : LeafData := { rows := ![![1, 5, 3, 6, 4, 2], ![0, 5, 3, 6, 4, 2], ![3, 4, 5, 6, 0, 1], ![2, 5, 0, 1, 6, 4], ![2, 5, 6, 0, 1, 3], ![2, 4, 3, 0, 1, 6], ![2, 4, 0, 1, 3, 5]], proof := .low (![95, 52, 116, 4, 121, 159, 164, 163, 117, 51, 178, 195, 78, 122, 51, 178, 195, 45, 44, 186, 185, 71, 49, 106, 3, 120, 63, 167]) }

theorem namedLeaf079_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6223)) namedLeaf079 = true :=
  by decide +kernel

def namedLeaf080 : LeafData := { rows := ![![1, 5, 3, 6, 4, 2], ![0, 5, 6, 3, 4, 2], ![3, 4, 5, 6, 0, 1], ![2, 5, 0, 6, 1, 4], ![2, 5, 6, 0, 1, 3], ![2, 4, 3, 0, 1, 6], ![2, 4, 0, 3, 1, 5]], proof := .tail 133 }

theorem namedLeaf080_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6224)) namedLeaf080 = true :=
  by decide +kernel

def namedLeaf081 : LeafData := { rows := ![![1, 5, 3, 6, 4, 2], ![0, 6, 5, 3, 4, 2], ![3, 4, 5, 6, 0, 1], ![2, 5, 0, 6, 1, 4], ![2, 5, 6, 0, 1, 3], ![2, 4, 3, 0, 6, 1], ![2, 4, 0, 3, 5, 1]], proof := .tail 145 }

theorem namedLeaf081_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6225)) namedLeaf081 = true :=
  by decide +kernel

def namedLeaf082 : LeafData := { rows := ![![1, 5, 6, 3, 4, 2], ![0, 5, 6, 3, 4, 2], ![3, 4, 5, 6, 0, 1], ![2, 5, 6, 0, 1, 4], ![2, 5, 6, 0, 1, 3], ![2, 4, 3, 0, 1, 6], ![2, 4, 3, 0, 1, 5]], proof := .low (![170, 12, 68, 93, 127, 29, 24, 140, 76, 192, 48, 84, 78, 130, 17, 48, 84, 174, 77, 124, 53, 125, 26, 97, 6, 196, 100, 152]) }

theorem namedLeaf082_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6226)) namedLeaf082 = true :=
  by decide +kernel

def namedLeaf083 : LeafData := { rows := ![![1, 5, 6, 3, 4, 2], ![0, 6, 5, 3, 4, 2], ![3, 4, 5, 6, 0, 1], ![2, 5, 6, 0, 1, 4], ![2, 5, 6, 0, 1, 3], ![2, 4, 3, 0, 6, 1], ![2, 4, 3, 0, 5, 1]], proof := .tail 32 }

theorem namedLeaf083_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6227)) namedLeaf083 = true :=
  by decide +kernel

def namedLeaf084 : LeafData := { rows := ![![1, 6, 5, 3, 4, 2], ![0, 6, 5, 3, 4, 2], ![3, 4, 5, 6, 0, 1], ![2, 5, 6, 0, 1, 4], ![2, 5, 6, 0, 1, 3], ![2, 4, 3, 6, 0, 1], ![2, 4, 3, 5, 0, 1]], proof := .tail 39 }

theorem namedLeaf084_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6228)) namedLeaf084 = true :=
  by decide +kernel

def namedLeaf085 : LeafData := { rows := ![![1, 6, 5, 3, 4, 2], ![0, 6, 5, 3, 4, 2], ![3, 4, 5, 6, 0, 1], ![2, 6, 5, 0, 1, 4], ![2, 5, 6, 0, 1, 3], ![2, 4, 6, 3, 0, 1], ![2, 4, 5, 3, 0, 1]], proof := .tail 157 }

theorem namedLeaf085_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6229)) namedLeaf085 = true :=
  by decide +kernel

def namedLeaf086 : LeafData := { rows := ![![1, 6, 5, 3, 4, 2], ![0, 6, 5, 3, 4, 2], ![3, 4, 5, 6, 0, 1], ![2, 6, 5, 0, 1, 4], ![2, 6, 5, 0, 1, 3], ![2, 6, 4, 3, 0, 1], ![2, 5, 4, 3, 0, 1]], proof := .tail 80 }

theorem namedLeaf086_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6230)) namedLeaf086 = true :=
  by decide +kernel

def namedLeaf087 : LeafData := { rows := ![![1, 6, 5, 3, 4, 2], ![0, 6, 5, 3, 4, 2], ![3, 4, 6, 5, 0, 1], ![2, 6, 5, 0, 1, 4], ![2, 6, 5, 0, 1, 3], ![6, 2, 4, 3, 0, 1], ![5, 2, 4, 3, 0, 1]], proof := .tail 27 }

theorem namedLeaf087_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6231)) namedLeaf087 = true :=
  by decide +kernel

def namedLeaf088 : LeafData := { rows := ![![1, 6, 5, 3, 4, 2], ![0, 6, 5, 3, 4, 2], ![3, 6, 4, 5, 0, 1], ![2, 6, 5, 0, 1, 4], ![6, 2, 5, 0, 1, 3], ![6, 2, 4, 3, 0, 1], ![5, 4, 2, 3, 0, 1]], proof := .tail 146 }

theorem namedLeaf088_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6232)) namedLeaf088 = true :=
  by decide +kernel

def namedLeaf089 : LeafData := { rows := ![![1, 6, 5, 3, 4, 2], ![0, 6, 5, 3, 4, 2], ![6, 3, 4, 5, 0, 1], ![6, 2, 5, 0, 1, 4], ![6, 2, 5, 0, 1, 3], ![6, 2, 4, 3, 0, 1], ![5, 4, 3, 2, 0, 1]], proof := .tail 56 }

theorem namedLeaf089_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6233)) namedLeaf089 = true :=
  by decide +kernel

def namedLeaf090 : LeafData := { rows := ![![1, 5, 3, 4, 6, 2], ![0, 5, 3, 4, 6, 2], ![3, 5, 4, 6, 0, 1], ![2, 5, 0, 1, 4, 6], ![5, 2, 0, 1, 3, 6], ![4, 2, 3, 0, 1, 6], ![2, 0, 1, 3, 4, 5]], proof := .tail 81 }

theorem namedLeaf090_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6234)) namedLeaf090 = true :=
  by decide +kernel

def namedLeaf091 : LeafData := { rows := ![![1, 5, 3, 4, 6, 2], ![0, 5, 3, 4, 6, 2], ![3, 5, 4, 6, 0, 1], ![2, 5, 0, 1, 6, 4], ![5, 2, 0, 1, 6, 3], ![4, 2, 3, 0, 1, 6], ![2, 0, 1, 4, 3, 5]], proof := .tail 33 }

theorem namedLeaf091_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6235)) namedLeaf091 = true :=
  by decide +kernel

def namedLeaf092 : LeafData := { rows := ![![1, 5, 3, 4, 6, 2], ![0, 5, 3, 6, 4, 2], ![3, 5, 4, 6, 0, 1], ![2, 5, 0, 1, 6, 4], ![5, 2, 0, 6, 1, 3], ![4, 2, 3, 0, 1, 6], ![2, 0, 4, 1, 3, 5]], proof := .tail 114 }

theorem namedLeaf092_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6236)) namedLeaf092 = true :=
  by decide +kernel

def namedLeaf093 : LeafData := { rows := ![![1, 5, 3, 6, 4, 2], ![0, 5, 3, 6, 4, 2], ![3, 5, 4, 6, 0, 1], ![2, 5, 0, 1, 6, 4], ![5, 2, 6, 0, 1, 3], ![4, 2, 3, 0, 1, 6], ![2, 4, 0, 1, 3, 5]], proof := .tail 85 }

theorem namedLeaf093_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6237)) namedLeaf093 = true :=
  by decide +kernel

def namedLeaf094 : LeafData := { rows := ![![1, 5, 3, 6, 4, 2], ![0, 5, 3, 6, 4, 2], ![3, 5, 6, 4, 0, 1], ![2, 5, 0, 1, 6, 4], ![5, 6, 2, 0, 1, 3], ![4, 2, 3, 0, 1, 6], ![4, 2, 0, 1, 3, 5]], proof := .low (![95, 52, 116, 4, 121, 159, 164, 163, 117, 51, 178, 195, 78, 122, 51, 178, 195, 154, 44, 186, 185, 71, 49, 106, 3, 120, 63, 167]) }

theorem namedLeaf094_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6238)) namedLeaf094 = true :=
  by decide +kernel

def namedLeaf095 : LeafData := { rows := ![![1, 5, 3, 4, 6, 2], ![0, 5, 6, 3, 4, 2], ![3, 5, 4, 6, 0, 1], ![2, 5, 0, 6, 1, 4], ![5, 2, 0, 6, 1, 3], ![4, 2, 3, 0, 1, 6], ![2, 0, 4, 3, 1, 5]], proof := .tail 191 }

theorem namedLeaf095_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6239)) namedLeaf095 = true :=
  by decide +kernel

def namedLeaf096 : LeafData := { rows := ![![1, 5, 3, 6, 4, 2], ![0, 5, 6, 3, 4, 2], ![3, 5, 4, 6, 0, 1], ![2, 5, 0, 6, 1, 4], ![5, 2, 6, 0, 1, 3], ![4, 2, 3, 0, 1, 6], ![2, 4, 0, 3, 1, 5]], proof := .tail 141 }

theorem namedLeaf096_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6240)) namedLeaf096 = true :=
  by decide +kernel

def namedLeaf097 : LeafData := { rows := ![![1, 5, 3, 6, 4, 2], ![0, 5, 6, 3, 4, 2], ![3, 5, 6, 4, 0, 1], ![2, 5, 0, 6, 1, 4], ![5, 6, 2, 0, 1, 3], ![4, 2, 3, 0, 1, 6], ![4, 2, 0, 3, 1, 5]], proof := .tail 191 }

theorem namedLeaf097_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6241)) namedLeaf097 = true :=
  by decide +kernel

def namedLeaf098 : LeafData := { rows := ![![1, 5, 3, 4, 6, 2], ![0, 6, 5, 3, 4, 2], ![3, 5, 4, 6, 0, 1], ![2, 5, 0, 6, 1, 4], ![5, 2, 0, 6, 1, 3], ![4, 2, 3, 0, 6, 1], ![2, 0, 4, 3, 5, 1]], proof := .tail 145 }

theorem namedLeaf098_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6242)) namedLeaf098 = true :=
  by decide +kernel

def namedLeaf099 : LeafData := { rows := ![![1, 5, 3, 6, 4, 2], ![0, 6, 5, 3, 4, 2], ![3, 5, 4, 6, 0, 1], ![2, 5, 0, 6, 1, 4], ![5, 2, 6, 0, 1, 3], ![4, 2, 3, 0, 6, 1], ![2, 4, 0, 3, 5, 1]], proof := .tail 16 }

theorem namedLeaf099_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6243)) namedLeaf099 = true :=
  by decide +kernel

def namedLeaf100 : LeafData := { rows := ![![1, 5, 3, 6, 4, 2], ![0, 6, 5, 3, 4, 2], ![3, 5, 6, 4, 0, 1], ![2, 5, 0, 6, 1, 4], ![5, 6, 2, 0, 1, 3], ![4, 2, 3, 0, 6, 1], ![4, 2, 0, 3, 5, 1]], proof := .tail 145 }

theorem namedLeaf100_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6244)) namedLeaf100 = true :=
  by decide +kernel

def namedLeaf101 : LeafData := { rows := ![![1, 5, 6, 3, 4, 2], ![0, 5, 6, 3, 4, 2], ![3, 5, 4, 6, 0, 1], ![2, 5, 6, 0, 1, 4], ![5, 2, 6, 0, 1, 3], ![4, 2, 3, 0, 1, 6], ![2, 4, 3, 0, 1, 5]], proof := .tail 37 }

theorem namedLeaf101_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6245)) namedLeaf101 = true :=
  by decide +kernel

def namedLeaf102 : LeafData := { rows := ![![1, 5, 6, 3, 4, 2], ![0, 6, 5, 3, 4, 2], ![3, 5, 4, 6, 0, 1], ![2, 5, 6, 0, 1, 4], ![5, 2, 6, 0, 1, 3], ![4, 2, 3, 0, 6, 1], ![2, 4, 3, 0, 5, 1]], proof := .tail 16 }

theorem namedLeaf102_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6246)) namedLeaf102 = true :=
  by decide +kernel

def namedLeaf103 : LeafData := { rows := ![![1, 6, 5, 3, 4, 2], ![0, 6, 5, 3, 4, 2], ![3, 5, 4, 6, 0, 1], ![2, 5, 6, 0, 1, 4], ![5, 2, 6, 0, 1, 3], ![4, 2, 3, 6, 0, 1], ![2, 4, 3, 5, 0, 1]], proof := .tail 168 }

theorem namedLeaf103_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6247)) namedLeaf103 = true :=
  by decide +kernel

def namedLeaf104 : LeafData := { rows := ![![1, 6, 5, 3, 4, 2], ![0, 6, 5, 3, 4, 2], ![3, 5, 4, 6, 0, 1], ![2, 6, 5, 0, 1, 4], ![5, 2, 6, 0, 1, 3], ![4, 2, 6, 3, 0, 1], ![2, 4, 5, 3, 0, 1]], proof := .tail 157 }

theorem namedLeaf104_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6248)) namedLeaf104 = true :=
  by decide +kernel

def namedLeaf105 : LeafData := { rows := ![![1, 5, 6, 3, 4, 2], ![0, 5, 6, 3, 4, 2], ![3, 5, 6, 4, 0, 1], ![2, 5, 6, 0, 1, 4], ![5, 6, 2, 0, 1, 3], ![4, 2, 3, 0, 1, 6], ![4, 2, 3, 0, 1, 5]], proof := .low (![170, 12, 68, 70, 127, 29, 24, 140, 76, 192, 48, 84, 78, 150, 34, 48, 84, 5, 15, 124, 53, 125, 26, 97, 6, 196, 100, 152]) }

theorem namedLeaf105_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6249)) namedLeaf105 = true :=
  by decide +kernel

def namedLeaf106 : LeafData := { rows := ![![1, 5, 6, 3, 4, 2], ![0, 6, 5, 3, 4, 2], ![3, 5, 6, 4, 0, 1], ![2, 5, 6, 0, 1, 4], ![5, 6, 2, 0, 1, 3], ![4, 2, 3, 0, 6, 1], ![4, 2, 3, 0, 5, 1]], proof := .tail 32 }

theorem namedLeaf106_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6250)) namedLeaf106 = true :=
  by decide +kernel

def namedLeaf107 : LeafData := { rows := ![![1, 6, 5, 3, 4, 2], ![0, 6, 5, 3, 4, 2], ![3, 5, 6, 4, 0, 1], ![2, 5, 6, 0, 1, 4], ![5, 6, 2, 0, 1, 3], ![4, 2, 3, 6, 0, 1], ![4, 2, 3, 5, 0, 1]], proof := .tail 39 }

theorem namedLeaf107_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6251)) namedLeaf107 = true :=
  by decide +kernel

def namedLeaf108 : LeafData := { rows := ![![1, 6, 5, 3, 4, 2], ![0, 6, 5, 3, 4, 2], ![3, 5, 6, 4, 0, 1], ![2, 6, 5, 0, 1, 4], ![5, 6, 2, 0, 1, 3], ![4, 2, 6, 3, 0, 1], ![4, 2, 5, 3, 0, 1]], proof := .tail 157 }

theorem namedLeaf108_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6252)) namedLeaf108 = true :=
  by decide +kernel

def namedLeaf109 : LeafData := { rows := ![![1, 6, 5, 3, 4, 2], ![0, 6, 5, 3, 4, 2], ![3, 6, 5, 4, 0, 1], ![2, 6, 5, 0, 1, 4], ![5, 6, 2, 0, 1, 3], ![4, 6, 2, 3, 0, 1], ![4, 5, 2, 3, 0, 1]], proof := .tail 50 }

theorem namedLeaf109_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6253)) namedLeaf109 = true :=
  by decide +kernel

def namedLeaf110 : LeafData := { rows := ![![1, 6, 5, 3, 4, 2], ![0, 6, 5, 3, 4, 2], ![3, 6, 5, 4, 0, 1], ![2, 6, 5, 0, 1, 4], ![6, 5, 2, 0, 1, 3], ![6, 4, 2, 3, 0, 1], ![5, 4, 2, 3, 0, 1]], proof := .tail 177 }

theorem namedLeaf110_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6254)) namedLeaf110 = true :=
  by decide +kernel

def namedLeaf111 : LeafData := { rows := ![![1, 6, 5, 3, 4, 2], ![0, 6, 5, 3, 4, 2], ![6, 3, 5, 4, 0, 1], ![6, 2, 5, 0, 1, 4], ![5, 6, 2, 0, 1, 3], ![4, 6, 2, 3, 0, 1], ![4, 5, 3, 2, 0, 1]], proof := .tail 144 }

theorem namedLeaf111_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6255)) namedLeaf111 = true :=
  by decide +kernel

def namedLeaf112 : LeafData := { rows := ![![1, 6, 5, 3, 4, 2], ![0, 6, 5, 3, 4, 2], ![6, 3, 5, 4, 0, 1], ![6, 2, 5, 0, 1, 4], ![6, 5, 2, 0, 1, 3], ![6, 4, 2, 3, 0, 1], ![5, 4, 3, 2, 0, 1]], proof := .tail 56 }

theorem namedLeaf112_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6256)) namedLeaf112 = true :=
  by decide +kernel

def namedLeaf113 : LeafData := { rows := ![![1, 5, 3, 4, 6, 2], ![0, 5, 3, 4, 6, 2], ![5, 3, 4, 6, 0, 1], ![5, 2, 0, 1, 4, 6], ![5, 2, 0, 1, 3, 6], ![4, 3, 2, 0, 1, 6], ![2, 0, 1, 3, 4, 5]], proof := .tail 81 }

theorem namedLeaf113_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6257)) namedLeaf113 = true :=
  by decide +kernel

def namedLeaf114 : LeafData := { rows := ![![1, 5, 3, 4, 6, 2], ![0, 5, 3, 4, 6, 2], ![5, 3, 4, 6, 0, 1], ![5, 2, 0, 1, 6, 4], ![5, 2, 0, 1, 6, 3], ![4, 3, 2, 0, 1, 6], ![2, 0, 1, 4, 3, 5]], proof := .tail 180 }

theorem namedLeaf114_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6258)) namedLeaf114 = true :=
  by decide +kernel

def namedLeaf115 : LeafData := { rows := ![![1, 5, 3, 4, 6, 2], ![0, 5, 3, 6, 4, 2], ![5, 3, 4, 6, 0, 1], ![5, 2, 0, 1, 6, 4], ![5, 2, 0, 6, 1, 3], ![4, 3, 2, 0, 1, 6], ![2, 0, 4, 1, 3, 5]], proof := .tail 109 }

theorem namedLeaf115_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6259)) namedLeaf115 = true :=
  by decide +kernel

def namedLeaf116 : LeafData := { rows := ![![1, 5, 3, 6, 4, 2], ![0, 5, 3, 6, 4, 2], ![5, 3, 4, 6, 0, 1], ![5, 2, 0, 1, 6, 4], ![5, 2, 6, 0, 1, 3], ![4, 3, 2, 0, 1, 6], ![2, 4, 0, 1, 3, 5]], proof := .tail 69 }

theorem namedLeaf116_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6260)) namedLeaf116 = true :=
  by decide +kernel

def namedLeaf117 : LeafData := { rows := ![![1, 5, 3, 6, 4, 2], ![0, 5, 3, 6, 4, 2], ![5, 3, 6, 4, 0, 1], ![5, 2, 0, 1, 6, 4], ![5, 6, 2, 0, 1, 3], ![4, 3, 2, 0, 1, 6], ![4, 2, 0, 1, 3, 5]], proof := .low (![95, 52, 116, 4, 67, 87, 58, 163, 117, 184, 35, 169, 78, 122, 126, 66, 8, 10, 44, 122, 122, 71, 103, 21, 46, 132, 42, 92]) }

theorem namedLeaf117_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6261)) namedLeaf117 = true :=
  by decide +kernel

def namedLeaf118 : LeafData := { rows := ![![1, 5, 3, 4, 6, 2], ![0, 5, 6, 3, 4, 2], ![5, 3, 4, 6, 0, 1], ![5, 2, 0, 6, 1, 4], ![5, 2, 0, 6, 1, 3], ![4, 3, 2, 0, 1, 6], ![2, 0, 4, 3, 1, 5]], proof := .tail 98 }

theorem namedLeaf118_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6262)) namedLeaf118 = true :=
  by decide +kernel

def namedLeaf119 : LeafData := { rows := ![![1, 5, 3, 6, 4, 2], ![0, 5, 6, 3, 4, 2], ![5, 3, 4, 6, 0, 1], ![5, 2, 0, 6, 1, 4], ![5, 2, 6, 0, 1, 3], ![4, 3, 2, 0, 1, 6], ![2, 4, 0, 3, 1, 5]], proof := .tail 98 }

theorem namedLeaf119_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6263)) namedLeaf119 = true :=
  by decide +kernel

def namedLeaf120 : LeafData := { rows := ![![1, 5, 3, 6, 4, 2], ![0, 5, 6, 3, 4, 2], ![5, 3, 6, 4, 0, 1], ![5, 2, 0, 6, 1, 4], ![5, 6, 2, 0, 1, 3], ![4, 3, 2, 0, 1, 6], ![4, 2, 0, 3, 1, 5]], proof := .tail 98 }

theorem namedLeaf120_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6264)) namedLeaf120 = true :=
  by decide +kernel

def namedLeaf121 : LeafData := { rows := ![![1, 5, 3, 4, 6, 2], ![0, 6, 5, 3, 4, 2], ![5, 3, 4, 6, 0, 1], ![5, 2, 0, 6, 1, 4], ![5, 2, 0, 6, 1, 3], ![4, 3, 2, 0, 6, 1], ![2, 0, 4, 3, 5, 1]], proof := .tail 73 }

theorem namedLeaf121_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6265)) namedLeaf121 = true :=
  by decide +kernel

def namedLeaf122 : LeafData := { rows := ![![1, 5, 3, 6, 4, 2], ![0, 6, 5, 3, 4, 2], ![5, 3, 4, 6, 0, 1], ![5, 2, 0, 6, 1, 4], ![5, 2, 6, 0, 1, 3], ![4, 3, 2, 0, 6, 1], ![2, 4, 0, 3, 5, 1]], proof := .tail 73 }

theorem namedLeaf122_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6266)) namedLeaf122 = true :=
  by decide +kernel

def namedLeaf123 : LeafData := { rows := ![![1, 5, 3, 6, 4, 2], ![0, 6, 5, 3, 4, 2], ![5, 3, 6, 4, 0, 1], ![5, 2, 0, 6, 1, 4], ![5, 6, 2, 0, 1, 3], ![4, 3, 2, 0, 6, 1], ![4, 2, 0, 3, 5, 1]], proof := .tail 73 }

theorem namedLeaf123_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6267)) namedLeaf123 = true :=
  by decide +kernel

def namedLeaf124 : LeafData := { rows := ![![1, 5, 6, 3, 4, 2], ![0, 5, 6, 3, 4, 2], ![5, 3, 4, 6, 0, 1], ![5, 2, 6, 0, 1, 4], ![5, 2, 6, 0, 1, 3], ![4, 3, 2, 0, 1, 6], ![2, 4, 3, 0, 1, 5]], proof := .tail 47 }

theorem namedLeaf124_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6268)) namedLeaf124 = true :=
  by decide +kernel

def namedLeaf125 : LeafData := { rows := ![![1, 5, 6, 3, 4, 2], ![0, 6, 5, 3, 4, 2], ![5, 3, 4, 6, 0, 1], ![5, 2, 6, 0, 1, 4], ![5, 2, 6, 0, 1, 3], ![4, 3, 2, 0, 6, 1], ![2, 4, 3, 0, 5, 1]], proof := .tail 73 }

theorem namedLeaf125_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6269)) namedLeaf125 = true :=
  by decide +kernel

def namedLeaf126 : LeafData := { rows := ![![1, 6, 5, 3, 4, 2], ![0, 6, 5, 3, 4, 2], ![5, 3, 4, 6, 0, 1], ![5, 2, 6, 0, 1, 4], ![5, 2, 6, 0, 1, 3], ![4, 3, 2, 6, 0, 1], ![2, 4, 3, 5, 0, 1]], proof := .tail 162 }

theorem namedLeaf126_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6270)) namedLeaf126 = true :=
  by decide +kernel

def namedLeaf127 : LeafData := { rows := ![![1, 5, 6, 3, 4, 2], ![0, 5, 6, 3, 4, 2], ![5, 3, 6, 4, 0, 1], ![5, 2, 6, 0, 1, 4], ![5, 6, 2, 0, 1, 3], ![4, 3, 2, 0, 1, 6], ![4, 2, 3, 0, 1, 5]], proof := .tail 65 }

theorem namedLeaf127_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6271)) namedLeaf127 = true :=
  by decide +kernel

def fallback : LeafData := { rows := fun _ _ => 0, proof := .tail 0 }
def lookup (offset : ℕ) : LeafData :=
  if offset < 128 then (if offset < 64 then (if offset < 32 then (if offset < 16 then (if offset < 8 then (if offset < 4 then (if offset < 2 then (if offset < 1 then (namedLeaf000) else (namedLeaf001)) else (if offset < 3 then (namedLeaf002) else (namedLeaf003))) else (if offset < 6 then (if offset < 5 then (namedLeaf004) else (namedLeaf005)) else (if offset < 7 then (namedLeaf006) else (namedLeaf007)))) else (if offset < 12 then (if offset < 10 then (if offset < 9 then (namedLeaf008) else (namedLeaf009)) else (if offset < 11 then (namedLeaf010) else (namedLeaf011))) else (if offset < 14 then (if offset < 13 then (namedLeaf012) else (namedLeaf013)) else (if offset < 15 then (namedLeaf014) else (namedLeaf015))))) else (if offset < 24 then (if offset < 20 then (if offset < 18 then (if offset < 17 then (namedLeaf016) else (namedLeaf017)) else (if offset < 19 then (namedLeaf018) else (namedLeaf019))) else (if offset < 22 then (if offset < 21 then (namedLeaf020) else (namedLeaf021)) else (if offset < 23 then (namedLeaf022) else (namedLeaf023)))) else (if offset < 28 then (if offset < 26 then (if offset < 25 then (namedLeaf024) else (namedLeaf025)) else (if offset < 27 then (namedLeaf026) else (namedLeaf027))) else (if offset < 30 then (if offset < 29 then (namedLeaf028) else (namedLeaf029)) else (if offset < 31 then (namedLeaf030) else (namedLeaf031)))))) else (if offset < 48 then (if offset < 40 then (if offset < 36 then (if offset < 34 then (if offset < 33 then (namedLeaf032) else (namedLeaf033)) else (if offset < 35 then (namedLeaf034) else (namedLeaf035))) else (if offset < 38 then (if offset < 37 then (namedLeaf036) else (namedLeaf037)) else (if offset < 39 then (namedLeaf038) else (namedLeaf039)))) else (if offset < 44 then (if offset < 42 then (if offset < 41 then (namedLeaf040) else (namedLeaf041)) else (if offset < 43 then (namedLeaf042) else (namedLeaf043))) else (if offset < 46 then (if offset < 45 then (namedLeaf044) else (namedLeaf045)) else (if offset < 47 then (namedLeaf046) else (namedLeaf047))))) else (if offset < 56 then (if offset < 52 then (if offset < 50 then (if offset < 49 then (namedLeaf048) else (namedLeaf049)) else (if offset < 51 then (namedLeaf050) else (namedLeaf051))) else (if offset < 54 then (if offset < 53 then (namedLeaf052) else (namedLeaf053)) else (if offset < 55 then (namedLeaf054) else (namedLeaf055)))) else (if offset < 60 then (if offset < 58 then (if offset < 57 then (namedLeaf056) else (namedLeaf057)) else (if offset < 59 then (namedLeaf058) else (namedLeaf059))) else (if offset < 62 then (if offset < 61 then (namedLeaf060) else (namedLeaf061)) else (if offset < 63 then (namedLeaf062) else (namedLeaf063))))))) else (if offset < 96 then (if offset < 80 then (if offset < 72 then (if offset < 68 then (if offset < 66 then (if offset < 65 then (namedLeaf064) else (namedLeaf065)) else (if offset < 67 then (namedLeaf066) else (namedLeaf067))) else (if offset < 70 then (if offset < 69 then (namedLeaf068) else (namedLeaf069)) else (if offset < 71 then (namedLeaf070) else (namedLeaf071)))) else (if offset < 76 then (if offset < 74 then (if offset < 73 then (namedLeaf072) else (namedLeaf073)) else (if offset < 75 then (namedLeaf074) else (namedLeaf075))) else (if offset < 78 then (if offset < 77 then (namedLeaf076) else (namedLeaf077)) else (if offset < 79 then (namedLeaf078) else (namedLeaf079))))) else (if offset < 88 then (if offset < 84 then (if offset < 82 then (if offset < 81 then (namedLeaf080) else (namedLeaf081)) else (if offset < 83 then (namedLeaf082) else (namedLeaf083))) else (if offset < 86 then (if offset < 85 then (namedLeaf084) else (namedLeaf085)) else (if offset < 87 then (namedLeaf086) else (namedLeaf087)))) else (if offset < 92 then (if offset < 90 then (if offset < 89 then (namedLeaf088) else (namedLeaf089)) else (if offset < 91 then (namedLeaf090) else (namedLeaf091))) else (if offset < 94 then (if offset < 93 then (namedLeaf092) else (namedLeaf093)) else (if offset < 95 then (namedLeaf094) else (namedLeaf095)))))) else (if offset < 112 then (if offset < 104 then (if offset < 100 then (if offset < 98 then (if offset < 97 then (namedLeaf096) else (namedLeaf097)) else (if offset < 99 then (namedLeaf098) else (namedLeaf099))) else (if offset < 102 then (if offset < 101 then (namedLeaf100) else (namedLeaf101)) else (if offset < 103 then (namedLeaf102) else (namedLeaf103)))) else (if offset < 108 then (if offset < 106 then (if offset < 105 then (namedLeaf104) else (namedLeaf105)) else (if offset < 107 then (namedLeaf106) else (namedLeaf107))) else (if offset < 110 then (if offset < 109 then (namedLeaf108) else (namedLeaf109)) else (if offset < 111 then (namedLeaf110) else (namedLeaf111))))) else (if offset < 120 then (if offset < 116 then (if offset < 114 then (if offset < 113 then (namedLeaf112) else (namedLeaf113)) else (if offset < 115 then (namedLeaf114) else (namedLeaf115))) else (if offset < 118 then (if offset < 117 then (namedLeaf116) else (namedLeaf117)) else (if offset < 119 then (namedLeaf118) else (namedLeaf119)))) else (if offset < 124 then (if offset < 122 then (if offset < 121 then (namedLeaf120) else (namedLeaf121)) else (if offset < 123 then (namedLeaf122) else (namedLeaf123))) else (if offset < 126 then (if offset < 125 then (namedLeaf124) else (namedLeaf125)) else (if offset < 127 then (namedLeaf126) else (namedLeaf127)))))))) else fallback

theorem point_checked (j : Fin 128) :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 (6144 + j.val))) (lookup j.val) = true := by
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

theorem correct (id : Fin 24698) (hlow : 6144 ≤ id.val) (hhigh : id.val < 6272) :
    leafCheck library (N4R2WordTree.catalog id) (lookup (id.val - 6144)) = true := by
  let j : Fin 128 := ⟨id.val - 6144, by omega⟩
  have hsum : 6144 + j.val = id.val := by dsimp [j]; omega
  have hindex : Fin.ofNat 24698 (6144 + j.val) = id := by
    apply Fin.ext
    simp only [Fin.ofNat, hsum, Nat.mod_eq_of_lt id.isLt]
  have hh := point_checked j
  rw [hindex] at hh
  exact hh

#print axioms point_checked
#print axioms correct
end Jsp404.N4R2OuterLeftData.LeafShard048
