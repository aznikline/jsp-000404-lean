import Jsp000404.N4R2OuterLeftReplay
import Jsp000404.N4R2WordCatalog

set_option autoImplicit false
set_option pp.fullNames true
set_option maxRecDepth 8192
set_option maxHeartbeats 0
set_option Elab.async false

namespace Jsp404.N4R2OuterLeftData.LeafShard168
open N4R2OuterLeftReplay

-- Cycle fingerprint 038b359e3c1f535bb30a979012099dcaa7e180ae25d6c6316c2a8fcafb917b1c.
def localCycle00000 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 2, .theta 1, .distance 0 1, .distance 1 5, .distance 5 6, .theta 5, .distance 4 5, .distance 3 4, .distance 2 3, .distance 1 2]
    constant := ![-1, 2, -2, -1, -1, 3, -1, -1, -1]
    coefficient := ![0, 1, 0, 0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false, false] }
  origin := ![.corridorLower 1 2, .gapLower 1 6, .gapLower 1 5, .triangle 24 0, .corridorLower 5 6, .corridorUpper 4 5, .triangle 31 0, .triangle 25 0, .triangle 15 0]

-- Cycle fingerprint 03d804322ddd0a124c3865ecaf6e14f06b214f6a3b15295cd3ce2d8b289368a1.
def localCycle00001 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 5, .distance 1 6, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1, .distance 0 1, .distance 0 2, .distance 2 5, .distance 1 5]
    constant := ![0, -2, 0, -2, -1, 3, 0, -1, 0]
    coefficient := ![0, 0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![true, false, true, false, false, false, true, false, true] }
  origin := ![.triangle 24 2, .gapLower 1 3, .triangle 19 1, .gapLower 1 1, .corridorLower 1 2, .corridorUpper 0 1, .triangle 0 2, .triangle 7 0, .triangle 17 2]

-- Cycle fingerprint 0407ca5a506ee07a3cd3cb91f6e63e24dee8c9cc53ce7cb6c04dbd181f3d4b4e.
def localCycle00002 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 0 4, .distance 4 5, .distance 3 5, .distance 2 3, .distance 3 4, .theta 3, .zero]
    constant := ![0, 3, 0, -1, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, false, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 13 0, .triangle 12 0, .triangle 31 2, .triangle 26 0, .triangle 25 0, .corridorLower 3 4, .thetaLower 3]

-- Cycle fingerprint 06730242989941dbff2fade7f7299ceaa8afbe07f39f0d5107e58fd10a551dfa.
def localCycle00003 : Cycle where
  length := 6
  data := {
    node := ![.distance 1 4, .distance 1 3, .distance 1 2, .theta 1, .distance 0 1, .distance 1 6, .distance 1 4]
    constant := ![0, 0, -1, 3, -3, 0]
    coefficient := ![0, 0, 0, 1, 0, 0]
    strict := ![true, true, false, false, false, true] }
  origin := ![.triangle 19 1, .triangle 15 1, .corridorLower 1 2, .corridorUpper 0 1, .gapLower 1 5, .triangle 23 1]

-- Cycle fingerprint 0779ff36dbb3649404f50ec3e0fbed75a8a51b4ec5e90f1bb8651af7195ac9d2.
def localCycle00004 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 3 6, .distance 0 3, .distance 3 4, .distance 1 3, .distance 3 5, .distance 2 3, .theta 3]
    constant := ![4, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 3 6, .triangle 11 0, .triangle 9 0, .triangle 19 0, .triangle 20 0, .triangle 26 0, .gapLower 3 0]

-- Cycle fingerprint 07a978c3c9c6183724e92af296a2ea282f69eb273b55865f202306c04c1e2a54.
def localCycle00005 : Cycle where
  length := 5
  data := {
    node := ![.distance 1 6, .distance 1 4, .theta 1, .distance 0 1, .distance 1 5, .distance 1 6]
    constant := ![-2, -1, 3, -2, 0]
    coefficient := ![0, 0, 1, 0, 0]
    strict := ![false, false, false, false, true] }
  origin := ![.gapLower 1 3, .corridorLower 1 4, .corridorUpper 0 1, .gapLower 1 5, .triangle 24 2]

-- Cycle fingerprint 08516f2665de92409ec2a76049c4831c8e5c58603e6f2aefa7b5e4417b4c6684.
def localCycle00006 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 6, .theta 6, .theta 5, .theta 4, .distance 3 4, .distance 4 5, .distance 0 4, .distance 0 6]
    constant := ![-2, 0, 0, 3, -1, -1, 0]
    coefficient := ![-1, 0, 0, 1, 0, 0, 0]
    strict := ![true, true, true, false, false, false, true] }
  origin := ![.gapUpper 6 6, .thetaNext 5, .thetaNext 4, .corridorUpper 3 4, .triangle 31 0, .triangle 12 0, .triangle 13 2]

-- Cycle fingerprint 088343b25fd89a845d211e146db752bd5a387c8d5a6ad48a31d58b0d6c01036f.
def localCycle00007 : Cycle where
  length := 10
  data := {
    node := ![.theta 1, .distance 0 1, .distance 1 6, .distance 1 2, .distance 1 3, .distance 1 4, .distance 4 5, .distance 3 4, .theta 3, .theta 2, .theta 1]
    constant := ![3, -1, 0, 0, 0, -1, -1, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, true, false, false, false, true, true] }
  origin := ![.corridorUpper 0 1, .triangle 4 0, .triangle 18 1, .triangle 15 2, .triangle 19 2, .triangle 22 0, .triangle 31 0, .corridorLower 3 4, .thetaNext 2, .thetaNext 1]

-- Cycle fingerprint 092c9d6bd907f5dd8df1262962e17cfb2b29b9b2f8431d4c67841cc9efc1547b.
def localCycle00008 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 6, .distance 1 5, .distance 1 3, .distance 1 2, .theta 1, .distance 0 1, .distance 0 2, .distance 2 4, .distance 1 4, .distance 1 6]
    constant := ![0, -3, 0, -1, 3, 0, -1, 0, 0]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0, 0]
    strict := ![true, false, true, false, false, true, false, true, true] }
  origin := ![.triangle 24 1, .gapLower 1 2, .triangle 15 1, .corridorLower 1 2, .corridorUpper 0 1, .triangle 0 2, .triangle 6 0, .triangle 16 2, .triangle 23 2]

-- Cycle fingerprint 09d7051112ecbf457443f3f8ae2a31e5c50e53f4ed8767565d41da57485c60ea.
def localCycle00009 : Cycle where
  length := 8
  data := {
    node := ![.distance 2 6, .distance 2 5, .distance 2 3, .distance 1 2, .theta 1, .distance 0 1, .distance 0 2, .distance 2 4, .distance 2 6]
    constant := ![0, 0, -1, -1, 1, 0, -1, 0]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![true, false, false, false, false, true, false, true] }
  origin := ![.triangle 30 1, .gapLower 2 2, .triangle 15 0, .corridorLower 1 2, .gapLower 1 6, .triangle 0 2, .triangle 6 0, .triangle 29 2]

-- Cycle fingerprint 0af8b91a6a9e86f1820ab0df3b546a3eefcd574685418e964c19eecae1a87559.
def localCycle00010 : Cycle where
  length := 11
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 2, .distance 0 4, .distance 0 5, .distance 5 6, .distance 4 6, .distance 2 4, .distance 4 5, .distance 1 4, .distance 1 3, .theta 1]
    constant := ![3, 0, 0, 0, -1, 0, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, true, false, false, false, false, false] }
  origin := ![.corridorUpper 0 1, .triangle 0 2, .triangle 6 2, .triangle 12 2, .triangle 14 0, .triangle 34 2, .triangle 29 0, .triangle 28 0, .triangle 22 0, .gapLower 1 2, .corridorLower 1 3]

-- Cycle fingerprint 0c1ed657bacddf0ddadc1c2e87ed9e8ef2d64551ec244fc6adca3131f18e6dc5.
def localCycle00011 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 2 5, .distance 1 5, .distance 1 6, .distance 1 4, .distance 1 3, .theta 1, .distance 0 1]
    constant := ![0, -1, 0, 0, -2, -2, -1, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![true, false, true, true, false, false, false, false] }
  origin := ![.triangle 0 2, .triangle 7 0, .triangle 17 2, .triangle 24 2, .gapLower 1 3, .gapLower 1 2, .corridorLower 1 3, .corridorUpper 0 1]

-- Cycle fingerprint 11bcd39ec6637df5a7ef30a411fb56eaccd91cbe4a10b83d3ac47c1722e51232.
def localCycle00012 : Cycle where
  length := 8
  data := {
    node := ![.theta 2, .distance 0 2, .distance 2 4, .distance 4 5, .distance 1 4, .distance 4 6, .theta 4, .theta 3, .theta 2]
    constant := ![3, -1, -1, -1, -1, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, true] }
  origin := ![.corridorUpper 0 2, .triangle 6 0, .triangle 28 0, .triangle 22 0, .triangle 23 0, .corridorLower 4 6, .thetaNext 3, .thetaNext 2]

-- Cycle fingerprint 139664b5d5bbfbb0fab305c29e0d40b84335b59f53b979ebf56254aa21fa414e.
def localCycle00013 : Cycle where
  length := 9
  data := {
    node := ![.distance 4 5, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1, .distance 0 1, .distance 0 2, .distance 2 6, .distance 2 4, .distance 4 5]
    constant := ![-1, 0, 0, -1, 3, 0, -1, 0, -1]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, false, true, false] }
  origin := ![.triangle 22 0, .gapLower 1 2, .triangle 15 1, .corridorLower 1 2, .corridorUpper 0 1, .triangle 0 2, .triangle 8 0, .triangle 29 1, .triangle 28 0]

-- Cycle fingerprint 1440f507746ba8548b7b4391e85c598ce0b2e7c3c7521d3e0b46fb5589fa2310.
def localCycle00014 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 5, .distance 1 3, .distance 1 2, .theta 1, .distance 0 1, .distance 0 2, .distance 2 4, .distance 1 4, .distance 1 6, .distance 1 5]
    constant := ![0, -2, -2, 3, 0, -1, 0, 0, 0]
    coefficient := ![0, 0, 0, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, true, true, true] }
  origin := ![.gapLower 1 2, .gapLower 1 1, .gapLower 1 0, .corridorUpper 0 1, .triangle 0 2, .triangle 6 0, .triangle 16 2, .triangle 23 2, .triangle 24 1]

-- Cycle fingerprint 16a128c9bdd81f0fd1382acc8bc919878a71328fcb4c69fe893b1087053c5903.
def localCycle00015 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 4, .distance 1 6, .distance 1 5, .distance 1 3, .distance 1 2, .theta 1, .distance 0 1]
    constant := ![-2, 0, 0, 0, -2, -1, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, true, false, false, false, false] }
  origin := ![.gapLower 1 5, .triangle 23 2, .triangle 24 1, .gapLower 1 2, .gapLower 1 1, .corridorLower 1 2, .corridorUpper 0 1]

-- Cycle fingerprint 172f29b856b0cef1a97a4e934dec3a3e6fce68f38e1453361c74982d73de68d9.
def localCycle00016 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 3 5, .distance 5 6, .distance 4 6, .distance 0 4, .distance 4 5, .distance 2 4, .distance 1 4, .theta 4]
    constant := ![3, 0, -1, 0, -1, -1, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 31 2, .triangle 33 0, .triangle 34 2, .triangle 13 0, .triangle 12 0, .triangle 28 0, .triangle 16 2, .gapLower 4 0]

-- Cycle fingerprint 17393648dc84c5cc1ec8dc3450cd525e64e54bfa8f1ee9266595d0e5f2874a23.
def localCycle00017 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 2, .theta 1, .distance 0 1, .distance 0 2, .distance 2 6, .distance 2 4, .distance 2 3, .distance 1 2]
    constant := ![-2, 3, 0, -1, 0, 0, -1]
    coefficient := ![0, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, true, false] }
  origin := ![.gapLower 1 0, .corridorUpper 0 1, .triangle 0 2, .triangle 8 0, .triangle 29 1, .triangle 25 1, .triangle 15 0]

-- Cycle fingerprint 179a23178912cf1459ee19d36a1b2aea640ec110c0ca68f480372d6b5b24861e.
def localCycle00018 : Cycle where
  length := 5
  data := {
    node := ![.distance 1 6, .distance 1 5, .theta 1, .distance 0 1, .distance 1 4, .distance 1 6]
    constant := ![-2, -1, 3, -2, 0]
    coefficient := ![0, 0, 1, 0, 0]
    strict := ![false, false, false, false, true] }
  origin := ![.gapLower 1 3, .corridorLower 1 5, .corridorUpper 0 1, .gapLower 1 5, .triangle 23 2]

-- Cycle fingerprint 195be1b48aa6290b889b664d65a2459be4f142f6536b3f7ef7e12d0a8923af58.
def localCycle00019 : Cycle where
  length := 4
  data := {
    node := ![.distance 0 1, .distance 1 6, .distance 1 5, .theta 1, .distance 0 1]
    constant := ![-2, -2, -1, 3]
    coefficient := ![0, 0, 0, 1]
    strict := ![false, false, false, false] }
  origin := ![.gapLower 1 5, .gapLower 1 4, .corridorLower 1 5, .corridorUpper 0 1]

-- Cycle fingerprint 1b09a3270b1c240ebfe9219642b0f0f310b3beb290020fc7a839629d609f8463.
def localCycle00020 : Cycle where
  length := 7
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 4, .distance 0 3, .distance 3 6, .distance 1 6, .distance 5 6, .theta 5]
    constant := ![3, -1, -1, -1, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 0, .triangle 9 0, .triangle 11 0, .triangle 21 2, .triangle 24 1, .corridorLower 5 6]

-- Cycle fingerprint 1b4315f4a9f6d6f352fca5fa0cdb1e1462af6701c7d2249cd744a9226bb96d95.
def localCycle00021 : Cycle where
  length := 5
  data := {
    node := ![.distance 1 4, .distance 1 5, .theta 1, .distance 0 1, .distance 1 6, .distance 1 4]
    constant := ![-2, -1, 3, -2, 0]
    coefficient := ![0, 0, 1, 0, 0]
    strict := ![false, false, false, false, true] }
  origin := ![.gapLower 1 3, .corridorLower 1 5, .corridorUpper 0 1, .gapLower 1 5, .triangle 23 1]

-- Cycle fingerprint 1c4222ca8bdbc79430f25e4b81cdc0b0a4a656ca04b0cf4f274f15a9d0e2096c.
def localCycle00022 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 2, .theta 1, .distance 0 1, .distance 0 2, .distance 0 4, .distance 0 5, .distance 5 6, .distance 2 5, .distance 2 3, .distance 1 2]
    constant := ![-1, 3, 0, 0, 0, -1, -1, 0, -1]
    coefficient := ![0, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, true, false, false, true, false] }
  origin := ![.corridorLower 1 2, .corridorUpper 0 1, .triangle 0 2, .triangle 6 2, .triangle 12 2, .triangle 14 0, .triangle 30 0, .triangle 26 1, .triangle 15 0]

-- Cycle fingerprint 1cffb72cbd2ded604879155f60093a9a997c6877c713e4e77a49179afc9f67fe.
def localCycle00023 : Cycle where
  length := 6
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 2, .distance 2 6, .distance 1 6, .distance 1 4, .theta 1]
    constant := ![3, 0, -1, 0, -3, -1]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false] }
  origin := ![.corridorUpper 0 1, .triangle 0 2, .triangle 8 0, .triangle 18 2, .gapLower 1 4, .corridorLower 1 4]

-- Cycle fingerprint 1d0a864c9006aa03b1169f6f7d8b9c6ca61f310f5e8395cfe52a59c47d81d37f.
def localCycle00024 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 2 5, .distance 1 5, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1, .distance 0 1]
    constant := ![0, -1, 0, 0, -2, 0, -2, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![true, false, true, true, false, true, false, false] }
  origin := ![.triangle 0 2, .triangle 7 0, .triangle 17 2, .triangle 22 1, .gapLower 1 2, .triangle 15 1, .gapLower 1 0, .corridorUpper 0 1]

-- Cycle fingerprint 1d4d64b608b0985d692b418256b8009f04f206700244ce15d1b44ce0a58145c1.
def localCycle00025 : Cycle where
  length := 7
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 2, .distance 2 5, .distance 1 5, .distance 1 4, .distance 1 3, .theta 1]
    constant := ![2, 0, -1, 0, 0, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, true, false, false] }
  origin := ![.gapLower 1 6, .triangle 0 2, .triangle 7 0, .triangle 17 2, .triangle 22 1, .gapLower 1 2, .corridorLower 1 3]

-- Cycle fingerprint 1eac609ad02760ae5cc15720379f2043faec8c4f6a09768875cb58bab308cd20.
def localCycle00026 : Cycle where
  length := 7
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 2, .distance 2 6, .distance 1 6, .distance 1 4, .distance 1 5, .theta 1]
    constant := ![2, 0, -1, 0, 0, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, true, false, false] }
  origin := ![.gapLower 1 6, .triangle 0 2, .triangle 8 0, .triangle 18 2, .triangle 23 1, .gapLower 1 3, .corridorLower 1 5]

-- Cycle fingerprint 2101307f1a7f4dca4e1344eea8f68cae270b45f06a59309d62a35f334c2936c7.
def localCycle00027 : Cycle where
  length := 7
  data := {
    node := ![.distance 2 3, .distance 1 2, .theta 1, .distance 0 1, .distance 0 2, .distance 2 5, .distance 2 4, .distance 2 3]
    constant := ![-1, -2, 3, 0, -1, 0, 0]
    coefficient := ![0, 0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true, true] }
  origin := ![.triangle 15 0, .gapLower 1 0, .corridorUpper 0 1, .triangle 0 2, .triangle 7 0, .triangle 28 1, .triangle 25 1]

-- Cycle fingerprint 22de68bb934a2c5f358587206f65b2decdefce93753414955002db9f5c850796.
def localCycle00028 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 4, .distance 1 3, .theta 1, .distance 0 1, .distance 0 2, .distance 2 5, .distance 1 5, .distance 1 4]
    constant := ![-3, -1, 3, 0, -1, 0, 0]
    coefficient := ![0, 0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true, true] }
  origin := ![.gapLower 1 2, .corridorLower 1 3, .corridorUpper 0 1, .triangle 0 2, .triangle 7 0, .triangle 17 2, .triangle 22 1]

-- Cycle fingerprint 2370e432f9e2b4c129d4f7e4744f7cc7c9c8f48f19d5832342020e687d8add5b.
def localCycle00029 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 6, .distance 1 5, .distance 1 3, .distance 1 2, .theta 1, .distance 0 1, .distance 0 2, .distance 2 4, .distance 1 4, .distance 1 6]
    constant := ![0, -2, -2, -1, 3, 0, -1, 0, 0]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0, 0]
    strict := ![true, false, false, false, false, true, false, true, true] }
  origin := ![.triangle 24 1, .gapLower 1 2, .gapLower 1 1, .corridorLower 1 2, .corridorUpper 0 1, .triangle 0 2, .triangle 6 0, .triangle 16 2, .triangle 23 2]

-- Cycle fingerprint 23bc5ab5326a0c6945e73a69e38cb5fa4b992481271ad0e0bf262fcdc20d46a7.
def localCycle00030 : Cycle where
  length := 9
  data := {
    node := ![.theta 1, .distance 0 1, .distance 1 5, .distance 5 6, .theta 5, .distance 4 5, .distance 3 4, .distance 2 3, .distance 1 2, .theta 1]
    constant := ![3, -3, -1, -1, 3, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false, false] }
  origin := ![.corridorUpper 0 1, .gapLower 1 5, .triangle 24 0, .corridorLower 5 6, .corridorUpper 4 5, .triangle 31 0, .triangle 25 0, .triangle 15 0, .corridorLower 1 2]

-- Cycle fingerprint 27f84542605637938a16876675a034e70a5c21c853e33ed52d8234032b5caf27.
def localCycle00031 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 2, .distance 0 4, .distance 4 5, .distance 5 6, .distance 2 6, .distance 0 2]
    constant := ![0, -1, -1, 0, 2]
    coefficient := ![0, 0, 0, 0, 0]
    strict := ![true, false, false, true, true] }
  origin := ![.triangle 6 2, .triangle 12 0, .triangle 34 0, .triangle 30 2, .gapUpper 2 5]

-- Cycle fingerprint 2a110720779616748d12458744723bf94a904daf4bfbc64411b40693c80682de.
def localCycle00032 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 5, .distance 1 6, .distance 1 4, .theta 1, .distance 0 1, .distance 0 2, .distance 2 5, .distance 1 5]
    constant := ![-2, -2, -1, 3, 0, -1, 0]
    coefficient := ![0, 0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, false, true, false, true] }
  origin := ![.gapLower 1 4, .gapLower 1 3, .corridorLower 1 4, .corridorUpper 0 1, .triangle 0 2, .triangle 7 0, .triangle 17 2]

-- Cycle fingerprint 2a2aa464ae5f52fd5d130c065f8ea5de01d9dfad9c2ec3fa08d35f89f35df88e.
def localCycle00033 : Cycle where
  length := 8
  data := {
    node := ![.distance 1 6, .distance 1 5, .distance 1 4, .distance 1 3, .theta 1, .distance 0 1, .distance 0 2, .distance 2 6, .distance 1 6]
    constant := ![0, 0, -2, -1, 2, 0, -1, 0]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![true, true, false, false, false, true, false, true] }
  origin := ![.triangle 24 1, .triangle 22 1, .gapLower 1 2, .corridorLower 1 3, .gapLower 1 6, .triangle 0 2, .triangle 8 0, .triangle 18 2]

-- Cycle fingerprint 2b50abe623bd812136d8283fc3e625dfd0bda6b41363fdb83326a661a4760bdb.
def localCycle00034 : Cycle where
  length := 8
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 2, .distance 2 6, .distance 1 6, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1]
    constant := ![3, 0, -1, 0, -2, 0, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, true, false, false] }
  origin := ![.corridorUpper 0 1, .triangle 0 2, .triangle 8 0, .triangle 18 2, .gapLower 1 4, .triangle 19 1, .gapLower 1 1, .corridorLower 1 2]

-- Cycle fingerprint 2e9c3c166c08a8e712c74701b0a0a7b1b816bf553b14675cff3583940a1db215.
def localCycle00035 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 0 3, .distance 3 4, .distance 2 4, .distance 1 2, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, 0, 0, -1, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, true, false, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 11 0, .triangle 9 0, .triangle 25 2, .triangle 16 0, .triangle 15 0, .corridorLower 2 3, .thetaLower 2]

-- Cycle fingerprint 2f1124a54bf45740fbeea5cac3addeefc3ea21d5c9d18f7aa99bd89b7645a019.
def localCycle00036 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 3 4, .distance 4 5, .distance 0 4, .distance 4 6, .distance 5 6, .theta 5, .theta 4]
    constant := ![3, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, true] }
  origin := ![.corridorUpper 3 4, .triangle 31 0, .triangle 12 0, .triangle 13 0, .triangle 34 1, .corridorLower 5 6, .thetaNext 4]

-- Cycle fingerprint 3028f31813391a0d38ea985b2b5d15d94fd8dd8ab4c5819ed0d0276c506be4fd.
def localCycle00037 : Cycle where
  length := 8
  data := {
    node := ![.theta 2, .distance 0 2, .distance 2 4, .distance 2 5, .distance 5 6, .distance 4 5, .theta 4, .theta 3, .theta 2]
    constant := ![3, -1, 0, -1, -1, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, true, true] }
  origin := ![.corridorUpper 0 2, .triangle 6 0, .triangle 28 2, .triangle 30 0, .triangle 34 0, .corridorLower 4 5, .thetaNext 3, .thetaNext 2]

-- Cycle fingerprint 31d8f18a9f3b7b35f39d8bf9a671f318770e696c15f8fb4a22fcd84b2e539249.
def localCycle00038 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 6, .distance 1 5, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1, .distance 0 1, .distance 0 2, .distance 2 6, .distance 1 6]
    constant := ![0, -3, 0, 0, -1, 3, 0, -1, 0]
    coefficient := ![0, 0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![true, false, true, true, false, false, true, false, true] }
  origin := ![.triangle 24 1, .gapLower 1 3, .triangle 19 1, .triangle 15 1, .corridorLower 1 2, .corridorUpper 0 1, .triangle 0 2, .triangle 8 0, .triangle 18 2]

-- Cycle fingerprint 32102fbabb7475ab08d5b38f4e49b13badb13c980a78fa198316ae8d33c65a03.
def localCycle00039 : Cycle where
  length := 8
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 2, .distance 2 6, .distance 1 6, .distance 1 4, .distance 1 5, .distance 1 3, .theta 1]
    constant := ![3, 0, -1, 0, -2, 0, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, true, false, false] }
  origin := ![.corridorUpper 0 1, .triangle 0 2, .triangle 8 0, .triangle 18 2, .gapLower 1 4, .triangle 22 2, .gapLower 1 2, .corridorLower 1 3]

-- Cycle fingerprint 33f4620e8aef4ceca4a87ad9e80fc284985cac02fbcf90f652019325e860b109.
def localCycle00040 : Cycle where
  length := 8
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 2, .distance 2 6, .distance 2 5, .distance 2 4, .distance 2 3, .distance 1 2, .theta 1]
    constant := ![3, 0, -1, 0, 0, 0, -1, -2]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, true, true, false, false] }
  origin := ![.corridorUpper 0 1, .triangle 0 2, .triangle 8 0, .triangle 30 1, .triangle 28 1, .triangle 25 1, .triangle 15 0, .gapLower 1 0]

-- Cycle fingerprint 36cbb4611e7a6d83d6980a533f1faaed5aab80979170aceca33e81e65ed776f3.
def localCycle00041 : Cycle where
  length := 13
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 0 3, .distance 3 4, .distance 4 5, .distance 2 5, .distance 1 2, .distance 2 4, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, 0, 0, -1, -1, -1, 0, -1, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, false, false, false, true, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 11 0, .triangle 9 0, .triangle 31 0, .gapLower 5 2, .triangle 17 0, .triangle 16 0, .triangle 25 1, .corridorLower 2 3, .thetaLower 2]

-- Cycle fingerprint 374bbed2ad2f7900de3582a237fb088bef34e804502959261f2f64a5f0125a0d.
def localCycle00042 : Cycle where
  length := 11
  data := {
    node := ![.theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 0 3, .distance 3 4, .distance 4 5, .distance 1 4, .distance 1 3, .theta 1, .zero, .theta 6]
    constant := ![3, 0, 0, -1, -1, -1, -1, 0, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, true, false, false, false, false, false, false, false, false] }
  origin := ![.corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 11 0, .triangle 9 0, .triangle 31 0, .triangle 22 0, .gapLower 1 1, .corridorLower 1 3, .thetaLower 1, .thetaUpper 6]

-- Cycle fingerprint 38338271d466ef156d821c7bca8dc8599ddcfddc15c6725d25f893853e0b4e60.
def localCycle00043 : Cycle where
  length := 10
  data := {
    node := ![.theta 1, .distance 0 1, .distance 1 6, .distance 1 2, .distance 1 3, .distance 1 4, .distance 4 5, .distance 3 4, .distance 2 3, .theta 2, .theta 1]
    constant := ![3, -1, 0, 0, 0, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, true, false, false, false, false, true] }
  origin := ![.corridorUpper 0 1, .triangle 4 0, .triangle 18 1, .triangle 15 2, .triangle 19 2, .triangle 22 0, .triangle 31 0, .triangle 25 0, .corridorLower 2 3, .thetaNext 1]

-- Cycle fingerprint 393a6b34c194ab0dac27b727b65cdb139dbd5e1fbf2309ae1ac5252375d0df23.
def localCycle00044 : Cycle where
  length := 8
  data := {
    node := ![.distance 1 5, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1, .distance 0 1, .distance 0 2, .distance 2 5, .distance 1 5]
    constant := ![0, 0, -2, -1, 2, 0, -1, 0]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![true, true, false, false, false, true, false, true] }
  origin := ![.triangle 22 1, .triangle 19 1, .gapLower 1 1, .corridorLower 1 2, .gapLower 1 6, .triangle 0 2, .triangle 7 0, .triangle 17 2]

-- Cycle fingerprint 3a589d55ed61a57380079fdc55942de31e5e00a6ce19f3fe9bb94efe51ebb83d.
def localCycle00045 : Cycle where
  length := 8
  data := {
    node := ![.distance 1 4, .distance 1 6, .distance 1 5, .distance 1 3, .theta 1, .distance 0 1, .distance 0 2, .distance 2 4, .distance 1 4]
    constant := ![0, 0, -2, -1, 2, 0, -1, 0]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![true, true, false, false, false, true, false, true] }
  origin := ![.triangle 23 2, .triangle 24 1, .gapLower 1 2, .corridorLower 1 3, .gapLower 1 6, .triangle 0 2, .triangle 6 0, .triangle 16 2]

-- Cycle fingerprint 3c18901d4f5112342afe61e1620eb572eace3472819777c6f38a5105a578d5ec.
def localCycle00046 : Cycle where
  length := 3
  data := {
    node := ![.distance 4 5, .distance 1 4, .distance 1 5, .distance 4 5]
    constant := ![2, -3, 0]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.gapUpper 4 1, .gapLower 1 3, .triangle 22 1]

-- Cycle fingerprint 3c4ca66acb6a2898bae2e4b711d847a04594933aa1fec47ac9299dd0808968d4.
def localCycle00047 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 0 3, .distance 3 4, .distance 1 4, .distance 4 5, .distance 2 4, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, 0, 0, -1, -1, 0, -1, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, true, false, false, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 11 0, .triangle 9 0, .triangle 19 2, .triangle 22 0, .triangle 28 0, .gapLower 2 1, .corridorLower 2 3, .thetaLower 2]

-- Cycle fingerprint 3e21ad345bca99a53f9f4b3cc33f7c411358268299908927b0cf661939f86301.
def localCycle00048 : Cycle where
  length := 7
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 2, .distance 2 6, .distance 1 6, .distance 1 5, .distance 1 4, .theta 1]
    constant := ![2, 0, -1, 0, 0, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, true, false, false] }
  origin := ![.gapLower 1 6, .triangle 0 2, .triangle 8 0, .triangle 18 2, .triangle 24 1, .gapLower 1 3, .corridorLower 1 4]

-- Cycle fingerprint 4420d97a13a0f4f732de50855315d6b3dc509e7eace1d836aa7564f477bc4e84.
def localCycle00049 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 2, .distance 2 5, .distance 1 5, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1, .distance 0 1, .distance 0 2]
    constant := ![-1, 0, 0, 0, -2, -2, 3, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 0]
    strict := ![false, true, true, true, false, false, false, true] }
  origin := ![.triangle 7 0, .triangle 17 2, .triangle 22 1, .triangle 19 1, .gapLower 1 1, .gapLower 1 0, .corridorUpper 0 1, .triangle 0 2]

-- Cycle fingerprint 450232b5fe6cf6f12f4eba1a67c64d43270263875b4240d85528182de73cc786.
def localCycle00050 : Cycle where
  length := 8
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 2, .distance 2 4, .distance 1 4, .distance 1 6, .distance 1 5, .distance 1 3, .theta 1]
    constant := ![3, 0, -1, 0, -2, 0, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, true, false, false] }
  origin := ![.corridorUpper 0 1, .triangle 0 2, .triangle 6 0, .triangle 16 2, .gapLower 1 4, .triangle 24 1, .gapLower 1 2, .corridorLower 1 3]

-- Cycle fingerprint 4aa3c57f0e639f7ad36a1bed8ac5a07dc26277cabfe3f2b3b2522e6d551180e0.
def localCycle00051 : Cycle where
  length := 10
  data := {
    node := ![.theta 1, .distance 0 1, .distance 1 6, .distance 1 2, .distance 1 3, .distance 3 5, .distance 2 3, .distance 3 4, .theta 3, .theta 2, .theta 1]
    constant := ![3, -1, 0, 0, -1, -1, -1, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, false, true, true] }
  origin := ![.corridorUpper 0 1, .triangle 4 0, .triangle 18 1, .triangle 15 2, .triangle 20 0, .triangle 26 0, .triangle 25 0, .corridorLower 3 4, .thetaNext 2, .thetaNext 1]

-- Cycle fingerprint 4bde736700ea04375d0f8f8fabf561164fc373e4870c432f67ea556505fe7fdc.
def localCycle00052 : Cycle where
  length := 10
  data := {
    node := ![.theta 1, .distance 0 1, .distance 1 6, .distance 1 2, .distance 1 3, .distance 3 4, .distance 2 3, .distance 3 5, .theta 3, .theta 2, .theta 1]
    constant := ![3, -1, 0, 0, -1, -1, -1, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, false, true, true] }
  origin := ![.corridorUpper 0 1, .triangle 4 0, .triangle 18 1, .triangle 15 2, .triangle 19 0, .triangle 25 0, .triangle 26 0, .corridorLower 3 5, .thetaNext 2, .thetaNext 1]

-- Cycle fingerprint 4d37c11475d3a0a263de528842841228c03370a20011ab0869f6ca0210432159.
def localCycle00053 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 2 5, .distance 1 5, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1, .distance 0 1]
    constant := ![0, -1, 0, 0, -2, -2, -1, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![true, false, true, true, false, false, false, false] }
  origin := ![.triangle 0 2, .triangle 7 0, .triangle 17 2, .triangle 22 1, .gapLower 1 2, .gapLower 1 1, .corridorLower 1 2, .corridorUpper 0 1]

-- Cycle fingerprint 4d89bed07a72fb14790cc023207e0a8502016736fe276548398a44549b2a4128.
def localCycle00054 : Cycle where
  length := 9
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 2, .distance 0 4, .distance 4 5, .distance 5 6, .distance 2 5, .distance 2 4, .distance 1 2, .theta 1]
    constant := ![3, 0, 0, -1, -1, -1, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, false, false, false, false] }
  origin := ![.corridorUpper 0 1, .triangle 0 2, .triangle 6 2, .triangle 12 0, .triangle 34 0, .triangle 30 0, .gapLower 2 3, .triangle 16 0, .corridorLower 1 2]

-- Cycle fingerprint 4d954c80e7fbf6a38ea0b1d85b4b76f6d424ba6beceaf761e6e88892f736df8c.
def localCycle00055 : Cycle where
  length := 13
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 0 3, .distance 3 4, .distance 2 4, .distance 1 2, .distance 2 3, .distance 3 5, .distance 4 5, .theta 4, .zero]
    constant := ![0, 3, 0, 0, -1, -1, 0, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, true, false, false, false, true, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 11 0, .triangle 9 0, .triangle 25 2, .triangle 16 0, .triangle 15 0, .triangle 26 0, .triangle 31 1, .corridorLower 4 5, .thetaLower 4]

-- Cycle fingerprint 4e6d1a6cb856d88087fec130a7d816d178f93a7cb2fdc7ef82e62362cfc3925a.
def localCycle00056 : Cycle where
  length := 8
  data := {
    node := ![.distance 2 5, .distance 2 4, .distance 2 3, .distance 1 2, .theta 1, .distance 0 1, .distance 0 2, .distance 2 6, .distance 2 5]
    constant := ![0, 0, -1, -1, 2, 0, -1, 0]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![true, true, false, false, false, true, false, true] }
  origin := ![.triangle 28 1, .triangle 25 1, .triangle 15 0, .corridorLower 1 2, .gapLower 1 6, .triangle 0 2, .triangle 8 0, .triangle 30 1]

-- Cycle fingerprint 5161d4292b8fe5cdc088bc6f7b790eefec1a186719791d8dedcef803f7a7b4ba.
def localCycle00057 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 4 5, .distance 5 6, .distance 2 5, .distance 2 4, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, -1, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 31 0, .triangle 34 0, .triangle 30 0, .gapLower 2 3, .triangle 16 0, .corridorLower 1 2, .thetaLower 1]

-- Cycle fingerprint 519539146e6fd0083fa734a84df20cb32ac824c4e4d4a524360e855495af9b76.
def localCycle00058 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .distance 2 4, .distance 1 4, .distance 1 6, .theta 1, .distance 0 1, .distance 0 2]
    constant := ![-1, 0, -2, -1, 2, 0]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![false, true, false, false, false, true] }
  origin := ![.triangle 6 0, .triangle 16 2, .gapLower 1 4, .corridorLower 1 6, .gapLower 1 6, .triangle 0 2]

-- Cycle fingerprint 52c07b7ee57c6d3019a862bc5d47d75340899c8440f87fd9d1db356a7d7515bc.
def localCycle00059 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 2 6, .distance 1 6, .distance 1 4, .distance 1 5, .distance 1 3, .theta 1, .distance 0 1]
    constant := ![0, -1, 0, 0, -2, -2, -1, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![true, false, true, true, false, false, false, false] }
  origin := ![.triangle 0 2, .triangle 8 0, .triangle 18 2, .triangle 23 1, .gapLower 1 3, .gapLower 1 2, .corridorLower 1 3, .corridorUpper 0 1]

-- Cycle fingerprint 53f540f5e6eef263af6d91d7edcd2dc8bb7cf3f9a4682c4c3a8a3f9475519b8f.
def localCycle00060 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 4, .distance 4 5, .distance 0 4, .distance 2 4, .distance 1 2, .theta 1, .theta 0, .zero]
    constant := ![0, 3, 0, -1, -1, -1, 0, -1, -1, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, true, false, false, true, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 0, .triangle 31 0, .triangle 12 0, .triangle 6 1, .triangle 16 0, .corridorLower 1 2, .thetaNext 0, .thetaLower 0]

-- Cycle fingerprint 55057025060d5ac4c6c31c2a5a6ea79aae74337f45794c0a59916b362743966a.
def localCycle00061 : Cycle where
  length := 8
  data := {
    node := ![.distance 1 6, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1, .distance 0 1, .distance 0 2, .distance 2 6, .distance 1 6]
    constant := ![0, 0, -2, -1, 2, 0, -1, 0]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![true, true, false, false, false, true, false, true] }
  origin := ![.triangle 23 1, .triangle 19 1, .gapLower 1 1, .corridorLower 1 2, .gapLower 1 6, .triangle 0 2, .triangle 8 0, .triangle 18 2]

-- Cycle fingerprint 5633ceceddcd09f1c0bfd8a99da0b388eec178550c105f39d68e043017d7fe2b.
def localCycle00062 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 4 5, .distance 5 6, .distance 0 5, .distance 2 5, .distance 2 4, .distance 2 3, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, -1, -1, -1, 0, 0, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, true, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 31 0, .triangle 34 0, .triangle 14 0, .triangle 7 1, .triangle 28 1, .triangle 25 1, .triangle 15 0, .corridorLower 1 2, .thetaLower 1]

-- Cycle fingerprint 566ca708274d902bf7ad6c897350c9584bcdf3bb2a2ad053d05a4aeb99d63ffe.
def localCycle00063 : Cycle where
  length := 8
  data := {
    node := ![.theta 2, .distance 0 2, .distance 2 4, .distance 4 6, .distance 1 4, .distance 4 5, .theta 4, .theta 3, .theta 2]
    constant := ![3, -1, -1, -1, -1, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, true] }
  origin := ![.corridorUpper 0 2, .triangle 6 0, .triangle 29 0, .triangle 23 0, .triangle 22 0, .corridorLower 4 5, .thetaNext 3, .thetaNext 2]

-- Cycle fingerprint 576d962427400cf5091aed23f5ba70acd0686af985769188d7e701c2c9ca11ca.
def localCycle00064 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 4 5, .distance 0 4, .distance 0 3, .distance 3 6, .distance 2 3, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, -1, -1, 0, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 31 0, .triangle 12 0, .triangle 9 1, .triangle 11 0, .triangle 27 0, .triangle 15 0, .corridorLower 1 2, .thetaLower 1]

-- Cycle fingerprint 57e116fb4946ca29596ca8d61682c97d467cb6469828953cdc947a04a5ff70ad.
def localCycle00065 : Cycle where
  length := 5
  data := {
    node := ![.distance 1 4, .distance 1 3, .theta 1, .distance 0 1, .distance 1 5, .distance 1 4]
    constant := ![-2, -1, 3, -2, 0]
    coefficient := ![0, 0, 1, 0, 0]
    strict := ![false, false, false, false, true] }
  origin := ![.gapLower 1 2, .corridorLower 1 3, .corridorUpper 0 1, .gapLower 1 5, .triangle 22 1]

-- Cycle fingerprint 57e20394d9642596f11ea0b5f95feb6f0fbf271708ee1bbcd464e51dfd62abcd.
def localCycle00066 : Cycle where
  length := 9
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 2, .distance 2 6, .distance 2 4, .distance 4 5, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1]
    constant := ![3, 0, -1, 0, -1, -1, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, true, true, false] }
  origin := ![.corridorUpper 0 1, .triangle 0 2, .triangle 8 0, .triangle 29 1, .triangle 28 0, .triangle 22 0, .triangle 19 1, .triangle 15 1, .corridorLower 1 2]

-- Cycle fingerprint 5849fc11d6efdc159143a7bcd74a7e54100fabe03fa821a442013f40cc731c77.
def localCycle00067 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 6, .distance 1 5, .distance 1 4, .theta 1, .distance 0 1, .distance 0 2, .distance 2 6, .distance 1 6]
    constant := ![-2, -2, -1, 3, 0, -1, 0]
    coefficient := ![0, 0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, false, true, false, true] }
  origin := ![.gapLower 1 4, .gapLower 1 3, .corridorLower 1 4, .corridorUpper 0 1, .triangle 0 2, .triangle 8 0, .triangle 18 2]

-- Cycle fingerprint 5a28d79874061aa88c97bb8cfb69957fd192b0ba3bcd40830a8ac0da13553ac0.
def localCycle00068 : Cycle where
  length := 4
  data := {
    node := ![.distance 0 1, .distance 1 4, .distance 1 6, .theta 1, .distance 0 1]
    constant := ![-2, -2, -1, 3]
    coefficient := ![0, 0, 0, 1]
    strict := ![false, false, false, false] }
  origin := ![.gapLower 1 5, .gapLower 1 4, .corridorLower 1 6, .corridorUpper 0 1]

-- Cycle fingerprint 5beefed54fde0d5502626bda2dab9d68af06945cb6d55de73c3b1accaa20b476.
def localCycle00069 : Cycle where
  length := 6
  data := {
    node := ![.theta 4, .distance 3 4, .distance 4 5, .distance 0 4, .distance 4 6, .distance 1 4, .theta 4]
    constant := ![3, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 31 0, .triangle 12 0, .triangle 13 0, .triangle 23 0, .gapLower 4 0]

-- Cycle fingerprint 5c7fe771329da80dfeb5c4c9d9507b70b7ef0675de1e92a8de1daab88a54160a.
def localCycle00070 : Cycle where
  length := 8
  data := {
    node := ![.distance 2 5, .distance 2 4, .distance 2 3, .distance 1 2, .theta 1, .distance 0 1, .distance 0 2, .distance 2 6, .distance 2 5]
    constant := ![0, 0, -1, -2, 2, 0, -1, 0]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![true, true, false, false, false, true, false, true] }
  origin := ![.triangle 28 1, .triangle 25 1, .triangle 15 0, .gapLower 1 0, .gapLower 1 6, .triangle 0 2, .triangle 8 0, .triangle 30 1]

-- Cycle fingerprint 5c96f37054b7bac940bc67395f93a0343906f24aef0015b313d6ef0038777f6e.
def localCycle00071 : Cycle where
  length := 5
  data := {
    node := ![.distance 1 5, .distance 1 4, .theta 1, .distance 0 1, .distance 1 6, .distance 1 5]
    constant := ![-2, -1, 3, -2, 0]
    coefficient := ![0, 0, 1, 0, 0]
    strict := ![false, false, false, false, true] }
  origin := ![.gapLower 1 3, .corridorLower 1 4, .corridorUpper 0 1, .gapLower 1 5, .triangle 24 1]

-- Cycle fingerprint 5d9f08c0314d933682900c2a508ddcf3c97fa5dd0b49a1da5d69da7ca563dadb.
def localCycle00072 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 0 4, .distance 4 5, .distance 3 4, .distance 1 3, .theta 1, .zero]
    constant := ![0, 3, 0, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 13 0, .triangle 12 0, .triangle 31 0, .triangle 19 0, .corridorLower 1 3, .thetaLower 1]

-- Cycle fingerprint 5e0156005fa42c242ecd311f0a384ac534b79fa3b2a28ee3a4c9827d252f4e59.
def localCycle00073 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 0 2, .distance 2 4, .distance 1 4, .distance 1 5, .distance 5 6, .distance 4 5, .theta 4, .theta 3, .theta 2]
    constant := ![3, -1, 0, 0, -1, -1, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, true, true] }
  origin := ![.corridorUpper 0 2, .triangle 6 0, .triangle 16 2, .triangle 22 2, .triangle 24 0, .triangle 34 0, .corridorLower 4 5, .thetaNext 3, .thetaNext 2]

-- Cycle fingerprint 5f97bd3dcb8dd18a69bef3087248e6e59dd94e6849e7d939fabe55be0326354f.
def localCycle00074 : Cycle where
  length := 13
  data := {
    node := ![.distance 3 4, .distance 2 4, .distance 4 5, .distance 1 4, .distance 1 2, .distance 2 3, .theta 2, .zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 0 3, .distance 3 4]
    constant := ![0, -1, -1, 0, -1, -1, 0, 0, 3, 0, 0, -1, -1]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![true, false, false, false, false, false, false, false, false, true, true, false, false] }
  origin := ![.triangle 25 2, .triangle 28 0, .triangle 22 0, .gapLower 1 2, .triangle 15 0, .corridorLower 2 3, .thetaLower 2, .thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 11 0, .triangle 9 0]

-- Cycle fingerprint 60130e2e044633709a88c8fbe1354f5225a95f64fb7b5353de3b0f32ab8e4aec.
def localCycle00075 : Cycle where
  length := 9
  data := {
    node := ![.theta 1, .distance 0 1, .distance 1 6, .distance 1 2, .distance 2 3, .distance 3 5, .distance 3 4, .theta 3, .theta 2, .theta 1]
    constant := ![3, -1, 0, -1, -1, 0, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, false, true, true] }
  origin := ![.corridorUpper 0 1, .triangle 4 0, .triangle 18 1, .triangle 15 0, .triangle 26 0, .triangle 31 1, .corridorLower 3 4, .thetaNext 2, .thetaNext 1]

-- Cycle fingerprint 60e3ec789b00594c11024d6d220b26a318d55e1b907b4a52caf99d358a58c222.
def localCycle00076 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 5, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1, .distance 0 1, .distance 0 2, .distance 2 6, .distance 1 6, .distance 1 5]
    constant := ![0, -2, -2, -1, 3, 0, -1, 0, 0]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0, 0]
    strict := ![true, false, false, false, false, true, false, true, true] }
  origin := ![.triangle 22 1, .gapLower 1 2, .gapLower 1 1, .corridorLower 1 2, .corridorUpper 0 1, .triangle 0 2, .triangle 8 0, .triangle 18 2, .triangle 24 1]

-- Cycle fingerprint 61da6197eeb68f92257cf56460ad017a58fde63a8d31ea6d5654fef330fea63f.
def localCycle00077 : Cycle where
  length := 12
  data := {
    node := ![.distance 2 4, .distance 2 3, .distance 1 2, .theta 1, .distance 0 1, .distance 1 5, .distance 5 6, .theta 5, .theta 4, .distance 3 4, .distance 4 5, .distance 4 6, .distance 2 4]
    constant := ![0, -1, -2, 3, -2, -1, -1, 0, 3, -1, 0, -1]
    coefficient := ![0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, true, false, false, true, false] }
  origin := ![.gapLower 2 2, .triangle 15 0, .gapLower 1 0, .corridorUpper 0 1, .gapLower 1 5, .triangle 24 0, .corridorLower 5 6, .thetaNext 4, .corridorUpper 3 4, .triangle 31 0, .triangle 34 2, .triangle 29 0]

-- Cycle fingerprint 61f70ea4d54e8e4dbb27bbd969a5912763934dbcf56fac9f26529a8c81d09646.
def localCycle00078 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 2, .distance 2 4, .distance 2 6, .distance 2 5, .distance 2 3, .distance 1 2, .theta 1, .distance 0 1, .distance 0 2]
    constant := ![-1, 0, 0, 0, -1, -2, 3, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 0]
    strict := ![false, true, true, false, false, false, false, true] }
  origin := ![.triangle 6 0, .triangle 29 2, .triangle 30 1, .gapLower 2 2, .triangle 15 0, .gapLower 1 0, .corridorUpper 0 1, .triangle 0 2]

-- Cycle fingerprint 627bc692b12051cb442ef9a5affa3ce2e825f868658afbdd0f6a76606d851455.
def localCycle00079 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 0 3, .distance 3 4, .distance 1 3, .distance 3 5, .distance 4 5, .theta 4, .zero]
    constant := ![0, 3, 0, 0, -1, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, false, true, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 11 0, .triangle 9 0, .triangle 19 0, .triangle 20 0, .triangle 31 1, .corridorLower 4 5, .thetaLower 4]

-- Cycle fingerprint 639d2685f3744fc8ed6697bd1deaf9cba7b840ea29443a2d645fbf7591ca317a.
def localCycle00080 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 5, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1, .distance 0 1, .distance 0 2, .distance 2 6, .distance 1 6, .distance 1 5]
    constant := ![0, -2, 0, -2, 3, 0, -1, 0, 0]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0, 0]
    strict := ![true, false, true, false, false, true, false, true, true] }
  origin := ![.triangle 22 1, .gapLower 1 2, .triangle 15 1, .gapLower 1 0, .corridorUpper 0 1, .triangle 0 2, .triangle 8 0, .triangle 18 2, .triangle 24 1]

-- Cycle fingerprint 667baf25244995362af15c5603b6ddfb097cc0a30f70743133540e32494228e3.
def localCycle00081 : Cycle where
  length := 8
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 2, .distance 2 4, .distance 1 4, .distance 1 6, .distance 1 3, .distance 1 2, .theta 1]
    constant := ![3, 0, -1, 0, -2, 0, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, true, false, false] }
  origin := ![.corridorUpper 0 1, .triangle 0 2, .triangle 6 0, .triangle 16 2, .gapLower 1 4, .triangle 21 1, .gapLower 1 1, .corridorLower 1 2]

-- Cycle fingerprint 66b3bb19ec76d7fb6d9c86ccc110e3afd4b6ca60bf79b0886a44ef73df2311d3.
def localCycle00082 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 2, .distance 2 4, .distance 4 5, .distance 5 6, .distance 1 5, .distance 1 4, .theta 1, .distance 0 1, .distance 0 2]
    constant := ![-1, -1, -1, -1, 0, -1, 3, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 0]
    strict := ![false, false, false, false, false, false, false, true] }
  origin := ![.triangle 6 0, .triangle 28 0, .triangle 34 0, .triangle 24 0, .gapLower 1 3, .corridorLower 1 4, .corridorUpper 0 1, .triangle 0 2]

-- Cycle fingerprint 6766bc97d2e2ff0b74a706039e727a4d111b1f3c57910531c77f922ccece51c3.
def localCycle00083 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 4, .distance 4 6, .distance 0 4, .distance 2 4, .distance 2 3, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, -1, -1, -1, 0, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 0, .triangle 32 0, .triangle 13 0, .triangle 6 1, .triangle 25 1, .triangle 15 0, .corridorLower 1 2, .thetaLower 1]

-- Cycle fingerprint 6a98de280c61d8fa382711845c76068fc289133bbaeae63e1f982d5796956fd1.
def localCycle00084 : Cycle where
  length := 10
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 2, .distance 0 4, .distance 4 5, .distance 2 4, .distance 4 6, .distance 5 6, .distance 1 5, .distance 1 4, .theta 1]
    constant := ![3, 0, 0, -1, -1, -1, 0, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, false, true, false, false, false] }
  origin := ![.corridorUpper 0 1, .triangle 0 2, .triangle 6 2, .triangle 12 0, .triangle 28 0, .triangle 29 0, .triangle 34 1, .triangle 24 0, .gapLower 1 3, .corridorLower 1 4]

-- Cycle fingerprint 6aa5f7c0266cab4e9a540932c26db7c5e2c6eec1c1415cef34bf351e0b1af48d.
def localCycle00085 : Cycle where
  length := 7
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 2, .distance 2 6, .distance 2 4, .distance 2 3, .distance 1 2, .theta 1]
    constant := ![2, 0, -1, 0, 0, -1, -2]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, true, false, false] }
  origin := ![.gapLower 1 6, .triangle 0 2, .triangle 8 0, .triangle 29 1, .triangle 25 1, .triangle 15 0, .gapLower 1 0]

-- Cycle fingerprint 7259d913abf72cf39e13ef91f091ddc0e73ba3cfbd4c0a36d2bd31fc9ebc02a4.
def localCycle00086 : Cycle where
  length := 3
  data := {
    node := ![.distance 5 6, .distance 1 5, .distance 1 6, .distance 5 6]
    constant := ![2, -3, 0]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.gapUpper 5 1, .gapLower 1 4, .triangle 24 1]

-- Cycle fingerprint 72f1031ec284c9473da8b95975c5603a47367e29b869ec99f15b7cf42b5dfe2a.
def localCycle00087 : Cycle where
  length := 4
  data := {
    node := ![.distance 0 1, .distance 1 6, .distance 1 4, .theta 1, .distance 0 1]
    constant := ![-2, -2, -1, 3]
    coefficient := ![0, 0, 0, 1]
    strict := ![false, false, false, false] }
  origin := ![.gapLower 1 5, .gapLower 1 4, .corridorLower 1 4, .corridorUpper 0 1]

-- Cycle fingerprint 74dbc92ec2673a69918c90ed9af0057bfe19d63df955775d89018399ddf95494.
def localCycle00088 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 4, .distance 1 6, .distance 1 5, .theta 1, .distance 0 1, .distance 0 2, .distance 2 4, .distance 1 4]
    constant := ![-2, -2, -1, 3, 0, -1, 0]
    coefficient := ![0, 0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, false, true, false, true] }
  origin := ![.gapLower 1 4, .gapLower 1 3, .corridorLower 1 5, .corridorUpper 0 1, .triangle 0 2, .triangle 6 0, .triangle 16 2]

-- Cycle fingerprint 75c13f0efb25878df53e968b7e55d9a5f91699decedf22bd5a8b8374ae8ee1a8.
def localCycle00089 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 2, .theta 1, .distance 0 1, .distance 0 2, .distance 2 6, .distance 2 4, .distance 2 3, .distance 1 2]
    constant := ![-3, 3, 0, -1, 0, 0, -1]
    coefficient := ![0, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, true, false] }
  origin := ![.gapLower 1 0, .corridorUpper 0 1, .triangle 0 2, .triangle 8 0, .triangle 29 1, .triangle 25 1, .triangle 15 0]

-- Cycle fingerprint 760087c8cbbe80ac4ca6cf172c0ecf30b4253e9380bf69e6e84203cce767be7f.
def localCycle00090 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 5, .distance 1 4, .theta 1, .distance 0 1, .distance 0 2, .distance 2 6, .distance 1 6, .distance 1 5]
    constant := ![-3, -1, 3, 0, -1, 0, 0]
    coefficient := ![0, 0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true, true] }
  origin := ![.gapLower 1 3, .corridorLower 1 4, .corridorUpper 0 1, .triangle 0 2, .triangle 8 0, .triangle 18 2, .triangle 24 1]

-- Cycle fingerprint 78ed3490cf7fe4e0254c1420b2ef5394fe5a2f45ebdc064e88e2358231dcfdf9.
def localCycle00091 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 6, .distance 1 5, .distance 1 3, .distance 1 2, .theta 1, .distance 0 1, .distance 0 2, .distance 2 4, .distance 1 4, .distance 1 6]
    constant := ![0, -2, 0, -2, 3, 0, -1, 0, 0]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0, 0]
    strict := ![true, false, true, false, false, true, false, true, true] }
  origin := ![.triangle 24 1, .gapLower 1 2, .triangle 15 1, .gapLower 1 0, .corridorUpper 0 1, .triangle 0 2, .triangle 6 0, .triangle 16 2, .triangle 23 2]

-- Cycle fingerprint 7a599a3c8311138c10d39ace607bfd4f1c70996723136750febcec32882724cb.
def localCycle00092 : Cycle where
  length := 8
  data := {
    node := ![.distance 4 5, .theta 4, .theta 3, .theta 2, .theta 1, .distance 0 1, .distance 1 4, .distance 4 6, .distance 4 5]
    constant := ![-1, 0, 0, 0, 2, -2, -1, 0]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![false, true, true, true, false, false, false, true] }
  origin := ![.corridorLower 4 5, .thetaNext 3, .thetaNext 2, .thetaNext 1, .gapLower 1 6, .gapLower 1 5, .triangle 23 0, .triangle 34 1]

-- Cycle fingerprint 7a5e31c1e81389574b07636d5fbc79490aea53f852d38e9b02a61e33a3d282c1.
def localCycle00093 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 4, .distance 0 4, .distance 4 6, .distance 2 4, .distance 2 3, .distance 1 2, .theta 1, .theta 0, .zero]
    constant := ![0, 3, -1, 0, -1, -1, 0, -1, -1, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, true, false, false, true, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 0, .triangle 9 2, .triangle 13 0, .triangle 29 0, .triangle 25 1, .triangle 15 0, .corridorLower 1 2, .thetaNext 0, .thetaLower 0]

-- Cycle fingerprint 7d50b76743e9302753b55e2222601712133923a3384a99c682dbbb3f5bb80af0.
def localCycle00094 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 4, .distance 4 6, .distance 5 6, .distance 2 5, .distance 2 4, .distance 2 3, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, -1, -1, 0, -1, 0, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 0, .triangle 32 0, .triangle 34 1, .triangle 30 0, .gapLower 2 3, .gapLower 2 2, .triangle 15 0, .corridorLower 1 2, .thetaLower 1]

-- Cycle fingerprint 805575bf04ab22e633974b9888a2d7c3c1d414542f559f9dee6882810c0614eb.
def localCycle00095 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 0 2, .distance 2 4, .distance 4 5, .distance 1 5, .distance 5 6, .theta 5, .theta 4, .theta 3, .theta 2]
    constant := ![3, -1, -1, 0, -1, -1, 0, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, true, true, true] }
  origin := ![.corridorUpper 0 2, .triangle 6 0, .triangle 28 0, .triangle 22 2, .triangle 24 0, .corridorLower 5 6, .thetaNext 4, .thetaNext 3, .thetaNext 2]

-- Cycle fingerprint 81343619877afd78519b3e008fa7e9c90ef43e615d6f22cbdb27312077535758.
def localCycle00096 : Cycle where
  length := 9
  data := {
    node := ![.theta 1, .distance 0 1, .distance 1 5, .distance 5 6, .theta 5, .distance 4 5, .distance 3 4, .distance 2 3, .distance 1 2, .theta 1]
    constant := ![3, -2, -1, -1, 3, -1, -1, -1, -2]
    coefficient := ![1, 0, 0, 0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false, false] }
  origin := ![.corridorUpper 0 1, .gapLower 1 5, .triangle 24 0, .corridorLower 5 6, .corridorUpper 4 5, .triangle 31 0, .triangle 25 0, .triangle 15 0, .gapLower 1 0]

-- Cycle fingerprint 81427d2c78f03357e25cb8b2c043c7a1e3b435cde1d8656cc1b5fb9f6de8aae7.
def localCycle00097 : Cycle where
  length := 3
  data := {
    node := ![.theta 1, .distance 0 1, .distance 1 4, .theta 1]
    constant := ![3, -3, -1]
    coefficient := ![1, 0, 0]
    strict := ![false, false, false] }
  origin := ![.corridorUpper 0 1, .gapLower 1 5, .corridorLower 1 4]

-- Cycle fingerprint 837f6163c5d8f86a5359371d9d89767b6cb7e72477c5c8308e4876169137e183.
def localCycle00098 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 4, .distance 1 3, .theta 1, .distance 0 1, .distance 0 2, .distance 0 4, .distance 4 5, .distance 2 4, .distance 4 6, .distance 1 4]
    constant := ![0, -1, 3, 0, 0, -1, -1, -1, -1]
    coefficient := ![0, 0, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false, false, false, false] }
  origin := ![.gapLower 1 2, .corridorLower 1 3, .corridorUpper 0 1, .triangle 0 2, .triangle 6 2, .triangle 12 0, .triangle 28 0, .triangle 29 0, .triangle 23 0]

-- Cycle fingerprint 83e17d21aa9bb7b9ed7d0e0304970b2cd9beed6a89ec3bcad2bfd03c413e5f81.
def localCycle00099 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 3 5, .distance 5 6, .distance 4 5, .distance 2 4, .distance 2 3, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, 0, -1, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 31 2, .triangle 33 0, .triangle 34 0, .triangle 28 0, .gapLower 2 2, .triangle 15 0, .corridorLower 1 2, .thetaLower 1]

-- Cycle fingerprint 8641ba6f8cc8c8b39f8cbc03c1091d0206d7e052790d33206262bf356ff24322.
def localCycle00100 : Cycle where
  length := 5
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 4, .distance 3 6, .theta 6, .theta 5]
    constant := ![3, -1, 0, -2, 0]
    coefficient := ![1, 0, 0, -1, 0]
    strict := ![false, false, true, true, true] }
  origin := ![.corridorUpper 4 5, .triangle 31 0, .triangle 32 2, .gapUpper 6 6, .thetaNext 5]

-- Cycle fingerprint 86bef04538bb77a1fcd2dc42b2226703e9269b3a876a8a89aa4047fd85954e1b.
def localCycle00101 : Cycle where
  length := 5
  data := {
    node := ![.theta 4, .distance 3 4, .distance 4 5, .distance 0 4, .distance 4 6, .theta 4]
    constant := ![3, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 31 0, .triangle 12 0, .triangle 13 0, .corridorLower 4 6]

-- Cycle fingerprint 876b495898da0aee2667ebb8d9211a01d6fe1b6488556d6d590a4fcfb4c27ba6.
def localCycle00102 : Cycle where
  length := 5
  data := {
    node := ![.distance 1 3, .distance 1 2, .theta 1, .distance 0 1, .distance 1 5, .distance 1 3]
    constant := ![-2, -1, 3, -2, 0]
    coefficient := ![0, 0, 1, 0, 0]
    strict := ![false, false, false, false, true] }
  origin := ![.gapLower 1 1, .corridorLower 1 2, .corridorUpper 0 1, .gapLower 1 5, .triangle 20 1]

-- Cycle fingerprint 89091e365020fc67a57526bd2c04e39a5807df70f578eaaa419f8bf8fc3ee543.
def localCycle00103 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 4, .distance 1 3, .distance 1 2, .theta 1, .distance 0 1, .distance 0 2, .distance 2 4, .distance 4 6, .distance 4 5, .distance 1 4]
    constant := ![0, 0, -1, 3, 0, -1, -1, 0, -1]
    coefficient := ![0, 0, 0, 1, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, false, false, true, false] }
  origin := ![.gapLower 1 2, .triangle 15 1, .corridorLower 1 2, .corridorUpper 0 1, .triangle 0 2, .triangle 6 0, .triangle 29 0, .triangle 34 1, .triangle 22 0]

-- Cycle fingerprint 8ba46946a4a9d3a8391a7a4039f067974bdbda1308efa0e0c5ed5d6caa605d68.
def localCycle00104 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 4, .distance 1 5, .distance 1 3, .distance 1 2, .theta 1, .distance 0 1, .distance 0 2, .distance 2 6, .distance 1 6, .distance 1 4]
    constant := ![0, -3, 0, -1, 3, 0, -1, 0, 0]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0, 0]
    strict := ![true, false, true, false, false, true, false, true, true] }
  origin := ![.triangle 22 2, .gapLower 1 2, .triangle 15 1, .corridorLower 1 2, .corridorUpper 0 1, .triangle 0 2, .triangle 8 0, .triangle 18 2, .triangle 23 1]

-- Cycle fingerprint 8d7948d62f5435508a90615113c0c2c8d08ef068545daee039f8b7be4f5c1f8f.
def localCycle00105 : Cycle where
  length := 8
  data := {
    node := ![.distance 2 6, .distance 2 5, .distance 2 3, .distance 1 2, .theta 1, .distance 0 1, .distance 0 2, .distance 2 4, .distance 2 6]
    constant := ![0, 0, -1, -1, 2, 0, -1, 0]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![true, false, false, false, false, true, false, true] }
  origin := ![.triangle 30 1, .gapLower 2 2, .triangle 15 0, .corridorLower 1 2, .gapLower 1 6, .triangle 0 2, .triangle 6 0, .triangle 29 2]

-- Cycle fingerprint 8e335c0c478952d41d15f46784d622262f15a7d3f708fa3a6adba6a47e9373bf.
def localCycle00106 : Cycle where
  length := 7
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 2, .distance 2 6, .distance 2 4, .distance 2 3, .distance 1 2, .theta 1]
    constant := ![2, 0, -1, 0, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, true, false, false] }
  origin := ![.gapLower 1 6, .triangle 0 2, .triangle 8 0, .triangle 29 1, .triangle 25 1, .triangle 15 0, .corridorLower 1 2]

-- Cycle fingerprint 904b092cfc637a6e92fbda08f40325153bff88dfb9bf2751f741a2342deb2c80.
def localCycle00107 : Cycle where
  length := 7
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 2, .distance 2 6, .distance 2 4, .distance 2 3, .distance 1 2, .theta 1]
    constant := ![1, 0, -1, 0, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, true, false, false] }
  origin := ![.gapLower 1 6, .triangle 0 2, .triangle 8 0, .triangle 29 1, .triangle 25 1, .triangle 15 0, .corridorLower 1 2]

-- Cycle fingerprint 943c41c3b46788d0dd652b7cdba47a05b49b6f3de319d7880da3d0162532c136.
def localCycle00108 : Cycle where
  length := 8
  data := {
    node := ![.theta 2, .distance 0 2, .distance 0 4, .distance 4 6, .distance 1 4, .distance 4 5, .theta 4, .theta 3, .theta 2]
    constant := ![3, 0, -1, -1, -1, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, true, true] }
  origin := ![.corridorUpper 0 2, .triangle 6 2, .triangle 13 0, .triangle 23 0, .triangle 22 0, .corridorLower 4 5, .thetaNext 3, .thetaNext 2]

-- Cycle fingerprint 95914cd27ea0c6e6f80416db3ec2177b21a1a852f8aa6b0c684a89e01f39b8ac.
def localCycle00109 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .distance 2 5, .distance 1 5, .distance 1 6, .theta 1, .distance 0 1, .distance 0 2]
    constant := ![-1, 0, -2, -1, 2, 0]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![false, true, false, false, false, true] }
  origin := ![.triangle 7 0, .triangle 17 2, .gapLower 1 4, .corridorLower 1 6, .gapLower 1 6, .triangle 0 2]

-- Cycle fingerprint 9938d2f65ee6b0ac979ac123edf4b0d50986ed92823c0e502e1032367eadfeb1.
def localCycle00110 : Cycle where
  length := 8
  data := {
    node := ![.theta 1, .distance 0 1, .distance 1 6, .distance 1 2, .distance 1 3, .distance 3 4, .distance 2 3, .theta 2, .theta 1]
    constant := ![3, -1, 0, 0, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, true] }
  origin := ![.corridorUpper 0 1, .triangle 4 0, .triangle 18 1, .triangle 15 2, .triangle 19 0, .triangle 25 0, .corridorLower 2 3, .thetaNext 1]

-- Cycle fingerprint 9aa95721b16ac5308710abce15d55188a6e338ff47ac68143832ee4ae2007325.
def localCycle00111 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 2, .theta 1, .distance 0 1, .distance 0 2, .distance 2 4, .distance 1 4, .distance 1 6, .distance 1 5, .distance 1 3, .distance 1 2]
    constant := ![-1, 2, 0, -1, 0, 0, 0, 0, -2]
    coefficient := ![0, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, true, true, false, false] }
  origin := ![.corridorLower 1 2, .gapLower 1 6, .triangle 0 2, .triangle 6 0, .triangle 16 2, .triangle 23 2, .triangle 24 1, .gapLower 1 2, .gapLower 1 1]

-- Cycle fingerprint 9c9d01cb44be14d3d565906d0de400230e8246e883378bdb96f24fddcd69709b.
def localCycle00112 : Cycle where
  length := 10
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 2, .distance 0 4, .distance 4 6, .distance 2 4, .distance 4 5, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1]
    constant := ![3, 0, 0, -1, -1, -1, -1, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, false, false, true, true, false] }
  origin := ![.corridorUpper 0 1, .triangle 0 2, .triangle 6 2, .triangle 13 0, .triangle 29 0, .triangle 28 0, .triangle 22 0, .triangle 19 1, .triangle 15 1, .corridorLower 1 2]

-- Cycle fingerprint 9dc2d78f42af6eaa743d18a4feb1344c7585e3eb107731d51b7790fc664b114d.
def localCycle00113 : Cycle where
  length := 10
  data := {
    node := ![.theta 2, .distance 0 2, .distance 0 4, .distance 0 5, .distance 5 6, .distance 4 6, .distance 1 4, .distance 4 5, .theta 4, .theta 3, .theta 2]
    constant := ![3, 0, 0, -1, 0, -1, -1, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, false, false, true, true] }
  origin := ![.corridorUpper 0 2, .triangle 6 2, .triangle 12 2, .triangle 14 0, .triangle 34 2, .triangle 23 0, .triangle 22 0, .corridorLower 4 5, .thetaNext 3, .thetaNext 2]

-- Cycle fingerprint 9e1353ec6e830bd2f07b06e58143f09e7e0d9db23b08b6017c11a024f8ddc37d.
def localCycle00114 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 2 5, .distance 2 4, .distance 4 6, .distance 1 4, .distance 1 3, .theta 1, .distance 0 1]
    constant := ![0, -1, 0, -1, -1, 0, -1, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![true, false, true, false, false, false, false, false] }
  origin := ![.triangle 0 2, .triangle 7 0, .triangle 28 1, .triangle 29 0, .triangle 23 0, .gapLower 1 2, .corridorLower 1 3, .corridorUpper 0 1]

-- Cycle fingerprint 9f361687a575e40326880ad70c8be8df5638f512d5db2f2e4abed6e5c47ca9df.
def localCycle00115 : Cycle where
  length := 8
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 2, .distance 0 5, .distance 5 6, .distance 2 5, .distance 2 4, .distance 1 2, .theta 1]
    constant := ![3, 0, 0, -1, -1, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, true, false, false] }
  origin := ![.corridorUpper 0 1, .triangle 0 2, .triangle 7 2, .triangle 14 0, .triangle 30 0, .triangle 28 1, .triangle 16 0, .corridorLower 1 2]

-- Cycle fingerprint 9f438862abdc23d888a98900a31f546503df016aee83bc5c3b59d86415e5d2b0.
def localCycle00116 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 2, .distance 2 6, .distance 1 6, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1, .distance 0 1, .distance 0 2]
    constant := ![-1, 0, 0, 0, -2, -2, 3, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 0]
    strict := ![false, true, true, true, false, false, false, true] }
  origin := ![.triangle 8 0, .triangle 18 2, .triangle 23 1, .triangle 19 1, .gapLower 1 1, .gapLower 1 0, .corridorUpper 0 1, .triangle 0 2]

-- Cycle fingerprint a086b6b85f40723be0c8e54c4cf923bdd7a5ed35f807e04afc005c0a15ce261d.
def localCycle00117 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 0 4, .distance 4 5, .distance 1 4, .distance 4 6, .distance 5 6, .theta 5, .theta 4]
    constant := ![3, 0, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, true, false, true] }
  origin := ![.corridorUpper 3 4, .triangle 9 2, .triangle 12 0, .triangle 22 0, .triangle 23 0, .triangle 34 1, .corridorLower 5 6, .thetaNext 4]

-- Cycle fingerprint a2601035bd31534f712076e0fa64b3538d32bf8ecf36befeb4c15c5b7709a115.
def localCycle00118 : Cycle where
  length := 8
  data := {
    node := ![.distance 4 5, .theta 4, .theta 3, .theta 2, .theta 1, .distance 0 1, .distance 1 6, .distance 1 4, .distance 4 5]
    constant := ![-1, 0, 0, 0, 2, -2, 0, -1]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![false, true, true, true, false, false, true, false] }
  origin := ![.corridorLower 4 5, .thetaNext 3, .thetaNext 2, .thetaNext 1, .gapLower 1 6, .gapLower 1 5, .triangle 23 1, .triangle 22 0]

-- Cycle fingerprint a2889098cc3e22ad5bacec00c82d3b6214c3f0c4d6f693e954fd6065fd4529ec.
def localCycle00119 : Cycle where
  length := 8
  data := {
    node := ![.distance 2 6, .distance 2 5, .distance 2 3, .distance 1 2, .theta 1, .distance 0 1, .distance 0 2, .distance 2 4, .distance 2 6]
    constant := ![0, 0, -1, -2, 2, 0, -1, 0]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![true, false, false, false, false, true, false, true] }
  origin := ![.triangle 30 1, .gapLower 2 2, .triangle 15 0, .gapLower 1 0, .gapLower 1 6, .triangle 0 2, .triangle 6 0, .triangle 29 2]

-- Cycle fingerprint a4bb63e638cbc52d5c605f177551013b1189e491a783c75c29f214b34f23cab8.
def localCycle00120 : Cycle where
  length := 8
  data := {
    node := ![.distance 2 4, .distance 2 6, .distance 2 5, .distance 2 3, .distance 1 2, .theta 1, .distance 0 1, .distance 0 2, .distance 2 4]
    constant := ![0, 0, 0, -1, -3, 3, 0, -1]
    coefficient := ![0, 0, 0, 0, 0, 1, 0, 0]
    strict := ![true, true, false, false, false, false, true, false] }
  origin := ![.triangle 29 2, .triangle 30 1, .gapLower 2 2, .triangle 15 0, .gapLower 1 0, .corridorUpper 0 1, .triangle 0 2, .triangle 6 0]

-- Cycle fingerprint a66461b4c7779bc49dc1bcbfc00c3f5f185412166b3e53a47732e761e1c2d93f.
def localCycle00121 : Cycle where
  length := 9
  data := {
    node := ![.distance 2 4, .distance 4 6, .distance 5 6, .distance 1 5, .distance 1 4, .theta 1, .distance 0 1, .distance 0 2, .distance 2 5, .distance 2 4]
    constant := ![-1, 0, -1, 0, -1, 3, 0, -1, 0]
    coefficient := ![0, 0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![false, true, false, false, false, false, true, false, true] }
  origin := ![.triangle 29 0, .triangle 34 1, .triangle 24 0, .gapLower 1 3, .corridorLower 1 4, .corridorUpper 0 1, .triangle 0 2, .triangle 7 0, .triangle 28 1]

-- Cycle fingerprint aa856c0543042324699a712e99fb5b689f80cb8b6265dd90971fd8734375f46e.
def localCycle00122 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 0 2, .distance 2 4, .distance 1 4, .distance 4 5, .distance 5 6, .theta 5, .theta 4, .theta 3, .theta 2]
    constant := ![3, -1, 0, -1, -1, -1, 0, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, true, true, true] }
  origin := ![.corridorUpper 0 2, .triangle 6 0, .triangle 16 2, .triangle 22 0, .triangle 34 0, .corridorLower 5 6, .thetaNext 4, .thetaNext 3, .thetaNext 2]

-- Cycle fingerprint ab656db88cabfdb807624b02d04a6cd558b723cbf91ae0e0289e84eddf86f27a.
def localCycle00123 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 0 4, .distance 4 5, .distance 3 4, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, 0, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 13 0, .triangle 12 0, .triangle 31 0, .triangle 25 0, .corridorLower 2 3, .thetaLower 2]

-- Cycle fingerprint ac52088406b17996a5bdb5804ef4a8727316056eec1de7ab4052b6aa4f83a81b.
def localCycle00124 : Cycle where
  length := 3
  data := {
    node := ![.distance 2 3, .distance 1 3, .distance 1 2, .distance 2 3]
    constant := ![0, -3, 2]
    coefficient := ![0, 0, 0]
    strict := ![false, false, true] }
  origin := ![.gapLower 3 1, .gapLower 1 1, .gapUpper 2 1]

-- Cycle fingerprint add6f0bcc82e41fab60c28b7e767249a8208d2a3d62e34ec5132714c0a26a9f6.
def localCycle00125 : Cycle where
  length := 12
  data := {
    node := ![.theta 1, .distance 0 1, .distance 1 6, .distance 1 2, .distance 1 3, .distance 1 4, .distance 4 5, .distance 3 5, .distance 2 3, .distance 3 4, .theta 3, .theta 2, .theta 1]
    constant := ![3, -1, 0, 0, 0, -1, 0, -1, -1, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, true, false, true, false, false, false, true, true] }
  origin := ![.corridorUpper 0 1, .triangle 4 0, .triangle 18 1, .triangle 15 2, .triangle 19 2, .triangle 22 0, .triangle 31 2, .triangle 26 0, .triangle 25 0, .corridorLower 3 4, .thetaNext 2, .thetaNext 1]

-- Cycle fingerprint ae5f64a7cb9c310910e96b949b23cb061b6babd406c167d89b82b6b875135c26.
def localCycle00126 : Cycle where
  length := 9
  data := {
    node := ![.distance 2 6, .distance 1 6, .distance 1 5, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1, .distance 0 1, .distance 0 2, .distance 2 6]
    constant := ![0, -3, 0, 0, 0, -1, 3, 0, -1]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 0, 0]
    strict := ![true, false, true, true, true, false, false, true, false] }
  origin := ![.triangle 18 2, .gapLower 1 4, .triangle 22 1, .triangle 19 1, .triangle 15 1, .corridorLower 1 2, .corridorUpper 0 1, .triangle 0 2, .triangle 8 0]

-- Cycle fingerprint b111364cb5c9738200d27fe33b07bbef03c34543a799ff87031c5295afe89e23.
def localCycle00127 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 0 3, .distance 3 6, .distance 5 6, .distance 4 5, .distance 2 4, .distance 2 3, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, -1, -1, 0, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, false, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 9 0, .triangle 11 0, .triangle 33 1, .triangle 34 0, .triangle 28 0, .gapLower 2 2, .triangle 15 0, .corridorLower 1 2, .thetaLower 1]

-- Cycle fingerprint b4a0dedf0b819bc691177a8b67432a5677a30e9ba9638c9f6e1231186cfebb02.
def localCycle00128 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 6, .distance 1 4, .distance 1 5, .distance 1 3, .distance 1 2, .theta 1, .distance 0 1, .distance 0 2, .distance 2 6, .distance 1 6]
    constant := ![0, -2, 0, -2, -1, 3, 0, -1, 0]
    coefficient := ![0, 0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![true, false, true, false, false, false, true, false, true] }
  origin := ![.triangle 23 1, .gapLower 1 3, .triangle 20 1, .gapLower 1 1, .corridorLower 1 2, .corridorUpper 0 1, .triangle 0 2, .triangle 8 0, .triangle 18 2]

-- Cycle fingerprint b7494df9695dd1c9ce7a4daaf53e3e271ad8eaaae242670cc69ee521d9784bc4.
def localCycle00129 : Cycle where
  length := 8
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 2, .distance 2 5, .distance 1 5, .distance 1 6, .distance 1 4, .distance 1 3, .theta 1]
    constant := ![3, 0, -1, 0, -2, 0, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, true, false, false] }
  origin := ![.corridorUpper 0 1, .triangle 0 2, .triangle 7 0, .triangle 17 2, .gapLower 1 4, .triangle 23 1, .gapLower 1 2, .corridorLower 1 3]

-- Cycle fingerprint b85444289096082297f3ce26c82aaf7f54fbb12fd4d51b90aef0433b402b6d42.
def localCycle00130 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 2, .distance 2 4, .distance 1 4, .distance 1 6, .distance 1 5, .distance 1 3, .theta 1, .distance 0 1, .distance 0 2]
    constant := ![-1, 0, 0, 0, -3, -1, 3, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 0]
    strict := ![false, true, true, true, false, false, false, true] }
  origin := ![.triangle 6 0, .triangle 16 2, .triangle 23 2, .triangle 24 1, .gapLower 1 2, .corridorLower 1 3, .corridorUpper 0 1, .triangle 0 2]

-- Cycle fingerprint b9006d9078232897f90f114a747d2df3dedaebcbd90fce16066f029b97650d19.
def localCycle00131 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 0 3, .distance 3 6, .distance 2 3, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 9 0, .triangle 11 0, .triangle 27 0, .triangle 15 0, .corridorLower 1 2, .thetaLower 1]

-- Cycle fingerprint b99aad3927399e434ccb1fda152b64a06315ed09132f1d649ea9fba24a37d30d.
def localCycle00132 : Cycle where
  length := 7
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 2, .distance 2 5, .distance 2 4, .distance 2 3, .distance 1 2, .theta 1]
    constant := ![1, 0, -1, 0, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, true, false, false] }
  origin := ![.gapLower 1 6, .triangle 0 2, .triangle 7 0, .triangle 28 1, .triangle 25 1, .triangle 15 0, .corridorLower 1 2]

-- Cycle fingerprint baa5b75c043ae8fa05387f46158f6556521d380be0f09d031ae2ae945615baba.
def localCycle00133 : Cycle where
  length := 7
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 2, .distance 2 5, .distance 2 4, .distance 2 3, .distance 1 2, .theta 1]
    constant := ![2, 0, -1, 0, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, true, false, false] }
  origin := ![.gapLower 1 6, .triangle 0 2, .triangle 7 0, .triangle 28 1, .triangle 25 1, .triangle 15 0, .corridorLower 1 2]

-- Cycle fingerprint bafaf3a0c026a88d5439ba519a342643ccfc03d02dbea5443f7ae9613b4d13f0.
def localCycle00134 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 2 4, .distance 1 4, .distance 1 6, .distance 1 5, .distance 1 3, .theta 1, .distance 0 1]
    constant := ![0, -1, 0, 0, -2, -2, -1, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![true, false, true, true, false, false, false, false] }
  origin := ![.triangle 0 2, .triangle 6 0, .triangle 16 2, .triangle 23 2, .gapLower 1 3, .gapLower 1 2, .corridorLower 1 3, .corridorUpper 0 1]

-- Cycle fingerprint bb228fdcf032d852c124266dc3b12ba493e45f7e7f817f7fb1a2244cf0e6f8d1.
def localCycle00135 : Cycle where
  length := 8
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 2, .distance 2 6, .distance 1 6, .distance 1 5, .distance 1 4, .distance 1 3, .theta 1]
    constant := ![3, 0, -1, 0, -2, 0, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, true, false, false] }
  origin := ![.corridorUpper 0 1, .triangle 0 2, .triangle 8 0, .triangle 18 2, .gapLower 1 4, .triangle 22 1, .gapLower 1 2, .corridorLower 1 3]

-- Cycle fingerprint bb78b35938f0ac401632455fac50e7a3b911d7a9ed3abfb7ed69558a6737fe82.
def localCycle00136 : Cycle where
  length := 8
  data := {
    node := ![.distance 2 6, .distance 2 5, .distance 2 4, .distance 2 3, .distance 1 2, .theta 1, .distance 0 1, .distance 0 2, .distance 2 6]
    constant := ![0, 0, 0, -1, -3, 3, 0, -1]
    coefficient := ![0, 0, 0, 0, 0, 1, 0, 0]
    strict := ![true, true, true, false, false, false, true, false] }
  origin := ![.triangle 30 1, .triangle 28 1, .triangle 25 1, .triangle 15 0, .gapLower 1 0, .corridorUpper 0 1, .triangle 0 2, .triangle 8 0]

-- Cycle fingerprint bba6066264ce34152a2ad4063ea80942dffa1ddb231a8763966f86ce1a4e9fa0.
def localCycle00137 : Cycle where
  length := 8
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 2, .distance 2 5, .distance 1 5, .distance 1 6, .distance 1 3, .distance 1 2, .theta 1]
    constant := ![3, 0, -1, 0, -2, 0, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, true, false, false] }
  origin := ![.corridorUpper 0 1, .triangle 0 2, .triangle 7 0, .triangle 17 2, .gapLower 1 4, .triangle 21 1, .gapLower 1 1, .corridorLower 1 2]

-- Cycle fingerprint bbac60631f19da0e48999b7e2afc29030a63e87cca0638fb134528ae36699c7c.
def localCycle00138 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 5 6, .distance 3 5, .distance 3 4, .distance 0 3, .distance 2 3, .distance 1 2, .theta 1, .theta 0, .zero]
    constant := ![0, 3, -1, -1, 0, -1, 0, -1, -1, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, true, false, false, true, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 34 0, .triangle 33 0, .triangle 31 1, .triangle 9 0, .triangle 5 1, .triangle 15 0, .corridorLower 1 2, .thetaNext 0, .thetaLower 0]

-- Cycle fingerprint bbe58873482db73066a5c817c464340f9dc4b7198296900cce778fe94a909e22.
def localCycle00139 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 2 6, .distance 1 6, .distance 1 5, .distance 1 4, .distance 1 2, .theta 1, .distance 0 1]
    constant := ![0, -1, 0, 0, -2, 0, -2, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![true, false, true, true, false, true, false, false] }
  origin := ![.triangle 0 2, .triangle 8 0, .triangle 18 2, .triangle 24 1, .gapLower 1 3, .triangle 16 1, .gapLower 1 0, .corridorUpper 0 1]

-- Cycle fingerprint bf7a5af5364bac4cbb1a94c04fad03fb81eda90b57827d5bf60f10f8304faeab.
def localCycle00140 : Cycle where
  length := 10
  data := {
    node := ![.theta 1, .distance 0 1, .distance 1 6, .distance 1 2, .distance 2 3, .distance 2 4, .distance 4 5, .distance 3 4, .theta 3, .theta 2, .theta 1]
    constant := ![3, -1, 0, -1, 0, -1, -1, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false, false, true, true] }
  origin := ![.corridorUpper 0 1, .triangle 4 0, .triangle 18 1, .triangle 15 0, .triangle 25 2, .triangle 28 0, .triangle 31 0, .corridorLower 3 4, .thetaNext 2, .thetaNext 1]

-- Cycle fingerprint c017bc554eaa1a9eb161e6818df53c99ea50eb3923cf5945eb9fcc34456564ff.
def localCycle00141 : Cycle where
  length := 8
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 4, .distance 0 3, .distance 3 6, .distance 1 6, .distance 4 6, .distance 5 6, .theta 5]
    constant := ![3, -1, -1, -1, 0, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, true, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 0, .triangle 9 0, .triangle 11 0, .triangle 21 2, .triangle 23 1, .triangle 34 1, .corridorLower 5 6]

-- Cycle fingerprint c074a17e879d2bca6fb867baaa63351f02857ae21343af028ef04fbb27bef71c.
def localCycle00142 : Cycle where
  length := 9
  data := {
    node := ![.distance 5 6, .distance 1 5, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1, .distance 0 1, .distance 0 2, .distance 2 5, .distance 5 6]
    constant := ![-1, 0, 0, 0, -1, 3, 0, -1, -1]
    coefficient := ![0, 0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![false, false, true, true, false, false, true, false, false] }
  origin := ![.triangle 24 0, .gapLower 1 3, .triangle 19 1, .triangle 15 1, .corridorLower 1 2, .corridorUpper 0 1, .triangle 0 2, .triangle 7 0, .triangle 30 0]

-- Cycle fingerprint c077ed16f83e5469f2314d62fcc7727687f0dc4abfcf39b2404324971fe6cd53.
def localCycle00143 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 2, .distance 2 6, .distance 1 6, .distance 1 5, .distance 1 4, .distance 1 3, .theta 1, .distance 0 1, .distance 0 2]
    constant := ![-1, 0, 0, 0, -3, -1, 3, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 0]
    strict := ![false, true, true, true, false, false, false, true] }
  origin := ![.triangle 8 0, .triangle 18 2, .triangle 24 1, .triangle 22 1, .gapLower 1 2, .corridorLower 1 3, .corridorUpper 0 1, .triangle 0 2]

-- Cycle fingerprint c094723b903cde6c5dab5540b3be6deebd8eb952829cc724c3c0b2e89eed68f9.
def localCycle00144 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 5, .distance 3 4, .distance 0 3, .distance 2 3, .distance 1 2, .theta 1, .theta 0, .zero]
    constant := ![0, 3, -1, -1, -1, 0, -1, -1, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, false, true, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 0, .triangle 31 0, .triangle 9 0, .triangle 5 1, .triangle 15 0, .corridorLower 1 2, .thetaNext 0, .thetaLower 0]

-- Cycle fingerprint c21919c262376cef0381dbc72b3a2089c1ca993dd27fb40451df7071160e27fc.
def localCycle00145 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 2, .theta 1, .distance 0 1, .distance 0 2, .distance 2 5, .distance 2 4, .distance 2 3, .distance 1 2]
    constant := ![-3, 3, 0, -1, 0, 0, -1]
    coefficient := ![0, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, true, false] }
  origin := ![.gapLower 1 0, .corridorUpper 0 1, .triangle 0 2, .triangle 7 0, .triangle 28 1, .triangle 25 1, .triangle 15 0]

-- Cycle fingerprint c24a043233da1ccfc85f5f64a197a1b3406760ef9537f2903bc2c4c35d8e7d63.
def localCycle00146 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 4, .distance 4 6, .distance 2 4, .distance 2 3, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, -1, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 0, .triangle 32 0, .triangle 29 0, .gapLower 2 2, .triangle 15 0, .corridorLower 1 2, .thetaLower 1]

-- Cycle fingerprint c24f95d19a7e82792d3a1051ffaf1ec1826201ce0ea3698973648fefad29c295.
def localCycle00147 : Cycle where
  length := 14
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 2, .distance 2 5, .distance 1 5, .distance 5 6, .theta 5, .distance 4 5, .distance 3 4, .distance 0 4, .distance 4 6, .distance 2 4, .distance 2 3, .distance 1 2, .theta 1]
    constant := ![3, 0, -1, 0, -1, -1, 3, -1, 0, -1, -1, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, false, false, true, false, false, true, false, false] }
  origin := ![.corridorUpper 0 1, .triangle 0 2, .triangle 7 0, .triangle 17 2, .triangle 24 0, .corridorLower 5 6, .corridorUpper 4 5, .triangle 31 0, .triangle 9 2, .triangle 13 0, .triangle 29 0, .triangle 25 1, .triangle 15 0, .corridorLower 1 2]

-- Cycle fingerprint c2b5dd7857d1604df8a9cc5eb455e1c97ae374be5b5ef3c91d432f3ee1a86191.
def localCycle00148 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 6, .distance 1 4, .distance 1 5, .theta 1, .distance 0 1, .distance 0 2, .distance 2 6, .distance 1 6]
    constant := ![-2, -2, -1, 3, 0, -1, 0]
    coefficient := ![0, 0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, false, true, false, true] }
  origin := ![.gapLower 1 4, .gapLower 1 3, .corridorLower 1 5, .corridorUpper 0 1, .triangle 0 2, .triangle 8 0, .triangle 18 2]

-- Cycle fingerprint c38b7ced8ab94c3c67c249c4500d2fbe96989c509166c28fa1bf61c97ab3289f.
def localCycle00149 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 4 6, .distance 0 4, .distance 4 5, .distance 2 4, .distance 2 3, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, -1, -1, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 32 0, .triangle 13 0, .triangle 12 0, .triangle 28 0, .triangle 25 1, .triangle 15 0, .corridorLower 1 2, .thetaLower 1]

-- Cycle fingerprint c4aa6f96170d82fd7ab673032b54902b6aa24695e0e56689c521eef1fdc3aa3a.
def localCycle00150 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 4, .distance 1 6, .distance 1 5, .distance 1 3, .distance 1 2, .theta 1, .distance 0 1, .distance 0 2, .distance 2 4, .distance 1 4]
    constant := ![0, -3, 0, 0, -1, 3, 0, -1, 0]
    coefficient := ![0, 0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![true, false, true, true, false, false, true, false, true] }
  origin := ![.triangle 23 2, .gapLower 1 3, .triangle 20 1, .triangle 15 1, .corridorLower 1 2, .corridorUpper 0 1, .triangle 0 2, .triangle 6 0, .triangle 16 2]

-- Cycle fingerprint c4f6b3780adefdd147be1d936842637f814ac8ca1dd9f3e88e32d6023fe867cb.
def localCycle00151 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 2 5, .distance 1 5, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1, .distance 0 1]
    constant := ![0, -1, 0, 0, -3, 0, -1, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![true, false, true, true, false, true, false, false] }
  origin := ![.triangle 0 2, .triangle 7 0, .triangle 17 2, .triangle 22 1, .gapLower 1 2, .triangle 15 1, .corridorLower 1 2, .corridorUpper 0 1]

-- Cycle fingerprint c7de0974ba779404767ffdffb4bc9a6940f7cea98897468d8529a2e19cba5eee.
def localCycle00152 : Cycle where
  length := 8
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 2, .distance 2 6, .distance 1 6, .distance 1 5, .distance 1 3, .distance 1 2, .theta 1]
    constant := ![3, 0, -1, 0, -2, 0, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, true, false, false] }
  origin := ![.corridorUpper 0 1, .triangle 0 2, .triangle 8 0, .triangle 18 2, .gapLower 1 4, .triangle 20 1, .gapLower 1 1, .corridorLower 1 2]

-- Cycle fingerprint c82196962e58d7c4e8564dc9ba61bf0195644410e98433a770a1ec47fb670a77.
def localCycle00153 : Cycle where
  length := 6
  data := {
    node := ![.distance 1 6, .distance 1 5, .distance 1 3, .theta 1, .distance 0 1, .distance 1 4, .distance 1 6]
    constant := ![0, -2, -1, 3, -2, 0]
    coefficient := ![0, 0, 0, 1, 0, 0]
    strict := ![true, false, false, false, false, true] }
  origin := ![.triangle 24 1, .gapLower 1 2, .corridorLower 1 3, .corridorUpper 0 1, .gapLower 1 5, .triangle 23 2]

-- Cycle fingerprint ca1565d3807849d96384b10073d21f387d33a6ea6f5db6bcad5081e80418a728.
def localCycle00154 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 4, .distance 0 3, .distance 3 6, .distance 2 3, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, -1, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 0, .triangle 9 0, .triangle 11 0, .triangle 27 0, .triangle 15 0, .corridorLower 1 2, .thetaLower 1]

-- Cycle fingerprint ca5c624b2db2d1d37b54a32645f484ff1f76740f3ff41813e8affdc7b3245fff.
def localCycle00155 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 0 4, .distance 4 5, .distance 3 4, .distance 2 3, .theta 2, .theta 1, .zero]
    constant := ![0, 3, 0, -1, -1, -1, -1, -1, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false, true, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 13 0, .triangle 12 0, .triangle 31 0, .triangle 25 0, .corridorLower 2 3, .thetaNext 1, .thetaLower 1]

-- Cycle fingerprint cb7650425c15fb8305d2f679ddd028fe28736f3590092a12bf9870d2478fd277.
def localCycle00156 : Cycle where
  length := 10
  data := {
    node := ![.theta 1, .distance 0 1, .distance 1 6, .distance 1 2, .distance 2 3, .distance 3 4, .distance 4 5, .theta 4, .theta 3, .theta 2, .theta 1]
    constant := ![3, -1, 0, -1, -1, -1, -1, 0, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, true, true, true] }
  origin := ![.corridorUpper 0 1, .triangle 4 0, .triangle 18 1, .triangle 15 0, .triangle 25 0, .triangle 31 0, .corridorLower 4 5, .thetaNext 3, .thetaNext 2, .thetaNext 1]

-- Cycle fingerprint cc22b686fcd8d9c4c67cb36e367b66bd8a8dc33dd2c33d6c2642ecdbef6bed7b.
def localCycle00157 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 0 4, .distance 4 5, .distance 2 4, .distance 2 3, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, 0, -1, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 13 0, .triangle 12 0, .triangle 28 0, .gapLower 2 2, .triangle 15 0, .corridorLower 1 2, .thetaLower 1]

-- Cycle fingerprint cc99576c139647ffffeb4aee17b9a6a9cd6f5f57b988c31c0dbd3d6ea14a0fff.
def localCycle00158 : Cycle where
  length := 5
  data := {
    node := ![.distance 1 4, .distance 1 3, .theta 1, .distance 0 1, .distance 1 6, .distance 1 4]
    constant := ![-2, -1, 3, -2, 0]
    coefficient := ![0, 0, 1, 0, 0]
    strict := ![false, false, false, false, true] }
  origin := ![.gapLower 1 2, .corridorLower 1 3, .corridorUpper 0 1, .gapLower 1 5, .triangle 23 1]

-- Cycle fingerprint cca9ccbe63dd699695f45247188688d44215e44f815b19b2a6e4f183716d7af7.
def localCycle00159 : Cycle where
  length := 8
  data := {
    node := ![.distance 2 5, .distance 2 4, .distance 2 3, .distance 1 2, .theta 1, .distance 0 1, .distance 0 2, .distance 2 6, .distance 2 5]
    constant := ![0, 0, -1, -1, 1, 0, -1, 0]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![true, true, false, false, false, true, false, true] }
  origin := ![.triangle 28 1, .triangle 25 1, .triangle 15 0, .corridorLower 1 2, .gapLower 1 6, .triangle 0 2, .triangle 8 0, .triangle 30 1]

-- Cycle fingerprint cd344af896d209ec40c33e4d4445a755c008420ce4d47fa3dca8c0acf4ca807d.
def localCycle00160 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 4, .distance 1 6, .distance 1 5, .distance 1 3, .distance 1 2, .theta 1, .distance 0 1, .distance 0 2, .distance 2 4, .distance 1 4]
    constant := ![0, -2, 0, -2, -1, 3, 0, -1, 0]
    coefficient := ![0, 0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![true, false, true, false, false, false, true, false, true] }
  origin := ![.triangle 23 2, .gapLower 1 3, .triangle 20 1, .gapLower 1 1, .corridorLower 1 2, .corridorUpper 0 1, .triangle 0 2, .triangle 6 0, .triangle 16 2]

-- Cycle fingerprint cdd72b1202a97311767a4513e66995c3493752f779a3a0b63e824d788f0caee1.
def localCycle00161 : Cycle where
  length := 5
  data := {
    node := ![.distance 1 2, .distance 1 3, .distance 3 4, .distance 4 5, .distance 2 5, .distance 1 2]
    constant := ![0, -1, -1, 0, 2]
    coefficient := ![0, 0, 0, 0, 0]
    strict := ![true, false, false, true, true] }
  origin := ![.triangle 15 2, .triangle 19 0, .triangle 31 0, .triangle 28 2, .gapUpper 2 3]

-- Cycle fingerprint ce19faa6dc5a6132fd57f439170a6199768b2afea48048bc9a52b3c232028e4d.
def localCycle00162 : Cycle where
  length := 3
  data := {
    node := ![.distance 4 6, .distance 1 4, .distance 1 6, .distance 4 6]
    constant := ![2, -3, 0]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.gapUpper 4 2, .gapLower 1 4, .triangle 23 1]

-- Cycle fingerprint ce3423612780a309af8f5ae25a1cfe730a3e8a657d0ec69634e7b678c3936b3b.
def localCycle00163 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 0 3, .distance 3 4, .distance 2 4, .distance 1 2, .distance 2 5, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, 0, 0, -1, -1, 0, -1, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, true, false, false, true, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 11 0, .triangle 9 0, .triangle 25 2, .triangle 16 0, .triangle 17 0, .triangle 26 1, .corridorLower 2 3, .thetaLower 2]

-- Cycle fingerprint d0dca61ee8fd99407a173d6652748068f52131e31401f023bca94f9b2f0b3771.
def localCycle00164 : Cycle where
  length := 11
  data := {
    node := ![.theta 4, .distance 3 4, .distance 4 5, .distance 0 4, .distance 2 4, .distance 1 2, .distance 2 6, .distance 3 6, .distance 4 6, .distance 5 6, .theta 5, .theta 4]
    constant := ![3, -1, -1, 0, -1, -1, 0, 0, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, true, true, true, false, true] }
  origin := ![.corridorUpper 3 4, .triangle 31 0, .triangle 12 0, .triangle 6 1, .triangle 16 0, .triangle 18 0, .triangle 27 1, .triangle 32 1, .triangle 34 1, .corridorLower 5 6, .thetaNext 4]

-- Cycle fingerprint d155f3dead4821e31f3bc183b6f0b88aef8a45832ee5365511ee1f715849ae9e.
def localCycle00165 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 2, .theta 1, .distance 0 1, .distance 0 2, .distance 2 6, .distance 1 6, .distance 1 5, .distance 1 4, .distance 1 3, .distance 1 2]
    constant := ![-1, 2, 0, -1, 0, 0, 0, 0, -2]
    coefficient := ![0, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, true, true, true, false] }
  origin := ![.corridorLower 1 2, .gapLower 1 6, .triangle 0 2, .triangle 8 0, .triangle 18 2, .triangle 24 1, .triangle 22 1, .triangle 19 1, .gapLower 1 1]

-- Cycle fingerprint d24a22a4bf3115f3bdd7bd51a79498024cd7d6f31463609b46e8d2a4f68c88d6.
def localCycle00166 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 3 4, .distance 4 6, .distance 0 4, .distance 2 4, .distance 1 4, .distance 4 5, .theta 4]
    constant := ![3, -1, -1, 0, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 32 0, .triangle 13 0, .triangle 6 1, .triangle 16 2, .triangle 22 0, .corridorLower 4 5]

-- Cycle fingerprint d34b0568a83fc6de8c0e1fedbce18c0301cc95e4bf47242dcabdaaf79c0f1593.
def localCycle00167 : Cycle where
  length := 9
  data := {
    node := ![.theta 1, .distance 0 1, .distance 1 6, .distance 1 2, .distance 2 4, .distance 4 5, .theta 4, .theta 3, .theta 2, .theta 1]
    constant := ![3, -1, 0, -1, -1, -1, 0, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, true, true, true] }
  origin := ![.corridorUpper 0 1, .triangle 4 0, .triangle 18 1, .triangle 16 0, .triangle 28 0, .corridorLower 4 5, .thetaNext 3, .thetaNext 2, .thetaNext 1]

-- Cycle fingerprint d53de361463d3f063d44c62f73dd91ae1d05fc53e509baa95c7cbb29bdcbb9c9.
def localCycle00168 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 3 5, .distance 5 6, .distance 4 6, .distance 0 4, .distance 2 4, .distance 1 4, .distance 4 5, .theta 4]
    constant := ![3, 0, -1, 0, -1, 0, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, true, true, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 31 2, .triangle 33 0, .triangle 34 2, .triangle 13 0, .triangle 6 1, .triangle 16 2, .triangle 22 0, .corridorLower 4 5]

-- Cycle fingerprint d6891c63801ad5fb0d050771a26b76a0c0d3d34d066358f00f8d17c24a23d485.
def localCycle00169 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 3 5, .distance 5 6, .distance 4 5, .distance 0 4, .distance 2 4, .distance 2 3, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, 0, -1, -1, -1, 0, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, true, true, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 31 2, .triangle 33 0, .triangle 34 0, .triangle 12 0, .triangle 6 1, .triangle 25 1, .triangle 15 0, .corridorLower 1 2, .thetaLower 1]

-- Cycle fingerprint da45685e977f02190be7c577dbc68053f003ff7dfcf4b134fec302e52a372a16.
def localCycle00170 : Cycle where
  length := 12
  data := {
    node := ![.distance 2 5, .distance 2 3, .distance 1 2, .theta 1, .distance 0 1, .distance 1 4, .distance 4 6, .distance 4 5, .theta 4, .distance 3 4, .distance 3 5, .distance 5 6, .distance 2 5]
    constant := ![0, -1, -2, 3, -2, -1, 0, -1, 3, 0, -1, -1]
    coefficient := ![0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, false, false, true, false, false] }
  origin := ![.gapLower 2 2, .triangle 15 0, .gapLower 1 0, .corridorUpper 0 1, .gapLower 1 5, .triangle 23 0, .triangle 34 1, .corridorLower 4 5, .corridorUpper 3 4, .triangle 31 2, .triangle 33 0, .triangle 30 0]

-- Cycle fingerprint dc12033ed8c91c742c991e9b2b5b21f49163b01ad6078062d459b202c59c5514.
def localCycle00171 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 4 5, .distance 0 4, .distance 4 6, .distance 2 4, .distance 2 3, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, -1, -1, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 31 0, .triangle 12 0, .triangle 13 0, .triangle 29 0, .gapLower 2 2, .triangle 15 0, .corridorLower 1 2, .thetaLower 1]

-- Cycle fingerprint dcf832b33e4b37594013b0071592a09e6453c0575c71000f1ca7535626bfeff4.
def localCycle00172 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 3 5, .distance 5 6, .distance 4 6, .distance 2 4, .distance 4 5, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, 0, -1, 0, -1, -1, -1, 0, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false, false, true, true, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 31 2, .triangle 33 0, .triangle 34 2, .triangle 29 0, .triangle 28 0, .triangle 22 0, .triangle 19 1, .triangle 15 1, .corridorLower 1 2, .thetaLower 1]

-- Cycle fingerprint deb393382ee3b0ca7b8043743f5cb5372a96066e8985bba225acccf0c8a24f4d.
def localCycle00173 : Cycle where
  length := 7
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 4, .distance 0 3, .distance 3 6, .distance 4 6, .distance 5 6, .theta 5]
    constant := ![3, -1, -1, -1, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 0, .triangle 9 0, .triangle 11 0, .triangle 32 1, .triangle 34 1, .corridorLower 5 6]

-- Cycle fingerprint df80e00ef762c06878eefae2574b4140619ecc79f827d315ecc595c7f2f70291.
def localCycle00174 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 4, .distance 4 6, .distance 2 4, .distance 2 3, .distance 1 2, .theta 1, .zero, .theta 5, .distance 4 5, .distance 0 4]
    constant := ![-1, -1, 0, -1, -1, 0, 0, 3, -1]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![false, false, false, false, false, false, false, false, false] }
  origin := ![.triangle 13 0, .triangle 29 0, .gapLower 2 2, .triangle 15 0, .corridorLower 1 2, .thetaLower 1, .thetaUpper 5, .corridorUpper 4 5, .triangle 12 0]

-- Cycle fingerprint e202180257c551be0a4ba2690b12d04cdd92d3f5e89cfcf1b1fc4dbbd98874c4.
def localCycle00175 : Cycle where
  length := 9
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 2, .distance 0 4, .distance 4 6, .distance 4 5, .distance 2 4, .distance 2 3, .distance 1 2, .theta 1]
    constant := ![3, 0, 0, -1, 0, -1, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, true, false, false] }
  origin := ![.corridorUpper 0 1, .triangle 0 2, .triangle 6 2, .triangle 13 0, .triangle 34 1, .triangle 28 0, .triangle 25 1, .triangle 15 0, .corridorLower 1 2]

-- Cycle fingerprint e3ace8397b166097bc74160ab13f3ebf203049c9b3025084dae8a7fae5a2f4a2.
def localCycle00176 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 3 4, .distance 3 5, .distance 5 6, .distance 4 6, .distance 1 4, .distance 4 5, .theta 4]
    constant := ![3, 0, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 31 2, .triangle 33 0, .triangle 34 2, .triangle 23 0, .triangle 22 0, .corridorLower 4 5]

-- Cycle fingerprint e48c8a4020365fb2dc4de8c052cbd5ef185f33d3264a3a8fe46968ac0ee1a086.
def localCycle00177 : Cycle where
  length := 9
  data := {
    node := ![.distance 4 5, .distance 1 4, .distance 1 3, .theta 1, .distance 0 1, .distance 0 2, .distance 2 4, .distance 2 5, .distance 5 6, .distance 4 5]
    constant := ![-1, 0, -1, 3, 0, -1, 0, -1, -1]
    coefficient := ![0, 0, 0, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, true, false, false] }
  origin := ![.triangle 22 0, .gapLower 1 2, .corridorLower 1 3, .corridorUpper 0 1, .triangle 0 2, .triangle 6 0, .triangle 28 2, .triangle 30 0, .triangle 34 0]

-- Cycle fingerprint e6866fa6d554c807e7626df9509139f0c24b833497414454f82b5978a358ab79.
def localCycle00178 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 0 3, .distance 3 4, .distance 4 5, .distance 2 4, .distance 1 2, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, 0, 0, -1, -1, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 11 0, .triangle 9 0, .triangle 31 0, .triangle 28 0, .triangle 16 0, .triangle 15 0, .corridorLower 2 3, .thetaLower 2]

-- Cycle fingerprint e68a824a6a24d4d3b357b7faceb192938e6204ad30d51312dbeb46f809392e17.
def localCycle00179 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 4, .distance 1 3, .distance 1 2, .theta 1, .distance 0 1, .distance 0 2, .distance 2 6, .distance 1 6, .distance 1 5, .distance 1 4]
    constant := ![0, -2, -2, 3, 0, -1, 0, 0, 0]
    coefficient := ![0, 0, 0, 1, 0, 0, 0, 0, 0]
    strict := ![true, false, false, false, true, false, true, true, true] }
  origin := ![.triangle 19 1, .gapLower 1 1, .gapLower 1 0, .corridorUpper 0 1, .triangle 0 2, .triangle 8 0, .triangle 18 2, .triangle 24 1, .triangle 22 1]

-- Cycle fingerprint e6b065392d469e065e537205e69a786ae8134ee2804fc1a808620805cd5a0e42.
def localCycle00180 : Cycle where
  length := 10
  data := {
    node := ![.theta 2, .distance 0 2, .distance 2 4, .distance 2 5, .distance 5 6, .distance 4 6, .distance 1 4, .distance 4 5, .theta 4, .theta 3, .theta 2]
    constant := ![3, -1, 0, -1, 0, -1, -1, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false, false, true, true] }
  origin := ![.corridorUpper 0 2, .triangle 6 0, .triangle 28 2, .triangle 30 0, .triangle 34 2, .triangle 23 0, .triangle 22 0, .corridorLower 4 5, .thetaNext 3, .thetaNext 2]

-- Cycle fingerprint e7452657dcec7ca0af7f642bf043bedcef8caad11b5ca78ac4c7d740a97516ad.
def localCycle00181 : Cycle where
  length := 5
  data := {
    node := ![.distance 1 3, .distance 1 2, .theta 1, .distance 0 1, .distance 1 6, .distance 1 3]
    constant := ![-2, -1, 3, -2, 0]
    coefficient := ![0, 0, 1, 0, 0]
    strict := ![false, false, false, false, true] }
  origin := ![.gapLower 1 1, .corridorLower 1 2, .corridorUpper 0 1, .gapLower 1 5, .triangle 21 1]

-- Cycle fingerprint e7c35613c920bfbb8380bc65b22d05955a241172651ec4e92b929d2dd8cb9e9c.
def localCycle00182 : Cycle where
  length := 12
  data := {
    node := ![.distance 4 6, .distance 2 4, .distance 2 3, .distance 1 2, .theta 1, .distance 0 1, .distance 1 5, .distance 5 6, .theta 5, .theta 4, .distance 3 4, .distance 4 5, .distance 4 6]
    constant := ![-1, 0, -1, -1, 2, -2, -1, -1, 0, 3, -1, 0]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0]
    strict := ![false, false, false, false, false, false, false, false, true, false, false, true] }
  origin := ![.triangle 29 0, .gapLower 2 2, .triangle 15 0, .corridorLower 1 2, .gapLower 1 6, .gapLower 1 5, .triangle 24 0, .corridorLower 5 6, .thetaNext 4, .corridorUpper 3 4, .triangle 31 0, .triangle 34 2]

-- Cycle fingerprint ed73c6f47f106d003db15f9fbdb6e1463dc967728648757979d041f5590c523f.
def localCycle00183 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 0 3, .distance 3 6, .distance 5 6, .distance 4 6, .distance 2 4, .distance 4 5, .theta 4]
    constant := ![3, -1, -1, 0, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 9 0, .triangle 11 0, .triangle 33 1, .triangle 34 2, .triangle 29 0, .triangle 28 0, .corridorLower 4 5]

-- Cycle fingerprint edb1b697777797253b665fb1129d2488e573158efcfb5b0cdd1533aa1cdd2a3e.
def localCycle00184 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 4, .distance 4 6, .distance 5 6, .distance 0 5, .distance 2 5, .distance 2 4, .distance 2 3, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, -1, -1, 0, -1, 0, 0, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, true, true, true, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 0, .triangle 32 0, .triangle 34 1, .triangle 14 0, .triangle 7 1, .triangle 28 1, .triangle 25 1, .triangle 15 0, .corridorLower 1 2, .thetaLower 1]

-- Cycle fingerprint ee323ebf84bbc4c6d122f1ac6b6389031dceb9759a92f24e18ecf46c711923aa.
def localCycle00185 : Cycle where
  length := 10
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 2, .distance 0 4, .distance 0 5, .distance 5 6, .distance 4 5, .distance 2 4, .distance 2 3, .distance 1 2, .theta 1]
    constant := ![3, 0, 0, 0, -1, -1, -1, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, false, false, false, false, false] }
  origin := ![.corridorUpper 0 1, .triangle 0 2, .triangle 6 2, .triangle 12 2, .triangle 14 0, .triangle 34 0, .triangle 28 0, .gapLower 2 2, .triangle 15 0, .corridorLower 1 2]

-- Cycle fingerprint ee95785255b16eef7a4d51f0463e31264c6551abaac1d5c69eea3c87a4e0b4f3.
def localCycle00186 : Cycle where
  length := 6
  data := {
    node := ![.theta 4, .distance 3 4, .distance 0 3, .distance 3 6, .distance 5 6, .distance 4 5, .theta 4]
    constant := ![3, -1, -1, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 9 0, .triangle 11 0, .triangle 33 1, .triangle 34 0, .corridorLower 4 5]

-- Cycle fingerprint ef656e1c076d3263d67b9c97e5e9a298fe6a705bcae0c303d3e94d623d4e71af.
def localCycle00187 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 2 6, .distance 1 6, .distance 1 5, .distance 1 4, .distance 1 3, .theta 1, .distance 0 1]
    constant := ![0, -1, 0, 0, -2, -2, -1, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![true, false, true, true, false, false, false, false] }
  origin := ![.triangle 0 2, .triangle 8 0, .triangle 18 2, .triangle 24 1, .gapLower 1 3, .gapLower 1 2, .corridorLower 1 3, .corridorUpper 0 1]

-- Cycle fingerprint f00e6c5772351f6f46b7239f12e67c34a00aea55e7fad89bfa94536d07fa5631.
def localCycle00188 : Cycle where
  length := 12
  data := {
    node := ![.distance 2 4, .distance 2 3, .distance 1 2, .theta 1, .distance 0 1, .distance 1 5, .distance 5 6, .theta 5, .theta 4, .distance 3 4, .distance 4 5, .distance 4 6, .distance 2 4]
    constant := ![0, -1, -1, 3, -3, -1, -1, 0, 3, -1, 0, -1]
    coefficient := ![0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, true, false, false, true, false] }
  origin := ![.gapLower 2 2, .triangle 15 0, .corridorLower 1 2, .corridorUpper 0 1, .gapLower 1 5, .triangle 24 0, .corridorLower 5 6, .thetaNext 4, .corridorUpper 3 4, .triangle 31 0, .triangle 34 2, .triangle 29 0]

-- Cycle fingerprint f3dbc225adbe10aa2bdbb8bf051ae058b60b422f3c359c2b6c100afcd61634b6.
def localCycle00189 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 0 4, .distance 4 5, .distance 2 5, .distance 1 2, .distance 2 3, .distance 3 4, .theta 3, .zero]
    constant := ![0, 3, 0, -1, -1, 0, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, false, false, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 13 0, .triangle 12 0, .triangle 28 2, .triangle 17 0, .triangle 15 0, .triangle 25 0, .corridorLower 3 4, .thetaLower 3]

-- Cycle fingerprint f43012e14d0a1e2fa52edf45a8ec256dd3f9adfd578d2af4e666347b72762577.
def localCycle00190 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 0 4, .distance 4 5, .distance 3 5, .distance 1 3, .distance 3 4, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, 0, -1, -1, 0, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, false, false, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 13 0, .triangle 12 0, .triangle 31 2, .triangle 20 0, .triangle 19 0, .triangle 25 0, .corridorLower 2 3, .thetaLower 2]

-- Cycle fingerprint f4bf91560f5b84a5ae386cf7f8e42bab57c0384c0c5f34c26fc86b80cbb7a76e.
def localCycle00191 : Cycle where
  length := 10
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 4, .distance 0 3, .distance 2 3, .distance 1 2, .distance 2 6, .distance 3 6, .distance 4 6, .distance 5 6, .theta 5]
    constant := ![3, -1, -1, 0, -1, -1, 0, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, true, true, true, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 0, .triangle 9 0, .triangle 5 1, .triangle 15 0, .triangle 18 0, .triangle 27 1, .triangle 32 1, .triangle 34 1, .corridorLower 5 6]

-- Cycle fingerprint f50698e427da57cb17e2be7af8847915a2cba2971bc8e21b19c029f87c09951e.
def localCycle00192 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 4, .distance 1 5, .distance 1 3, .distance 1 2, .theta 1, .distance 0 1, .distance 0 2, .distance 2 6, .distance 1 6, .distance 1 4]
    constant := ![0, -2, -2, -1, 3, 0, -1, 0, 0]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0, 0]
    strict := ![true, false, false, false, false, true, false, true, true] }
  origin := ![.triangle 22 2, .gapLower 1 2, .gapLower 1 1, .corridorLower 1 2, .corridorUpper 0 1, .triangle 0 2, .triangle 8 0, .triangle 18 2, .triangle 23 1]

-- Cycle fingerprint f55dde6233a9bbe4b063e56852ea082281522e9be247f616c047dcbb510d1e3c.
def localCycle00193 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 6, .distance 1 5, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1, .distance 0 1]
    constant := ![-3, 0, 0, 0, 0, -1, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, true, true, true, false, false] }
  origin := ![.gapLower 1 5, .triangle 24 1, .triangle 22 1, .triangle 19 1, .triangle 15 1, .corridorLower 1 2, .corridorUpper 0 1]

-- Cycle fingerprint f9ea7af3bdc4af9bb2d6cc3fd7c3e59167e7c37b15240dd61c3c5c3ea131eb57.
def localCycle00194 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 5, .distance 1 6, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1, .distance 0 1, .distance 0 2, .distance 2 5, .distance 1 5]
    constant := ![0, -3, 0, 0, -1, 3, 0, -1, 0]
    coefficient := ![0, 0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![true, false, true, true, false, false, true, false, true] }
  origin := ![.triangle 24 2, .gapLower 1 3, .triangle 19 1, .triangle 15 1, .corridorLower 1 2, .corridorUpper 0 1, .triangle 0 2, .triangle 7 0, .triangle 17 2]

-- Cycle fingerprint fb42ab2a114d15c99b9b0ae910e47c6edb654f8fce50beb5c409970f1ae2a513.
def localCycle00195 : Cycle where
  length := 8
  data := {
    node := ![.distance 4 5, .distance 2 4, .distance 2 3, .distance 1 2, .theta 1, .distance 0 1, .distance 0 2, .distance 0 4, .distance 4 5]
    constant := ![-1, 0, -1, -1, 3, 0, 0, -1]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![false, true, false, false, false, true, true, false] }
  origin := ![.triangle 28 0, .triangle 25 1, .triangle 15 0, .corridorLower 1 2, .corridorUpper 0 1, .triangle 0 2, .triangle 6 2, .triangle 12 0]

-- Cycle fingerprint fb7bd8223a897fe04e5ecf3fc148c05e6aeb61fffb389d900f4a1b2b3912e59f.
def localCycle00196 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 6, .distance 1 5, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1, .distance 0 1, .distance 0 2, .distance 2 6, .distance 1 6]
    constant := ![0, -2, 0, -2, -1, 3, 0, -1, 0]
    coefficient := ![0, 0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![true, false, true, false, false, false, true, false, true] }
  origin := ![.triangle 24 1, .gapLower 1 3, .triangle 19 1, .gapLower 1 1, .corridorLower 1 2, .corridorUpper 0 1, .triangle 0 2, .triangle 8 0, .triangle 18 2]

-- Cycle fingerprint fd3ba523112913f3a2c25a755f61b80b1e557224fc91d84f7ee00a3dec6ce484.
def localCycle00197 : Cycle where
  length := 4
  data := {
    node := ![.distance 0 1, .distance 1 5, .distance 1 6, .theta 1, .distance 0 1]
    constant := ![-2, -2, -1, 3]
    coefficient := ![0, 0, 0, 1]
    strict := ![false, false, false, false] }
  origin := ![.gapLower 1 5, .gapLower 1 4, .corridorLower 1 6, .corridorUpper 0 1]

-- Cycle fingerprint fdb8ce4d311915bf30e12657f4c0915e51a4cb947d1eb80234a598a2fccfdd50.
def localCycle00198 : Cycle where
  length := 7
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 2, .distance 2 5, .distance 2 4, .distance 2 3, .distance 1 2, .theta 1]
    constant := ![2, 0, -1, 0, 0, -1, -2]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, true, false, false] }
  origin := ![.gapLower 1 6, .triangle 0 2, .triangle 7 0, .triangle 28 1, .triangle 25 1, .triangle 15 0, .gapLower 1 0]

-- Cycle fingerprint fe168f48d48af381052638b248b8be63bcf7b607be1b265a7edafc808bfd6f1b.
def localCycle00199 : Cycle where
  length := 5
  data := {
    node := ![.distance 1 5, .distance 1 3, .theta 1, .distance 0 1, .distance 1 6, .distance 1 5]
    constant := ![-2, -1, 3, -2, 0]
    coefficient := ![0, 0, 1, 0, 0]
    strict := ![false, false, false, false, true] }
  origin := ![.gapLower 1 2, .corridorLower 1 3, .corridorUpper 0 1, .gapLower 1 5, .triangle 24 1]

def library : Library := fun id => if id < 100 then (if id < 50 then (if id < 25 then (if id < 12 then (if id < 6 then (if id < 3 then (if id < 1 then (if id = 0 then some localCycle00000 else none) else (if id < 2 then (if id = 1 then some localCycle00001 else none) else (if id = 2 then some localCycle00002 else none))) else (if id < 4 then (if id = 3 then some localCycle00003 else none) else (if id < 5 then (if id = 4 then some localCycle00004 else none) else (if id = 5 then some localCycle00005 else none)))) else (if id < 9 then (if id < 7 then (if id = 6 then some localCycle00006 else none) else (if id < 8 then (if id = 7 then some localCycle00007 else none) else (if id = 8 then some localCycle00008 else none))) else (if id < 10 then (if id = 9 then some localCycle00009 else none) else (if id < 11 then (if id = 10 then some localCycle00010 else none) else (if id = 11 then some localCycle00011 else none))))) else (if id < 18 then (if id < 15 then (if id < 13 then (if id = 12 then some localCycle00012 else none) else (if id < 14 then (if id = 13 then some localCycle00013 else none) else (if id = 14 then some localCycle00014 else none))) else (if id < 16 then (if id = 15 then some localCycle00015 else none) else (if id < 17 then (if id = 16 then some localCycle00016 else none) else (if id = 17 then some localCycle00017 else none)))) else (if id < 21 then (if id < 19 then (if id = 18 then some localCycle00018 else none) else (if id < 20 then (if id = 19 then some localCycle00019 else none) else (if id = 20 then some localCycle00020 else none))) else (if id < 23 then (if id < 22 then (if id = 21 then some localCycle00021 else none) else (if id = 22 then some localCycle00022 else none)) else (if id < 24 then (if id = 23 then some localCycle00023 else none) else (if id = 24 then some localCycle00024 else none)))))) else (if id < 37 then (if id < 31 then (if id < 28 then (if id < 26 then (if id = 25 then some localCycle00025 else none) else (if id < 27 then (if id = 26 then some localCycle00026 else none) else (if id = 27 then some localCycle00027 else none))) else (if id < 29 then (if id = 28 then some localCycle00028 else none) else (if id < 30 then (if id = 29 then some localCycle00029 else none) else (if id = 30 then some localCycle00030 else none)))) else (if id < 34 then (if id < 32 then (if id = 31 then some localCycle00031 else none) else (if id < 33 then (if id = 32 then some localCycle00032 else none) else (if id = 33 then some localCycle00033 else none))) else (if id < 35 then (if id = 34 then some localCycle00034 else none) else (if id < 36 then (if id = 35 then some localCycle00035 else none) else (if id = 36 then some localCycle00036 else none))))) else (if id < 43 then (if id < 40 then (if id < 38 then (if id = 37 then some localCycle00037 else none) else (if id < 39 then (if id = 38 then some localCycle00038 else none) else (if id = 39 then some localCycle00039 else none))) else (if id < 41 then (if id = 40 then some localCycle00040 else none) else (if id < 42 then (if id = 41 then some localCycle00041 else none) else (if id = 42 then some localCycle00042 else none)))) else (if id < 46 then (if id < 44 then (if id = 43 then some localCycle00043 else none) else (if id < 45 then (if id = 44 then some localCycle00044 else none) else (if id = 45 then some localCycle00045 else none))) else (if id < 48 then (if id < 47 then (if id = 46 then some localCycle00046 else none) else (if id = 47 then some localCycle00047 else none)) else (if id < 49 then (if id = 48 then some localCycle00048 else none) else (if id = 49 then some localCycle00049 else none))))))) else (if id < 75 then (if id < 62 then (if id < 56 then (if id < 53 then (if id < 51 then (if id = 50 then some localCycle00050 else none) else (if id < 52 then (if id = 51 then some localCycle00051 else none) else (if id = 52 then some localCycle00052 else none))) else (if id < 54 then (if id = 53 then some localCycle00053 else none) else (if id < 55 then (if id = 54 then some localCycle00054 else none) else (if id = 55 then some localCycle00055 else none)))) else (if id < 59 then (if id < 57 then (if id = 56 then some localCycle00056 else none) else (if id < 58 then (if id = 57 then some localCycle00057 else none) else (if id = 58 then some localCycle00058 else none))) else (if id < 60 then (if id = 59 then some localCycle00059 else none) else (if id < 61 then (if id = 60 then some localCycle00060 else none) else (if id = 61 then some localCycle00061 else none))))) else (if id < 68 then (if id < 65 then (if id < 63 then (if id = 62 then some localCycle00062 else none) else (if id < 64 then (if id = 63 then some localCycle00063 else none) else (if id = 64 then some localCycle00064 else none))) else (if id < 66 then (if id = 65 then some localCycle00065 else none) else (if id < 67 then (if id = 66 then some localCycle00066 else none) else (if id = 67 then some localCycle00067 else none)))) else (if id < 71 then (if id < 69 then (if id = 68 then some localCycle00068 else none) else (if id < 70 then (if id = 69 then some localCycle00069 else none) else (if id = 70 then some localCycle00070 else none))) else (if id < 73 then (if id < 72 then (if id = 71 then some localCycle00071 else none) else (if id = 72 then some localCycle00072 else none)) else (if id < 74 then (if id = 73 then some localCycle00073 else none) else (if id = 74 then some localCycle00074 else none)))))) else (if id < 87 then (if id < 81 then (if id < 78 then (if id < 76 then (if id = 75 then some localCycle00075 else none) else (if id < 77 then (if id = 76 then some localCycle00076 else none) else (if id = 77 then some localCycle00077 else none))) else (if id < 79 then (if id = 78 then some localCycle00078 else none) else (if id < 80 then (if id = 79 then some localCycle00079 else none) else (if id = 80 then some localCycle00080 else none)))) else (if id < 84 then (if id < 82 then (if id = 81 then some localCycle00081 else none) else (if id < 83 then (if id = 82 then some localCycle00082 else none) else (if id = 83 then some localCycle00083 else none))) else (if id < 85 then (if id = 84 then some localCycle00084 else none) else (if id < 86 then (if id = 85 then some localCycle00085 else none) else (if id = 86 then some localCycle00086 else none))))) else (if id < 93 then (if id < 90 then (if id < 88 then (if id = 87 then some localCycle00087 else none) else (if id < 89 then (if id = 88 then some localCycle00088 else none) else (if id = 89 then some localCycle00089 else none))) else (if id < 91 then (if id = 90 then some localCycle00090 else none) else (if id < 92 then (if id = 91 then some localCycle00091 else none) else (if id = 92 then some localCycle00092 else none)))) else (if id < 96 then (if id < 94 then (if id = 93 then some localCycle00093 else none) else (if id < 95 then (if id = 94 then some localCycle00094 else none) else (if id = 95 then some localCycle00095 else none))) else (if id < 98 then (if id < 97 then (if id = 96 then some localCycle00096 else none) else (if id = 97 then some localCycle00097 else none)) else (if id < 99 then (if id = 98 then some localCycle00098 else none) else (if id = 99 then some localCycle00099 else none)))))))) else (if id < 150 then (if id < 125 then (if id < 112 then (if id < 106 then (if id < 103 then (if id < 101 then (if id = 100 then some localCycle00100 else none) else (if id < 102 then (if id = 101 then some localCycle00101 else none) else (if id = 102 then some localCycle00102 else none))) else (if id < 104 then (if id = 103 then some localCycle00103 else none) else (if id < 105 then (if id = 104 then some localCycle00104 else none) else (if id = 105 then some localCycle00105 else none)))) else (if id < 109 then (if id < 107 then (if id = 106 then some localCycle00106 else none) else (if id < 108 then (if id = 107 then some localCycle00107 else none) else (if id = 108 then some localCycle00108 else none))) else (if id < 110 then (if id = 109 then some localCycle00109 else none) else (if id < 111 then (if id = 110 then some localCycle00110 else none) else (if id = 111 then some localCycle00111 else none))))) else (if id < 118 then (if id < 115 then (if id < 113 then (if id = 112 then some localCycle00112 else none) else (if id < 114 then (if id = 113 then some localCycle00113 else none) else (if id = 114 then some localCycle00114 else none))) else (if id < 116 then (if id = 115 then some localCycle00115 else none) else (if id < 117 then (if id = 116 then some localCycle00116 else none) else (if id = 117 then some localCycle00117 else none)))) else (if id < 121 then (if id < 119 then (if id = 118 then some localCycle00118 else none) else (if id < 120 then (if id = 119 then some localCycle00119 else none) else (if id = 120 then some localCycle00120 else none))) else (if id < 123 then (if id < 122 then (if id = 121 then some localCycle00121 else none) else (if id = 122 then some localCycle00122 else none)) else (if id < 124 then (if id = 123 then some localCycle00123 else none) else (if id = 124 then some localCycle00124 else none)))))) else (if id < 137 then (if id < 131 then (if id < 128 then (if id < 126 then (if id = 125 then some localCycle00125 else none) else (if id < 127 then (if id = 126 then some localCycle00126 else none) else (if id = 127 then some localCycle00127 else none))) else (if id < 129 then (if id = 128 then some localCycle00128 else none) else (if id < 130 then (if id = 129 then some localCycle00129 else none) else (if id = 130 then some localCycle00130 else none)))) else (if id < 134 then (if id < 132 then (if id = 131 then some localCycle00131 else none) else (if id < 133 then (if id = 132 then some localCycle00132 else none) else (if id = 133 then some localCycle00133 else none))) else (if id < 135 then (if id = 134 then some localCycle00134 else none) else (if id < 136 then (if id = 135 then some localCycle00135 else none) else (if id = 136 then some localCycle00136 else none))))) else (if id < 143 then (if id < 140 then (if id < 138 then (if id = 137 then some localCycle00137 else none) else (if id < 139 then (if id = 138 then some localCycle00138 else none) else (if id = 139 then some localCycle00139 else none))) else (if id < 141 then (if id = 140 then some localCycle00140 else none) else (if id < 142 then (if id = 141 then some localCycle00141 else none) else (if id = 142 then some localCycle00142 else none)))) else (if id < 146 then (if id < 144 then (if id = 143 then some localCycle00143 else none) else (if id < 145 then (if id = 144 then some localCycle00144 else none) else (if id = 145 then some localCycle00145 else none))) else (if id < 148 then (if id < 147 then (if id = 146 then some localCycle00146 else none) else (if id = 147 then some localCycle00147 else none)) else (if id < 149 then (if id = 148 then some localCycle00148 else none) else (if id = 149 then some localCycle00149 else none))))))) else (if id < 175 then (if id < 162 then (if id < 156 then (if id < 153 then (if id < 151 then (if id = 150 then some localCycle00150 else none) else (if id < 152 then (if id = 151 then some localCycle00151 else none) else (if id = 152 then some localCycle00152 else none))) else (if id < 154 then (if id = 153 then some localCycle00153 else none) else (if id < 155 then (if id = 154 then some localCycle00154 else none) else (if id = 155 then some localCycle00155 else none)))) else (if id < 159 then (if id < 157 then (if id = 156 then some localCycle00156 else none) else (if id < 158 then (if id = 157 then some localCycle00157 else none) else (if id = 158 then some localCycle00158 else none))) else (if id < 160 then (if id = 159 then some localCycle00159 else none) else (if id < 161 then (if id = 160 then some localCycle00160 else none) else (if id = 161 then some localCycle00161 else none))))) else (if id < 168 then (if id < 165 then (if id < 163 then (if id = 162 then some localCycle00162 else none) else (if id < 164 then (if id = 163 then some localCycle00163 else none) else (if id = 164 then some localCycle00164 else none))) else (if id < 166 then (if id = 165 then some localCycle00165 else none) else (if id < 167 then (if id = 166 then some localCycle00166 else none) else (if id = 167 then some localCycle00167 else none)))) else (if id < 171 then (if id < 169 then (if id = 168 then some localCycle00168 else none) else (if id < 170 then (if id = 169 then some localCycle00169 else none) else (if id = 170 then some localCycle00170 else none))) else (if id < 173 then (if id < 172 then (if id = 171 then some localCycle00171 else none) else (if id = 172 then some localCycle00172 else none)) else (if id < 174 then (if id = 173 then some localCycle00173 else none) else (if id = 174 then some localCycle00174 else none)))))) else (if id < 187 then (if id < 181 then (if id < 178 then (if id < 176 then (if id = 175 then some localCycle00175 else none) else (if id < 177 then (if id = 176 then some localCycle00176 else none) else (if id = 177 then some localCycle00177 else none))) else (if id < 179 then (if id = 178 then some localCycle00178 else none) else (if id < 180 then (if id = 179 then some localCycle00179 else none) else (if id = 180 then some localCycle00180 else none)))) else (if id < 184 then (if id < 182 then (if id = 181 then some localCycle00181 else none) else (if id < 183 then (if id = 182 then some localCycle00182 else none) else (if id = 183 then some localCycle00183 else none))) else (if id < 185 then (if id = 184 then some localCycle00184 else none) else (if id < 186 then (if id = 185 then some localCycle00185 else none) else (if id = 186 then some localCycle00186 else none))))) else (if id < 193 then (if id < 190 then (if id < 188 then (if id = 187 then some localCycle00187 else none) else (if id < 189 then (if id = 188 then some localCycle00188 else none) else (if id = 189 then some localCycle00189 else none))) else (if id < 191 then (if id = 190 then some localCycle00190 else none) else (if id < 192 then (if id = 191 then some localCycle00191 else none) else (if id = 192 then some localCycle00192 else none)))) else (if id < 196 then (if id < 194 then (if id = 193 then some localCycle00193 else none) else (if id < 195 then (if id = 194 then some localCycle00194 else none) else (if id = 195 then some localCycle00195 else none))) else (if id < 198 then (if id < 197 then (if id = 196 then some localCycle00196 else none) else (if id = 197 then some localCycle00197 else none)) else (if id < 199 then (if id = 198 then some localCycle00198 else none) else (if id = 199 then some localCycle00199 else none))))))))

def namedLeaf000 : LeafData := { rows := ![![5, 4, 3, 2, 6, 1], ![3, 2, 4, 5, 6, 0], ![3, 1, 4, 5, 0, 6], ![2, 1, 5, 4, 0, 6], ![1, 2, 5, 3, 0, 6], ![1, 2, 4, 3, 0, 6], ![1, 0, 2, 3, 4, 5]], proof := .tail 178 }

theorem namedLeaf000_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21504)) namedLeaf000 = true :=
  by decide +kernel

def namedLeaf001 : LeafData := { rows := ![![5, 4, 3, 2, 6, 1], ![3, 2, 4, 5, 6, 0], ![3, 1, 5, 4, 0, 6], ![2, 1, 5, 4, 0, 6], ![1, 5, 2, 3, 0, 6], ![1, 4, 2, 3, 0, 6], ![1, 0, 2, 3, 4, 5]], proof := .tail 74 }

theorem namedLeaf001_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21505)) namedLeaf001 = true :=
  by decide +kernel

def namedLeaf002 : LeafData := { rows := ![![5, 4, 3, 2, 6, 1], ![3, 2, 5, 4, 6, 0], ![3, 1, 5, 4, 0, 6], ![2, 1, 5, 4, 0, 6], ![5, 1, 2, 3, 0, 6], ![4, 1, 2, 3, 0, 6], ![1, 0, 2, 3, 4, 5]], proof := .tail 35 }

theorem namedLeaf002_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21506)) namedLeaf002 = true :=
  by decide +kernel

def namedLeaf003 : LeafData := { rows := ![![5, 4, 3, 2, 6, 1], ![3, 5, 2, 4, 6, 0], ![3, 5, 1, 4, 0, 6], ![2, 1, 5, 4, 0, 6], ![5, 1, 2, 3, 0, 6], ![4, 2, 1, 3, 0, 6], ![1, 0, 2, 3, 4, 5]], proof := .tail 163 }

theorem namedLeaf003_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21507)) namedLeaf003 = true :=
  by decide +kernel

def namedLeaf004 : LeafData := { rows := ![![5, 4, 3, 2, 6, 1], ![5, 3, 2, 4, 6, 0], ![3, 5, 1, 4, 0, 6], ![2, 5, 1, 4, 0, 6], ![5, 1, 2, 3, 0, 6], ![4, 2, 3, 1, 0, 6], ![1, 0, 2, 3, 4, 5]], proof := .tail 4 }

theorem namedLeaf004_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21508)) namedLeaf004 = true :=
  by decide +kernel

def namedLeaf005 : LeafData := { rows := ![![5, 4, 3, 2, 6, 1], ![5, 3, 2, 4, 6, 0], ![5, 3, 1, 4, 0, 6], ![5, 2, 1, 4, 0, 6], ![5, 1, 2, 3, 0, 6], ![4, 3, 2, 1, 0, 6], ![1, 0, 2, 3, 4, 5]], proof := .tail 55 }

theorem namedLeaf005_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21509)) namedLeaf005 = true :=
  by decide +kernel

def namedLeaf006 : LeafData := { rows := ![![5, 4, 3, 2, 6, 1], ![3, 4, 2, 5, 6, 0], ![3, 4, 1, 5, 0, 6], ![2, 1, 4, 5, 0, 6], ![2, 1, 3, 5, 0, 6], ![1, 2, 3, 4, 0, 6], ![1, 0, 2, 3, 4, 5]], proof := .tail 72 }

theorem namedLeaf006_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21510)) namedLeaf006 = true :=
  by decide +kernel

def namedLeaf007 : LeafData := { rows := ![![5, 4, 3, 2, 6, 1], ![3, 4, 2, 5, 6, 0], ![3, 4, 1, 5, 0, 6], ![2, 1, 5, 4, 0, 6], ![2, 1, 5, 3, 0, 6], ![1, 2, 4, 3, 0, 6], ![1, 0, 2, 3, 4, 5]], proof := .tail 41 }

theorem namedLeaf007_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21511)) namedLeaf007 = true :=
  by decide +kernel

def namedLeaf008 : LeafData := { rows := ![![5, 4, 3, 2, 6, 1], ![4, 3, 2, 5, 6, 0], ![3, 4, 1, 5, 0, 6], ![2, 4, 1, 5, 0, 6], ![2, 3, 1, 5, 0, 6], ![1, 2, 3, 4, 0, 6], ![1, 0, 2, 3, 4, 5]], proof := .tail 190 }

theorem namedLeaf008_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21512)) namedLeaf008 = true :=
  by decide +kernel

def namedLeaf009 : LeafData := { rows := ![![5, 4, 3, 2, 6, 1], ![4, 3, 2, 5, 6, 0], ![4, 3, 1, 5, 0, 6], ![4, 2, 1, 5, 0, 6], ![3, 2, 1, 5, 0, 6], ![1, 2, 3, 4, 0, 6], ![1, 0, 2, 3, 4, 5]], proof := .tail 189 }

theorem namedLeaf009_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21513)) namedLeaf009 = true :=
  by decide +kernel

def namedLeaf010 : LeafData := { rows := ![![5, 4, 3, 2, 6, 1], ![3, 4, 5, 2, 6, 0], ![3, 4, 5, 1, 0, 6], ![2, 1, 4, 5, 0, 6], ![2, 1, 3, 5, 0, 6], ![2, 1, 3, 4, 0, 6], ![1, 0, 2, 3, 4, 5]], proof := .tail 155 }

theorem namedLeaf010_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21514)) namedLeaf010 = true :=
  by decide +kernel

def namedLeaf011 : LeafData := { rows := ![![5, 4, 3, 2, 6, 1], ![3, 4, 5, 2, 6, 0], ![3, 4, 5, 1, 0, 6], ![2, 1, 5, 4, 0, 6], ![2, 1, 5, 3, 0, 6], ![2, 1, 4, 3, 0, 6], ![1, 0, 2, 3, 4, 5]], proof := .tail 42 }

theorem namedLeaf011_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21515)) namedLeaf011 = true :=
  by decide +kernel

def namedLeaf012 : LeafData := { rows := ![![5, 4, 3, 2, 6, 1], ![3, 5, 4, 2, 6, 0], ![3, 4, 5, 1, 0, 6], ![2, 1, 5, 4, 0, 6], ![2, 5, 1, 3, 0, 6], ![2, 4, 1, 3, 0, 6], ![1, 0, 2, 3, 4, 5]], proof := .tail 47 }

theorem namedLeaf012_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21516)) namedLeaf012 = true :=
  by decide +kernel

def namedLeaf013 : LeafData := { rows := ![![5, 4, 3, 2, 6, 1], ![3, 5, 4, 2, 6, 0], ![3, 5, 4, 1, 0, 6], ![2, 1, 5, 4, 0, 6], ![5, 2, 1, 3, 0, 6], ![4, 2, 1, 3, 0, 6], ![1, 0, 2, 3, 4, 5]], proof := .tail 167 }

theorem namedLeaf013_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21517)) namedLeaf013 = true :=
  by decide +kernel

def namedLeaf014 : LeafData := { rows := ![![5, 4, 3, 2, 6, 1], ![5, 3, 4, 2, 6, 0], ![3, 4, 5, 1, 0, 6], ![2, 5, 1, 4, 0, 6], ![2, 5, 1, 3, 0, 6], ![2, 4, 3, 1, 0, 6], ![1, 0, 2, 3, 4, 5]], proof := .tail 4 }

theorem namedLeaf014_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21518)) namedLeaf014 = true :=
  by decide +kernel

def namedLeaf015 : LeafData := { rows := ![![5, 4, 3, 2, 6, 1], ![5, 3, 4, 2, 6, 0], ![3, 5, 4, 1, 0, 6], ![2, 5, 1, 4, 0, 6], ![5, 2, 1, 3, 0, 6], ![4, 2, 3, 1, 0, 6], ![1, 0, 2, 3, 4, 5]], proof := .tail 4 }

theorem namedLeaf015_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21519)) namedLeaf015 = true :=
  by decide +kernel

def namedLeaf016 : LeafData := { rows := ![![5, 4, 3, 2, 6, 1], ![5, 3, 4, 2, 6, 0], ![5, 3, 4, 1, 0, 6], ![5, 2, 1, 4, 0, 6], ![5, 2, 1, 3, 0, 6], ![4, 3, 2, 1, 0, 6], ![1, 0, 2, 3, 4, 5]], proof := .tail 79 }

theorem namedLeaf016_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21520)) namedLeaf016 = true :=
  by decide +kernel

def namedLeaf017 : LeafData := { rows := ![![5, 4, 3, 2, 6, 1], ![4, 3, 5, 2, 6, 0], ![3, 4, 5, 1, 0, 6], ![2, 4, 1, 5, 0, 6], ![2, 3, 1, 5, 0, 6], ![2, 1, 3, 4, 0, 6], ![1, 0, 2, 3, 4, 5]], proof := .tail 190 }

theorem namedLeaf017_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21521)) namedLeaf017 = true :=
  by decide +kernel

def namedLeaf018 : LeafData := { rows := ![![5, 4, 3, 2, 6, 1], ![4, 3, 5, 2, 6, 0], ![4, 3, 5, 1, 0, 6], ![4, 2, 1, 5, 0, 6], ![3, 2, 1, 5, 0, 6], ![2, 1, 3, 4, 0, 6], ![1, 0, 2, 3, 4, 5]], proof := .tail 2 }

theorem namedLeaf018_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21522)) namedLeaf018 = true :=
  by decide +kernel

def namedLeaf019 : LeafData := { rows := ![![5, 4, 3, 2, 6, 1], ![4, 5, 3, 2, 6, 0], ![3, 4, 5, 1, 0, 6], ![2, 4, 5, 1, 0, 6], ![2, 3, 1, 5, 0, 6], ![2, 3, 1, 4, 0, 6], ![1, 0, 2, 3, 4, 5]], proof := .tail 123 }

theorem namedLeaf019_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21523)) namedLeaf019 = true :=
  by decide +kernel

def namedLeaf020 : LeafData := { rows := ![![5, 4, 3, 2, 6, 1], ![4, 5, 3, 2, 6, 0], ![4, 3, 5, 1, 0, 6], ![4, 2, 5, 1, 0, 6], ![3, 2, 1, 5, 0, 6], ![2, 3, 1, 4, 0, 6], ![1, 0, 2, 3, 4, 5]], proof := .tail 51 }

theorem namedLeaf020_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21524)) namedLeaf020 = true :=
  by decide +kernel

def namedLeaf021 : LeafData := { rows := ![![5, 4, 3, 2, 6, 1], ![4, 5, 3, 2, 6, 0], ![4, 5, 3, 1, 0, 6], ![4, 5, 2, 1, 0, 6], ![3, 2, 1, 5, 0, 6], ![3, 2, 1, 4, 0, 6], ![1, 0, 2, 3, 4, 5]], proof := .tail 75 }

theorem namedLeaf021_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21525)) namedLeaf021 = true :=
  by decide +kernel

def namedLeaf022 : LeafData := { rows := ![![5, 4, 3, 2, 6, 1], ![5, 4, 3, 2, 6, 0], ![3, 4, 5, 1, 0, 6], ![2, 4, 5, 1, 0, 6], ![2, 3, 5, 1, 0, 6], ![2, 3, 4, 1, 0, 6], ![1, 0, 2, 3, 4, 5]], proof := .tail 43 }

theorem namedLeaf022_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21526)) namedLeaf022 = true :=
  by decide +kernel

def namedLeaf023 : LeafData := { rows := ![![5, 4, 3, 2, 6, 1], ![5, 4, 3, 2, 6, 0], ![3, 4, 5, 1, 0, 6], ![2, 5, 4, 1, 0, 6], ![2, 5, 3, 1, 0, 6], ![2, 4, 3, 1, 0, 6], ![1, 0, 2, 3, 4, 5]], proof := .tail 161 }

theorem namedLeaf023_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21527)) namedLeaf023 = true :=
  by decide +kernel

def namedLeaf024 : LeafData := { rows := ![![5, 4, 3, 2, 6, 1], ![5, 4, 3, 2, 6, 0], ![3, 5, 4, 1, 0, 6], ![2, 5, 4, 1, 0, 6], ![5, 2, 3, 1, 0, 6], ![4, 2, 3, 1, 0, 6], ![1, 0, 2, 3, 4, 5]], proof := .tail 110 }

theorem namedLeaf024_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21528)) namedLeaf024 = true :=
  by decide +kernel

def namedLeaf025 : LeafData := { rows := ![![5, 4, 3, 2, 6, 1], ![5, 4, 3, 2, 6, 0], ![5, 3, 4, 1, 0, 6], ![5, 2, 4, 1, 0, 6], ![5, 2, 3, 1, 0, 6], ![4, 3, 2, 1, 0, 6], ![1, 0, 2, 3, 4, 5]], proof := .tail 52 }

theorem namedLeaf025_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21529)) namedLeaf025 = true :=
  by decide +kernel

def namedLeaf026 : LeafData := { rows := ![![5, 4, 3, 2, 6, 1], ![5, 4, 3, 2, 6, 0], ![4, 3, 5, 1, 0, 6], ![4, 2, 5, 1, 0, 6], ![3, 2, 5, 1, 0, 6], ![2, 3, 4, 1, 0, 6], ![1, 0, 2, 3, 4, 5]], proof := .tail 125 }

theorem namedLeaf026_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21530)) namedLeaf026 = true :=
  by decide +kernel

def namedLeaf027 : LeafData := { rows := ![![5, 4, 3, 2, 6, 1], ![5, 4, 3, 2, 6, 0], ![4, 5, 3, 1, 0, 6], ![4, 5, 2, 1, 0, 6], ![3, 2, 5, 1, 0, 6], ![3, 2, 4, 1, 0, 6], ![1, 0, 2, 3, 4, 5]], proof := .tail 7 }

theorem namedLeaf027_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21531)) namedLeaf027 = true :=
  by decide +kernel

def namedLeaf028 : LeafData := { rows := ![![5, 4, 3, 2, 6, 1], ![5, 4, 3, 2, 6, 0], ![5, 4, 3, 1, 0, 6], ![4, 5, 2, 1, 0, 6], ![3, 5, 2, 1, 0, 6], ![3, 4, 2, 1, 0, 6], ![1, 0, 2, 3, 4, 5]], proof := .tail 140 }

theorem namedLeaf028_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21532)) namedLeaf028 = true :=
  by decide +kernel

def namedLeaf029 : LeafData := { rows := ![![5, 4, 3, 2, 6, 1], ![5, 4, 3, 2, 6, 0], ![5, 4, 3, 1, 0, 6], ![5, 4, 2, 1, 0, 6], ![5, 3, 2, 1, 0, 6], ![4, 3, 2, 1, 0, 6], ![1, 0, 2, 3, 4, 5]], proof := .tail 156 }

theorem namedLeaf029_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21533)) namedLeaf029 = true :=
  by decide +kernel

def namedLeaf030 : LeafData := { rows := ![![3, 4, 5, 6, 2, 1], ![2, 3, 4, 5, 6, 0], ![1, 3, 4, 5, 6, 0], ![1, 2, 0, 4, 5, 6], ![1, 2, 0, 3, 5, 6], ![1, 2, 0, 3, 4, 6], ![1, 2, 0, 3, 4, 5]], proof := .tail 144 }

theorem namedLeaf030_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21534)) namedLeaf030 = true :=
  by decide +kernel

def namedLeaf031 : LeafData := { rows := ![![3, 4, 5, 6, 2, 1], ![2, 3, 4, 5, 6, 0], ![1, 3, 4, 5, 6, 0], ![1, 2, 0, 4, 5, 6], ![1, 2, 0, 3, 6, 5], ![1, 2, 0, 3, 6, 4], ![1, 2, 0, 3, 5, 4]], proof := .tail 138 }

theorem namedLeaf031_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21535)) namedLeaf031 = true :=
  by decide +kernel

def namedLeaf032 : LeafData := { rows := ![![3, 4, 5, 6, 2, 1], ![2, 3, 4, 5, 6, 0], ![1, 3, 4, 5, 6, 0], ![1, 2, 0, 4, 6, 5], ![1, 2, 0, 3, 6, 5], ![1, 2, 0, 6, 3, 4], ![1, 2, 0, 5, 3, 4]], proof := .low (![136, 124, 143, 90, 126, 193, 159, 179, 80, 139, 40, 40, 70, 76, 196, 152, 181, 165, 187, 135, 158, 33, 67, 71, 48, 19, 56, 56]) }

theorem namedLeaf032_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21536)) namedLeaf032 = true :=
  by decide +kernel

def namedLeaf033 : LeafData := { rows := ![![3, 4, 6, 5, 2, 1], ![2, 3, 4, 5, 6, 0], ![1, 3, 4, 5, 6, 0], ![1, 2, 0, 4, 6, 5], ![1, 2, 0, 3, 6, 5], ![1, 2, 6, 0, 3, 4], ![1, 2, 5, 0, 3, 4]], proof := .tail 115 }

theorem namedLeaf033_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21537)) namedLeaf033 = true :=
  by decide +kernel

def namedLeaf034 : LeafData := { rows := ![![3, 4, 6, 5, 2, 1], ![2, 3, 4, 5, 6, 0], ![1, 3, 4, 6, 5, 0], ![1, 2, 0, 4, 6, 5], ![1, 2, 0, 3, 6, 5], ![1, 6, 2, 0, 3, 4], ![1, 5, 2, 0, 3, 4]], proof := .tail 142 }

theorem namedLeaf034_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21538)) namedLeaf034 = true :=
  by decide +kernel

def namedLeaf035 : LeafData := { rows := ![![3, 4, 6, 5, 2, 1], ![2, 3, 4, 6, 5, 0], ![1, 3, 4, 6, 5, 0], ![1, 2, 0, 4, 6, 5], ![1, 2, 0, 3, 6, 5], ![6, 1, 2, 0, 3, 4], ![5, 1, 2, 0, 3, 4]], proof := .low (![145, 124, 151, 194, 86, 30, 132, 49, 27, 27, 27, 96, 198, 53, 1, 137, 102, 44, 11, 129, 65, 133, 32, 5, 133, 197, 109, 0]) }

theorem namedLeaf035_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21539)) namedLeaf035 = true :=
  by decide +kernel

def namedLeaf036 : LeafData := { rows := ![![3, 4, 5, 6, 2, 1], ![2, 3, 4, 5, 6, 0], ![1, 3, 4, 5, 6, 0], ![1, 2, 0, 6, 4, 5], ![1, 2, 0, 6, 3, 5], ![1, 2, 0, 6, 3, 4], ![1, 2, 0, 5, 4, 3]], proof := .tail 184 }

theorem namedLeaf036_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21540)) namedLeaf036 = true :=
  by decide +kernel

def namedLeaf037 : LeafData := { rows := ![![3, 4, 6, 5, 2, 1], ![2, 3, 4, 5, 6, 0], ![1, 3, 4, 5, 6, 0], ![1, 2, 0, 6, 4, 5], ![1, 2, 0, 6, 3, 5], ![1, 2, 6, 0, 3, 4], ![1, 2, 5, 0, 4, 3]], proof := .tail 94 }

theorem namedLeaf037_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21541)) namedLeaf037 = true :=
  by decide +kernel

def namedLeaf038 : LeafData := { rows := ![![3, 4, 6, 5, 2, 1], ![2, 3, 4, 5, 6, 0], ![1, 3, 4, 6, 5, 0], ![1, 2, 0, 6, 4, 5], ![1, 2, 0, 6, 3, 5], ![1, 6, 2, 0, 3, 4], ![1, 5, 2, 0, 4, 3]], proof := .tail 146 }

theorem namedLeaf038_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21542)) namedLeaf038 = true :=
  by decide +kernel

def namedLeaf039 : LeafData := { rows := ![![3, 4, 6, 5, 2, 1], ![2, 3, 4, 6, 5, 0], ![1, 3, 4, 6, 5, 0], ![1, 2, 0, 6, 4, 5], ![1, 2, 0, 6, 3, 5], ![6, 1, 2, 0, 3, 4], ![5, 1, 2, 0, 4, 3]], proof := .tail 83 }

theorem namedLeaf039_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21543)) namedLeaf039 = true :=
  by decide +kernel

def namedLeaf040 : LeafData := { rows := ![![3, 6, 4, 5, 2, 1], ![2, 3, 4, 5, 6, 0], ![1, 3, 4, 5, 6, 0], ![1, 2, 0, 6, 4, 5], ![1, 2, 6, 0, 3, 5], ![1, 2, 6, 0, 3, 4], ![1, 2, 5, 4, 0, 3]], proof := .tail 93 }

theorem namedLeaf040_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21544)) namedLeaf040 = true :=
  by decide +kernel

def namedLeaf041 : LeafData := { rows := ![![3, 6, 4, 5, 2, 1], ![2, 3, 4, 5, 6, 0], ![1, 3, 4, 6, 5, 0], ![1, 2, 0, 6, 4, 5], ![1, 2, 6, 0, 3, 5], ![1, 6, 2, 0, 3, 4], ![1, 5, 2, 4, 0, 3]], proof := .tail 174 }

theorem namedLeaf041_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21545)) namedLeaf041 = true :=
  by decide +kernel

def namedLeaf042 : LeafData := { rows := ![![3, 6, 4, 5, 2, 1], ![2, 3, 4, 5, 6, 0], ![1, 3, 6, 4, 5, 0], ![1, 2, 0, 6, 4, 5], ![1, 6, 2, 0, 3, 5], ![1, 6, 2, 0, 3, 4], ![1, 5, 4, 2, 0, 3]], proof := .tail 121 }

theorem namedLeaf042_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21546)) namedLeaf042 = true :=
  by decide +kernel

def namedLeaf043 : LeafData := { rows := ![![3, 6, 4, 5, 2, 1], ![2, 3, 4, 6, 5, 0], ![1, 3, 4, 6, 5, 0], ![1, 2, 0, 6, 4, 5], ![1, 2, 6, 0, 3, 5], ![6, 1, 2, 0, 3, 4], ![5, 1, 2, 4, 0, 3]], proof := .tail 147 }

theorem namedLeaf043_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21547)) namedLeaf043 = true :=
  by decide +kernel

def namedLeaf044 : LeafData := { rows := ![![3, 6, 4, 5, 2, 1], ![2, 3, 4, 6, 5, 0], ![1, 3, 6, 4, 5, 0], ![1, 2, 0, 6, 4, 5], ![1, 6, 2, 0, 3, 5], ![6, 1, 2, 0, 3, 4], ![5, 1, 4, 2, 0, 3]], proof := .tail 114 }

theorem namedLeaf044_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21548)) namedLeaf044 = true :=
  by decide +kernel

def namedLeaf045 : LeafData := { rows := ![![3, 6, 4, 5, 2, 1], ![2, 3, 6, 4, 5, 0], ![1, 3, 6, 4, 5, 0], ![1, 2, 0, 6, 4, 5], ![6, 1, 2, 0, 3, 5], ![6, 1, 2, 0, 3, 4], ![5, 4, 1, 2, 0, 3]], proof := .tail 100 }

theorem namedLeaf045_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21549)) namedLeaf045 = true :=
  by decide +kernel

def namedLeaf046 : LeafData := { rows := ![![3, 4, 5, 6, 2, 1], ![2, 3, 4, 5, 6, 0], ![1, 3, 4, 5, 6, 0], ![1, 2, 0, 5, 4, 6], ![1, 2, 0, 5, 3, 6], ![1, 2, 0, 4, 3, 6], ![1, 2, 0, 3, 4, 5]], proof := .tail 60 }

theorem namedLeaf046_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21550)) namedLeaf046 = true :=
  by decide +kernel

def namedLeaf047 : LeafData := { rows := ![![3, 4, 5, 6, 2, 1], ![2, 3, 4, 5, 6, 0], ![1, 3, 4, 5, 6, 0], ![1, 2, 0, 5, 6, 4], ![1, 2, 0, 5, 6, 3], ![1, 2, 0, 4, 3, 6], ![1, 2, 0, 4, 3, 5]], proof := .low (![136, 124, 143, 38, 126, 193, 159, 179, 80, 40, 40, 40, 70, 76, 196, 152, 181, 165, 187, 135, 158, 33, 67, 71, 56, 19, 56, 56]) }

theorem namedLeaf047_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21551)) namedLeaf047 = true :=
  by decide +kernel

def namedLeaf048 : LeafData := { rows := ![![3, 4, 5, 6, 2, 1], ![2, 3, 4, 5, 6, 0], ![1, 3, 4, 5, 6, 0], ![1, 2, 0, 6, 5, 4], ![1, 2, 0, 5, 6, 3], ![1, 2, 0, 4, 6, 3], ![1, 2, 0, 4, 5, 3]], proof := .tail 169 }

theorem namedLeaf048_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21552)) namedLeaf048 = true :=
  by decide +kernel

def namedLeaf049 : LeafData := { rows := ![![3, 4, 5, 6, 2, 1], ![2, 3, 4, 5, 6, 0], ![1, 3, 4, 5, 6, 0], ![1, 2, 0, 6, 5, 4], ![1, 2, 0, 6, 5, 3], ![1, 2, 0, 6, 4, 3], ![1, 2, 0, 5, 4, 3]], proof := .tail 62 }

theorem namedLeaf049_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21553)) namedLeaf049 = true :=
  by decide +kernel

def namedLeaf050 : LeafData := { rows := ![![3, 4, 6, 5, 2, 1], ![2, 3, 4, 5, 6, 0], ![1, 3, 4, 5, 6, 0], ![1, 2, 0, 6, 5, 4], ![1, 2, 0, 6, 5, 3], ![1, 2, 6, 0, 4, 3], ![1, 2, 5, 0, 4, 3]], proof := .tail 57 }

theorem namedLeaf050_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21554)) namedLeaf050 = true :=
  by decide +kernel

def namedLeaf051 : LeafData := { rows := ![![3, 4, 6, 5, 2, 1], ![2, 3, 4, 5, 6, 0], ![1, 3, 4, 6, 5, 0], ![1, 2, 0, 6, 5, 4], ![1, 2, 0, 6, 5, 3], ![1, 6, 2, 0, 4, 3], ![1, 5, 2, 0, 4, 3]], proof := .tail 142 }

theorem namedLeaf051_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21555)) namedLeaf051 = true :=
  by decide +kernel

def namedLeaf052 : LeafData := { rows := ![![3, 4, 6, 5, 2, 1], ![2, 3, 4, 6, 5, 0], ![1, 3, 4, 6, 5, 0], ![1, 2, 0, 6, 5, 4], ![1, 2, 0, 6, 5, 3], ![6, 1, 2, 0, 4, 3], ![5, 1, 2, 0, 4, 3]], proof := .low (![145, 124, 28, 194, 86, 188, 132, 49, 24, 27, 27, 77, 198, 53, 1, 137, 102, 44, 11, 129, 65, 25, 32, 5, 133, 197, 109, 182]) }

theorem namedLeaf052_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21556)) namedLeaf052 = true :=
  by decide +kernel

def namedLeaf053 : LeafData := { rows := ![![3, 6, 4, 5, 2, 1], ![2, 3, 4, 5, 6, 0], ![1, 3, 4, 5, 6, 0], ![1, 2, 0, 6, 5, 4], ![1, 2, 6, 0, 5, 3], ![1, 2, 6, 0, 4, 3], ![1, 2, 5, 4, 0, 3]], proof := .tail 171 }

theorem namedLeaf053_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21557)) namedLeaf053 = true :=
  by decide +kernel

def namedLeaf054 : LeafData := { rows := ![![3, 6, 4, 5, 2, 1], ![2, 3, 4, 5, 6, 0], ![1, 3, 4, 6, 5, 0], ![1, 2, 0, 6, 5, 4], ![1, 2, 6, 0, 5, 3], ![1, 6, 2, 0, 4, 3], ![1, 5, 2, 4, 0, 3]], proof := .tail 171 }

theorem namedLeaf054_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21558)) namedLeaf054 = true :=
  by decide +kernel

def namedLeaf055 : LeafData := { rows := ![![3, 6, 4, 5, 2, 1], ![2, 3, 4, 5, 6, 0], ![1, 3, 6, 4, 5, 0], ![1, 2, 0, 6, 5, 4], ![1, 6, 2, 0, 5, 3], ![1, 6, 2, 0, 4, 3], ![1, 5, 4, 2, 0, 3]], proof := .tail 69 }

theorem namedLeaf055_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21559)) namedLeaf055 = true :=
  by decide +kernel

def namedLeaf056 : LeafData := { rows := ![![3, 6, 4, 5, 2, 1], ![2, 3, 4, 6, 5, 0], ![1, 3, 4, 6, 5, 0], ![1, 2, 0, 6, 5, 4], ![1, 2, 6, 0, 5, 3], ![6, 1, 2, 0, 4, 3], ![5, 1, 2, 4, 0, 3]], proof := .tail 171 }

theorem namedLeaf056_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21560)) namedLeaf056 = true :=
  by decide +kernel

def namedLeaf057 : LeafData := { rows := ![![3, 6, 4, 5, 2, 1], ![2, 3, 4, 6, 5, 0], ![1, 3, 6, 4, 5, 0], ![1, 2, 0, 6, 5, 4], ![1, 6, 2, 0, 5, 3], ![6, 1, 2, 0, 4, 3], ![5, 1, 4, 2, 0, 3]], proof := .tail 69 }

theorem namedLeaf057_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21561)) namedLeaf057 = true :=
  by decide +kernel

def namedLeaf058 : LeafData := { rows := ![![3, 6, 4, 5, 2, 1], ![2, 3, 6, 4, 5, 0], ![1, 3, 6, 4, 5, 0], ![1, 2, 0, 6, 5, 4], ![6, 1, 2, 0, 5, 3], ![6, 1, 2, 0, 4, 3], ![5, 4, 1, 2, 0, 3]], proof := .tail 36 }

theorem namedLeaf058_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21562)) namedLeaf058 = true :=
  by decide +kernel

def namedLeaf059 : LeafData := { rows := ![![3, 5, 4, 6, 2, 1], ![2, 3, 4, 5, 6, 0], ![1, 3, 4, 5, 6, 0], ![1, 2, 0, 5, 4, 6], ![1, 2, 5, 0, 3, 6], ![1, 2, 4, 0, 3, 6], ![1, 2, 0, 3, 4, 5]], proof := .tail 157 }

theorem namedLeaf059_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21563)) namedLeaf059 = true :=
  by decide +kernel

def namedLeaf060 : LeafData := { rows := ![![3, 5, 4, 6, 2, 1], ![2, 3, 4, 5, 6, 0], ![1, 3, 4, 5, 6, 0], ![1, 2, 0, 5, 6, 4], ![1, 2, 5, 0, 6, 3], ![1, 2, 4, 0, 3, 6], ![1, 2, 0, 4, 3, 5]], proof := .tail 149 }

theorem namedLeaf060_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21564)) namedLeaf060 = true :=
  by decide +kernel

def namedLeaf061 : LeafData := { rows := ![![3, 5, 4, 6, 2, 1], ![2, 3, 4, 5, 6, 0], ![1, 3, 4, 5, 6, 0], ![1, 2, 0, 6, 5, 4], ![1, 2, 5, 0, 6, 3], ![1, 2, 4, 0, 6, 3], ![1, 2, 0, 4, 5, 3]], proof := .tail 16 }

theorem namedLeaf061_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21565)) namedLeaf061 = true :=
  by decide +kernel

def namedLeaf062 : LeafData := { rows := ![![3, 5, 6, 4, 2, 1], ![2, 3, 4, 5, 6, 0], ![1, 3, 4, 5, 6, 0], ![1, 2, 0, 5, 6, 4], ![1, 2, 5, 6, 0, 3], ![1, 2, 4, 0, 3, 6], ![1, 2, 4, 0, 3, 5]], proof := .tail 175 }

theorem namedLeaf062_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21566)) namedLeaf062 = true :=
  by decide +kernel

def namedLeaf063 : LeafData := { rows := ![![3, 5, 6, 4, 2, 1], ![2, 3, 4, 5, 6, 0], ![1, 3, 4, 5, 6, 0], ![1, 2, 0, 6, 5, 4], ![1, 2, 5, 6, 0, 3], ![1, 2, 4, 0, 6, 3], ![1, 2, 4, 0, 5, 3]], proof := .tail 99 }

theorem namedLeaf063_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21567)) namedLeaf063 = true :=
  by decide +kernel

def namedLeaf064 : LeafData := { rows := ![![3, 6, 5, 4, 2, 1], ![2, 3, 4, 5, 6, 0], ![1, 3, 4, 5, 6, 0], ![1, 2, 0, 6, 5, 4], ![1, 2, 5, 6, 0, 3], ![1, 2, 4, 6, 0, 3], ![1, 2, 4, 5, 0, 3]], proof := .tail 185 }

theorem namedLeaf064_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21568)) namedLeaf064 = true :=
  by decide +kernel

def namedLeaf065 : LeafData := { rows := ![![3, 6, 5, 4, 2, 1], ![2, 3, 4, 5, 6, 0], ![1, 3, 4, 5, 6, 0], ![1, 2, 0, 6, 5, 4], ![1, 2, 6, 5, 0, 3], ![1, 2, 6, 4, 0, 3], ![1, 2, 5, 4, 0, 3]], proof := .tail 54 }

theorem namedLeaf065_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21569)) namedLeaf065 = true :=
  by decide +kernel

def namedLeaf066 : LeafData := { rows := ![![3, 6, 5, 4, 2, 1], ![2, 3, 4, 5, 6, 0], ![1, 3, 4, 6, 5, 0], ![1, 2, 0, 6, 5, 4], ![1, 2, 6, 5, 0, 3], ![1, 6, 2, 4, 0, 3], ![1, 5, 2, 4, 0, 3]], proof := .tail 195 }

theorem namedLeaf066_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21570)) namedLeaf066 = true :=
  by decide +kernel

def namedLeaf067 : LeafData := { rows := ![![3, 6, 5, 4, 2, 1], ![2, 3, 4, 6, 5, 0], ![1, 3, 4, 6, 5, 0], ![1, 2, 0, 6, 5, 4], ![1, 2, 6, 5, 0, 3], ![6, 1, 2, 4, 0, 3], ![5, 1, 2, 4, 0, 3]], proof := .tail 195 }

theorem namedLeaf067_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21571)) namedLeaf067 = true :=
  by decide +kernel

def namedLeaf068 : LeafData := { rows := ![![3, 6, 5, 4, 2, 1], ![2, 3, 4, 5, 6, 0], ![1, 3, 6, 4, 5, 0], ![1, 2, 0, 6, 5, 4], ![1, 6, 2, 5, 0, 3], ![1, 6, 2, 4, 0, 3], ![1, 5, 4, 2, 0, 3]], proof := .tail 84 }

theorem namedLeaf068_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21572)) namedLeaf068 = true :=
  by decide +kernel

def namedLeaf069 : LeafData := { rows := ![![3, 6, 5, 4, 2, 1], ![2, 3, 4, 6, 5, 0], ![1, 3, 6, 4, 5, 0], ![1, 2, 0, 6, 5, 4], ![1, 6, 2, 5, 0, 3], ![6, 1, 2, 4, 0, 3], ![5, 1, 4, 2, 0, 3]], proof := .tail 98 }

theorem namedLeaf069_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21573)) namedLeaf069 = true :=
  by decide +kernel

def namedLeaf070 : LeafData := { rows := ![![3, 6, 5, 4, 2, 1], ![2, 3, 6, 4, 5, 0], ![1, 3, 6, 4, 5, 0], ![1, 2, 0, 6, 5, 4], ![6, 1, 2, 5, 0, 3], ![6, 1, 2, 4, 0, 3], ![5, 4, 1, 2, 0, 3]], proof := .tail 117 }

theorem namedLeaf070_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21574)) namedLeaf070 = true :=
  by decide +kernel

def namedLeaf071 : LeafData := { rows := ![![3, 5, 4, 6, 2, 1], ![2, 3, 4, 5, 6, 0], ![1, 3, 5, 4, 6, 0], ![1, 2, 0, 5, 4, 6], ![1, 5, 2, 0, 3, 6], ![1, 4, 2, 0, 3, 6], ![1, 2, 0, 3, 4, 5]], proof := .tail 13 }

theorem namedLeaf071_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21575)) namedLeaf071 = true :=
  by decide +kernel

def namedLeaf072 : LeafData := { rows := ![![3, 5, 4, 6, 2, 1], ![2, 3, 4, 5, 6, 0], ![1, 3, 5, 4, 6, 0], ![1, 2, 0, 5, 6, 4], ![1, 5, 2, 0, 6, 3], ![1, 4, 2, 0, 3, 6], ![1, 2, 0, 4, 3, 5]], proof := .tail 66 }

theorem namedLeaf072_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21576)) namedLeaf072 = true :=
  by decide +kernel

def namedLeaf073 : LeafData := { rows := ![![3, 5, 4, 6, 2, 1], ![2, 3, 4, 5, 6, 0], ![1, 3, 5, 4, 6, 0], ![1, 2, 0, 6, 5, 4], ![1, 5, 2, 0, 6, 3], ![1, 4, 2, 0, 6, 3], ![1, 2, 0, 4, 5, 3]], proof := .tail 172 }

theorem namedLeaf073_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21577)) namedLeaf073 = true :=
  by decide +kernel

def namedLeaf074 : LeafData := { rows := ![![3, 5, 6, 4, 2, 1], ![2, 3, 4, 5, 6, 0], ![1, 3, 5, 4, 6, 0], ![1, 2, 0, 5, 6, 4], ![1, 5, 2, 6, 0, 3], ![1, 4, 2, 0, 3, 6], ![1, 2, 4, 0, 3, 5]], proof := .tail 112 }

theorem namedLeaf074_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21578)) namedLeaf074 = true :=
  by decide +kernel

def namedLeaf075 : LeafData := { rows := ![![3, 5, 6, 4, 2, 1], ![2, 3, 4, 5, 6, 0], ![1, 3, 5, 4, 6, 0], ![1, 2, 0, 6, 5, 4], ![1, 5, 2, 6, 0, 3], ![1, 4, 2, 0, 6, 3], ![1, 2, 4, 0, 5, 3]], proof := .tail 112 }

theorem namedLeaf075_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21579)) namedLeaf075 = true :=
  by decide +kernel

def namedLeaf076 : LeafData := { rows := ![![3, 6, 5, 4, 2, 1], ![2, 3, 4, 5, 6, 0], ![1, 3, 5, 4, 6, 0], ![1, 2, 0, 6, 5, 4], ![1, 5, 2, 6, 0, 3], ![1, 4, 2, 6, 0, 3], ![1, 2, 4, 5, 0, 3]], proof := .tail 10 }

theorem namedLeaf076_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21580)) namedLeaf076 = true :=
  by decide +kernel

def namedLeaf077 : LeafData := { rows := ![![3, 5, 6, 4, 2, 1], ![2, 3, 4, 5, 6, 0], ![1, 3, 5, 6, 4, 0], ![1, 2, 0, 5, 6, 4], ![1, 5, 6, 2, 0, 3], ![1, 4, 2, 0, 3, 6], ![1, 4, 2, 0, 3, 5]], proof := .tail 103 }

theorem namedLeaf077_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21581)) namedLeaf077 = true :=
  by decide +kernel

def namedLeaf078 : LeafData := { rows := ![![3, 5, 6, 4, 2, 1], ![2, 3, 4, 5, 6, 0], ![1, 3, 5, 6, 4, 0], ![1, 2, 0, 6, 5, 4], ![1, 5, 6, 2, 0, 3], ![1, 4, 2, 0, 6, 3], ![1, 4, 2, 0, 5, 3]], proof := .tail 103 }

theorem namedLeaf078_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21582)) namedLeaf078 = true :=
  by decide +kernel

def namedLeaf079 : LeafData := { rows := ![![3, 6, 5, 4, 2, 1], ![2, 3, 4, 5, 6, 0], ![1, 3, 5, 6, 4, 0], ![1, 2, 0, 6, 5, 4], ![1, 5, 6, 2, 0, 3], ![1, 4, 2, 6, 0, 3], ![1, 4, 2, 5, 0, 3]], proof := .tail 22 }

theorem namedLeaf079_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21583)) namedLeaf079 = true :=
  by decide +kernel

def namedLeaf080 : LeafData := { rows := ![![3, 6, 5, 4, 2, 1], ![2, 3, 4, 5, 6, 0], ![1, 3, 6, 5, 4, 0], ![1, 2, 0, 6, 5, 4], ![1, 5, 6, 2, 0, 3], ![1, 4, 6, 2, 0, 3], ![1, 4, 5, 2, 0, 3]], proof := .tail 177 }

theorem namedLeaf080_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21584)) namedLeaf080 = true :=
  by decide +kernel

def namedLeaf081 : LeafData := { rows := ![![3, 6, 5, 4, 2, 1], ![2, 3, 4, 5, 6, 0], ![1, 3, 6, 5, 4, 0], ![1, 2, 0, 6, 5, 4], ![1, 6, 5, 2, 0, 3], ![1, 6, 4, 2, 0, 3], ![1, 5, 4, 2, 0, 3]], proof := .tail 82 }

theorem namedLeaf081_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21585)) namedLeaf081 = true :=
  by decide +kernel

def namedLeaf082 : LeafData := { rows := ![![3, 6, 5, 4, 2, 1], ![2, 3, 4, 6, 5, 0], ![1, 3, 6, 5, 4, 0], ![1, 2, 0, 6, 5, 4], ![1, 6, 5, 2, 0, 3], ![6, 1, 4, 2, 0, 3], ![5, 1, 4, 2, 0, 3]], proof := .tail 95 }

theorem namedLeaf082_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21586)) namedLeaf082 = true :=
  by decide +kernel

def namedLeaf083 : LeafData := { rows := ![![3, 6, 5, 4, 2, 1], ![2, 3, 6, 4, 5, 0], ![1, 3, 6, 5, 4, 0], ![1, 2, 0, 6, 5, 4], ![6, 1, 5, 2, 0, 3], ![6, 1, 4, 2, 0, 3], ![5, 4, 1, 2, 0, 3]], proof := .tail 12 }

theorem namedLeaf083_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21587)) namedLeaf083 = true :=
  by decide +kernel

def namedLeaf084 : LeafData := { rows := ![![3, 5, 4, 6, 2, 1], ![2, 3, 5, 4, 6, 0], ![1, 3, 5, 4, 6, 0], ![1, 2, 0, 5, 4, 6], ![5, 1, 2, 0, 3, 6], ![4, 1, 2, 0, 3, 6], ![1, 2, 0, 3, 4, 5]], proof := .low (![89, 124, 104, 46, 23, 3, 107, 116, 17, 17, 17, 17, 85, 192, 128, 34, 181, 61, 59, 39, 199, 106, 148, 21, 26, 87, 106, 118]) }

theorem namedLeaf084_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21588)) namedLeaf084 = true :=
  by decide +kernel

def namedLeaf085 : LeafData := { rows := ![![3, 5, 4, 6, 2, 1], ![2, 3, 5, 4, 6, 0], ![1, 3, 5, 4, 6, 0], ![1, 2, 0, 5, 6, 4], ![5, 1, 2, 0, 6, 3], ![4, 1, 2, 0, 3, 6], ![1, 2, 0, 4, 3, 5]], proof := .tail 166 }

theorem namedLeaf085_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21589)) namedLeaf085 = true :=
  by decide +kernel

def namedLeaf086 : LeafData := { rows := ![![3, 5, 4, 6, 2, 1], ![2, 3, 5, 4, 6, 0], ![1, 3, 5, 4, 6, 0], ![1, 2, 0, 6, 5, 4], ![5, 1, 2, 0, 6, 3], ![4, 1, 2, 0, 6, 3], ![1, 2, 0, 4, 5, 3]], proof := .tail 168 }

theorem namedLeaf086_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21590)) namedLeaf086 = true :=
  by decide +kernel

def namedLeaf087 : LeafData := { rows := ![![3, 5, 6, 4, 2, 1], ![2, 3, 5, 4, 6, 0], ![1, 3, 5, 4, 6, 0], ![1, 2, 0, 5, 6, 4], ![5, 1, 2, 6, 0, 3], ![4, 1, 2, 0, 3, 6], ![1, 2, 4, 0, 3, 5]], proof := .tail 108 }

theorem namedLeaf087_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21591)) namedLeaf087 = true :=
  by decide +kernel

def namedLeaf088 : LeafData := { rows := ![![3, 5, 6, 4, 2, 1], ![2, 3, 5, 4, 6, 0], ![1, 3, 5, 4, 6, 0], ![1, 2, 0, 6, 5, 4], ![5, 1, 2, 6, 0, 3], ![4, 1, 2, 0, 6, 3], ![1, 2, 4, 0, 5, 3]], proof := .tail 176 }

theorem namedLeaf088_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21592)) namedLeaf088 = true :=
  by decide +kernel

def namedLeaf089 : LeafData := { rows := ![![3, 6, 5, 4, 2, 1], ![2, 3, 5, 4, 6, 0], ![1, 3, 5, 4, 6, 0], ![1, 2, 0, 6, 5, 4], ![5, 1, 2, 6, 0, 3], ![4, 1, 2, 6, 0, 3], ![1, 2, 4, 5, 0, 3]], proof := .tail 113 }

theorem namedLeaf089_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21593)) namedLeaf089 = true :=
  by decide +kernel

def namedLeaf090 : LeafData := { rows := ![![3, 5, 6, 4, 2, 1], ![2, 3, 5, 4, 6, 0], ![1, 3, 5, 6, 4, 0], ![1, 2, 0, 5, 6, 4], ![5, 1, 6, 2, 0, 3], ![4, 1, 2, 0, 3, 6], ![1, 4, 2, 0, 3, 5]], proof := .tail 63 }

theorem namedLeaf090_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21594)) namedLeaf090 = true :=
  by decide +kernel

def namedLeaf091 : LeafData := { rows := ![![3, 5, 6, 4, 2, 1], ![2, 3, 5, 4, 6, 0], ![1, 3, 5, 6, 4, 0], ![1, 2, 0, 6, 5, 4], ![5, 1, 6, 2, 0, 3], ![4, 1, 2, 0, 6, 3], ![1, 4, 2, 0, 5, 3]], proof := .tail 63 }

theorem namedLeaf091_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21595)) namedLeaf091 = true :=
  by decide +kernel

def namedLeaf092 : LeafData := { rows := ![![3, 6, 5, 4, 2, 1], ![2, 3, 5, 4, 6, 0], ![1, 3, 5, 6, 4, 0], ![1, 2, 0, 6, 5, 4], ![5, 1, 6, 2, 0, 3], ![4, 1, 2, 6, 0, 3], ![1, 4, 2, 5, 0, 3]], proof := .tail 63 }

theorem namedLeaf092_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21596)) namedLeaf092 = true :=
  by decide +kernel

def namedLeaf093 : LeafData := { rows := ![![3, 6, 5, 4, 2, 1], ![2, 3, 5, 4, 6, 0], ![1, 3, 6, 5, 4, 0], ![1, 2, 0, 6, 5, 4], ![5, 1, 6, 2, 0, 3], ![4, 1, 6, 2, 0, 3], ![1, 4, 5, 2, 0, 3]], proof := .tail 180 }

theorem namedLeaf093_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21597)) namedLeaf093 = true :=
  by decide +kernel

def namedLeaf094 : LeafData := { rows := ![![3, 5, 6, 4, 2, 1], ![2, 3, 5, 6, 4, 0], ![1, 3, 5, 6, 4, 0], ![1, 2, 0, 5, 6, 4], ![5, 6, 1, 2, 0, 3], ![4, 1, 2, 0, 3, 6], ![4, 1, 2, 0, 3, 5]], proof := .low (![120, 124, 8, 150, 162, 97, 9, 14, 78, 78, 78, 78, 119, 29, 160, 81, 15, 111, 134, 50, 153, 105, 88, 18, 105, 68, 58, 92]) }

theorem namedLeaf094_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21598)) namedLeaf094 = true :=
  by decide +kernel

def namedLeaf095 : LeafData := { rows := ![![3, 5, 6, 4, 2, 1], ![2, 3, 5, 6, 4, 0], ![1, 3, 5, 6, 4, 0], ![1, 2, 0, 6, 5, 4], ![5, 6, 1, 2, 0, 3], ![4, 1, 2, 0, 6, 3], ![4, 1, 2, 0, 5, 3]], proof := .low (![120, 124, 130, 150, 162, 97, 9, 14, 91, 78, 78, 170, 119, 29, 160, 81, 15, 111, 134, 50, 153, 45, 88, 18, 105, 68, 58, 92]) }

theorem namedLeaf095_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21599)) namedLeaf095 = true :=
  by decide +kernel

def namedLeaf096 : LeafData := { rows := ![![3, 6, 5, 4, 2, 1], ![2, 3, 5, 6, 4, 0], ![1, 3, 5, 6, 4, 0], ![1, 2, 0, 6, 5, 4], ![5, 6, 1, 2, 0, 3], ![4, 1, 2, 6, 0, 3], ![4, 1, 2, 5, 0, 3]], proof := .tail 22 }

theorem namedLeaf096_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21600)) namedLeaf096 = true :=
  by decide +kernel

def namedLeaf097 : LeafData := { rows := ![![3, 6, 5, 4, 2, 1], ![2, 3, 5, 6, 4, 0], ![1, 3, 6, 5, 4, 0], ![1, 2, 0, 6, 5, 4], ![5, 6, 1, 2, 0, 3], ![4, 1, 6, 2, 0, 3], ![4, 1, 5, 2, 0, 3]], proof := .tail 37 }

theorem namedLeaf097_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21601)) namedLeaf097 = true :=
  by decide +kernel

def namedLeaf098 : LeafData := { rows := ![![3, 6, 5, 4, 2, 1], ![2, 3, 6, 5, 4, 0], ![1, 3, 6, 5, 4, 0], ![1, 2, 0, 6, 5, 4], ![5, 6, 1, 2, 0, 3], ![4, 6, 1, 2, 0, 3], ![4, 5, 1, 2, 0, 3]], proof := .tail 73 }

theorem namedLeaf098_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21602)) namedLeaf098 = true :=
  by decide +kernel

def namedLeaf099 : LeafData := { rows := ![![3, 6, 5, 4, 2, 1], ![2, 3, 6, 5, 4, 0], ![1, 3, 6, 5, 4, 0], ![1, 2, 0, 6, 5, 4], ![6, 5, 1, 2, 0, 3], ![6, 4, 1, 2, 0, 3], ![5, 4, 1, 2, 0, 3]], proof := .tail 122 }

theorem namedLeaf099_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21603)) namedLeaf099 = true :=
  by decide +kernel

def namedLeaf100 : LeafData := { rows := ![![6, 3, 4, 5, 2, 1], ![2, 3, 4, 5, 6, 0], ![1, 3, 4, 5, 6, 0], ![1, 2, 6, 0, 4, 5], ![1, 2, 6, 0, 3, 5], ![1, 2, 6, 0, 3, 4], ![1, 2, 5, 4, 3, 0]], proof := .tail 154 }

theorem namedLeaf100_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21604)) namedLeaf100 = true :=
  by decide +kernel

def namedLeaf101 : LeafData := { rows := ![![6, 3, 4, 5, 2, 1], ![2, 3, 4, 5, 6, 0], ![1, 3, 4, 6, 5, 0], ![1, 2, 6, 0, 4, 5], ![1, 2, 6, 0, 3, 5], ![1, 6, 2, 0, 3, 4], ![1, 5, 2, 4, 3, 0]], proof := .tail 154 }

theorem namedLeaf101_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21605)) namedLeaf101 = true :=
  by decide +kernel

def namedLeaf102 : LeafData := { rows := ![![6, 3, 4, 5, 2, 1], ![2, 3, 4, 5, 6, 0], ![1, 3, 6, 4, 5, 0], ![1, 2, 6, 0, 4, 5], ![1, 6, 2, 0, 3, 5], ![1, 6, 2, 0, 3, 4], ![1, 5, 4, 2, 3, 0]], proof := .tail 154 }

theorem namedLeaf102_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21606)) namedLeaf102 = true :=
  by decide +kernel

def namedLeaf103 : LeafData := { rows := ![![6, 3, 4, 5, 2, 1], ![2, 3, 4, 5, 6, 0], ![1, 6, 3, 4, 5, 0], ![1, 6, 2, 0, 4, 5], ![1, 6, 2, 0, 3, 5], ![1, 6, 2, 0, 3, 4], ![1, 5, 4, 3, 2, 0]], proof := .tail 173 }

theorem namedLeaf103_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21607)) namedLeaf103 = true :=
  by decide +kernel

def namedLeaf104 : LeafData := { rows := ![![6, 3, 4, 5, 2, 1], ![2, 3, 4, 6, 5, 0], ![1, 3, 4, 6, 5, 0], ![1, 2, 6, 0, 4, 5], ![1, 2, 6, 0, 3, 5], ![6, 1, 2, 0, 3, 4], ![5, 1, 2, 4, 3, 0]], proof := .tail 154 }

theorem namedLeaf104_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21608)) namedLeaf104 = true :=
  by decide +kernel

def namedLeaf105 : LeafData := { rows := ![![6, 3, 4, 5, 2, 1], ![2, 3, 4, 6, 5, 0], ![1, 3, 6, 4, 5, 0], ![1, 2, 6, 0, 4, 5], ![1, 6, 2, 0, 3, 5], ![6, 1, 2, 0, 3, 4], ![5, 1, 4, 2, 3, 0]], proof := .tail 154 }

theorem namedLeaf105_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21609)) namedLeaf105 = true :=
  by decide +kernel

def namedLeaf106 : LeafData := { rows := ![![6, 3, 4, 5, 2, 1], ![2, 3, 4, 6, 5, 0], ![1, 6, 3, 4, 5, 0], ![1, 6, 2, 0, 4, 5], ![1, 6, 2, 0, 3, 5], ![6, 1, 2, 0, 3, 4], ![5, 1, 4, 3, 2, 0]], proof := .tail 20 }

theorem namedLeaf106_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21610)) namedLeaf106 = true :=
  by decide +kernel

def namedLeaf107 : LeafData := { rows := ![![6, 3, 4, 5, 2, 1], ![2, 3, 6, 4, 5, 0], ![1, 3, 6, 4, 5, 0], ![1, 2, 6, 0, 4, 5], ![6, 1, 2, 0, 3, 5], ![6, 1, 2, 0, 3, 4], ![5, 4, 1, 2, 3, 0]], proof := .tail 154 }

theorem namedLeaf107_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21611)) namedLeaf107 = true :=
  by decide +kernel

def namedLeaf108 : LeafData := { rows := ![![6, 3, 4, 5, 2, 1], ![2, 3, 6, 4, 5, 0], ![1, 6, 3, 4, 5, 0], ![1, 6, 2, 0, 4, 5], ![6, 1, 2, 0, 3, 5], ![6, 1, 2, 0, 3, 4], ![5, 4, 1, 3, 2, 0]], proof := .tail 141 }

theorem namedLeaf108_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21612)) namedLeaf108 = true :=
  by decide +kernel

def namedLeaf109 : LeafData := { rows := ![![6, 3, 4, 5, 2, 1], ![2, 6, 3, 4, 5, 0], ![1, 6, 3, 4, 5, 0], ![6, 1, 2, 0, 4, 5], ![6, 1, 2, 0, 3, 5], ![6, 1, 2, 0, 3, 4], ![5, 4, 3, 1, 2, 0]], proof := .tail 173 }

theorem namedLeaf109_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21613)) namedLeaf109 = true :=
  by decide +kernel

def namedLeaf110 : LeafData := { rows := ![![6, 3, 4, 5, 2, 1], ![6, 2, 3, 4, 5, 0], ![6, 1, 3, 4, 5, 0], ![6, 1, 2, 0, 4, 5], ![6, 1, 2, 0, 3, 5], ![6, 1, 2, 0, 3, 4], ![5, 4, 3, 2, 1, 0]], proof := .tail 191 }

theorem namedLeaf110_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21614)) namedLeaf110 = true :=
  by decide +kernel

def namedLeaf111 : LeafData := { rows := ![![6, 3, 4, 5, 2, 1], ![2, 3, 4, 5, 6, 0], ![1, 3, 4, 5, 6, 0], ![1, 2, 6, 0, 5, 4], ![1, 2, 6, 0, 5, 3], ![1, 2, 6, 0, 4, 3], ![1, 2, 5, 4, 3, 0]], proof := .tail 131 }

theorem namedLeaf111_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21615)) namedLeaf111 = true :=
  by decide +kernel

def namedLeaf112 : LeafData := { rows := ![![6, 3, 4, 5, 2, 1], ![2, 3, 4, 5, 6, 0], ![1, 3, 4, 6, 5, 0], ![1, 2, 6, 0, 5, 4], ![1, 2, 6, 0, 5, 3], ![1, 6, 2, 0, 4, 3], ![1, 5, 2, 4, 3, 0]], proof := .tail 131 }

theorem namedLeaf112_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21616)) namedLeaf112 = true :=
  by decide +kernel

def namedLeaf113 : LeafData := { rows := ![![6, 3, 4, 5, 2, 1], ![2, 3, 4, 5, 6, 0], ![1, 3, 6, 4, 5, 0], ![1, 2, 6, 0, 5, 4], ![1, 6, 2, 0, 5, 3], ![1, 6, 2, 0, 4, 3], ![1, 5, 4, 2, 3, 0]], proof := .tail 64 }

theorem namedLeaf113_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21617)) namedLeaf113 = true :=
  by decide +kernel

def namedLeaf114 : LeafData := { rows := ![![6, 3, 4, 5, 2, 1], ![2, 3, 4, 5, 6, 0], ![1, 6, 3, 4, 5, 0], ![1, 6, 2, 0, 5, 4], ![1, 6, 2, 0, 5, 3], ![1, 6, 2, 0, 4, 3], ![1, 5, 4, 3, 2, 0]], proof := .tail 69 }

theorem namedLeaf114_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21618)) namedLeaf114 = true :=
  by decide +kernel

def namedLeaf115 : LeafData := { rows := ![![6, 3, 4, 5, 2, 1], ![2, 3, 4, 6, 5, 0], ![1, 3, 4, 6, 5, 0], ![1, 2, 6, 0, 5, 4], ![1, 2, 6, 0, 5, 3], ![6, 1, 2, 0, 4, 3], ![5, 1, 2, 4, 3, 0]], proof := .tail 131 }

theorem namedLeaf115_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21619)) namedLeaf115 = true :=
  by decide +kernel

def namedLeaf116 : LeafData := { rows := ![![6, 3, 4, 5, 2, 1], ![2, 3, 4, 6, 5, 0], ![1, 3, 6, 4, 5, 0], ![1, 2, 6, 0, 5, 4], ![1, 6, 2, 0, 5, 3], ![6, 1, 2, 0, 4, 3], ![5, 1, 4, 2, 3, 0]], proof := .tail 64 }

theorem namedLeaf116_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21620)) namedLeaf116 = true :=
  by decide +kernel

def namedLeaf117 : LeafData := { rows := ![![6, 3, 4, 5, 2, 1], ![2, 3, 4, 6, 5, 0], ![1, 6, 3, 4, 5, 0], ![1, 6, 2, 0, 5, 4], ![1, 6, 2, 0, 5, 3], ![6, 1, 2, 0, 4, 3], ![5, 1, 4, 3, 2, 0]], proof := .tail 69 }

theorem namedLeaf117_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21621)) namedLeaf117 = true :=
  by decide +kernel

def namedLeaf118 : LeafData := { rows := ![![6, 3, 4, 5, 2, 1], ![2, 3, 6, 4, 5, 0], ![1, 3, 6, 4, 5, 0], ![1, 2, 6, 0, 5, 4], ![6, 1, 2, 0, 5, 3], ![6, 1, 2, 0, 4, 3], ![5, 4, 1, 2, 3, 0]], proof := .tail 64 }

theorem namedLeaf118_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21622)) namedLeaf118 = true :=
  by decide +kernel

def namedLeaf119 : LeafData := { rows := ![![6, 3, 4, 5, 2, 1], ![2, 3, 6, 4, 5, 0], ![1, 6, 3, 4, 5, 0], ![1, 6, 2, 0, 5, 4], ![6, 1, 2, 0, 5, 3], ![6, 1, 2, 0, 4, 3], ![5, 4, 1, 3, 2, 0]], proof := .tail 6 }

theorem namedLeaf119_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21623)) namedLeaf119 = true :=
  by decide +kernel

def namedLeaf120 : LeafData := { rows := ![![6, 3, 4, 5, 2, 1], ![2, 6, 3, 4, 5, 0], ![1, 6, 3, 4, 5, 0], ![6, 1, 2, 0, 5, 4], ![6, 1, 2, 0, 5, 3], ![6, 1, 2, 0, 4, 3], ![5, 4, 3, 1, 2, 0]], proof := .tail 101 }

theorem namedLeaf120_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21624)) namedLeaf120 = true :=
  by decide +kernel

def namedLeaf121 : LeafData := { rows := ![![6, 3, 4, 5, 2, 1], ![6, 2, 3, 4, 5, 0], ![6, 1, 3, 4, 5, 0], ![6, 1, 2, 0, 5, 4], ![6, 1, 2, 0, 5, 3], ![6, 1, 2, 0, 4, 3], ![5, 4, 3, 2, 1, 0]], proof := .tail 164 }

theorem namedLeaf121_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21625)) namedLeaf121 = true :=
  by decide +kernel

def namedLeaf122 : LeafData := { rows := ![![6, 3, 5, 4, 2, 1], ![2, 3, 4, 5, 6, 0], ![1, 3, 4, 5, 6, 0], ![1, 2, 6, 0, 5, 4], ![1, 2, 5, 6, 0, 3], ![1, 2, 4, 6, 0, 3], ![1, 2, 4, 5, 3, 0]], proof := .tail 127 }

theorem namedLeaf122_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21626)) namedLeaf122 = true :=
  by decide +kernel

def namedLeaf123 : LeafData := { rows := ![![6, 3, 5, 4, 2, 1], ![2, 3, 4, 5, 6, 0], ![1, 3, 4, 5, 6, 0], ![1, 2, 6, 0, 5, 4], ![1, 2, 6, 5, 0, 3], ![1, 2, 6, 4, 0, 3], ![1, 2, 5, 4, 3, 0]], proof := .tail 31 }

theorem namedLeaf123_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21627)) namedLeaf123 = true :=
  by decide +kernel

def namedLeaf124 : LeafData := { rows := ![![6, 3, 5, 4, 2, 1], ![2, 3, 4, 5, 6, 0], ![1, 3, 4, 6, 5, 0], ![1, 2, 6, 0, 5, 4], ![1, 2, 6, 5, 0, 3], ![1, 6, 2, 4, 0, 3], ![1, 5, 2, 4, 3, 0]], proof := .tail 131 }

theorem namedLeaf124_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21628)) namedLeaf124 = true :=
  by decide +kernel

def namedLeaf125 : LeafData := { rows := ![![6, 3, 5, 4, 2, 1], ![2, 3, 4, 5, 6, 0], ![1, 3, 6, 4, 5, 0], ![1, 2, 6, 0, 5, 4], ![1, 6, 2, 5, 0, 3], ![1, 6, 2, 4, 0, 3], ![1, 5, 4, 2, 3, 0]], proof := .tail 84 }

theorem namedLeaf125_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21629)) namedLeaf125 = true :=
  by decide +kernel

def namedLeaf126 : LeafData := { rows := ![![6, 3, 5, 4, 2, 1], ![2, 3, 4, 5, 6, 0], ![1, 3, 5, 4, 6, 0], ![1, 2, 6, 0, 5, 4], ![1, 5, 2, 6, 0, 3], ![1, 4, 2, 6, 0, 3], ![1, 2, 4, 5, 3, 0]], proof := .tail 183 }

theorem namedLeaf126_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21630)) namedLeaf126 = true :=
  by decide +kernel

def namedLeaf127 : LeafData := { rows := ![![6, 3, 5, 4, 2, 1], ![2, 3, 4, 5, 6, 0], ![1, 3, 5, 6, 4, 0], ![1, 2, 6, 0, 5, 4], ![1, 5, 6, 2, 0, 3], ![1, 4, 2, 6, 0, 3], ![1, 4, 2, 5, 3, 0]], proof := .tail 186 }

theorem namedLeaf127_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21631)) namedLeaf127 = true :=
  by decide +kernel

def fallback : LeafData := { rows := fun _ _ => 0, proof := .tail 0 }
def lookup (offset : ℕ) : LeafData :=
  if offset < 128 then (if offset < 64 then (if offset < 32 then (if offset < 16 then (if offset < 8 then (if offset < 4 then (if offset < 2 then (if offset < 1 then (namedLeaf000) else (namedLeaf001)) else (if offset < 3 then (namedLeaf002) else (namedLeaf003))) else (if offset < 6 then (if offset < 5 then (namedLeaf004) else (namedLeaf005)) else (if offset < 7 then (namedLeaf006) else (namedLeaf007)))) else (if offset < 12 then (if offset < 10 then (if offset < 9 then (namedLeaf008) else (namedLeaf009)) else (if offset < 11 then (namedLeaf010) else (namedLeaf011))) else (if offset < 14 then (if offset < 13 then (namedLeaf012) else (namedLeaf013)) else (if offset < 15 then (namedLeaf014) else (namedLeaf015))))) else (if offset < 24 then (if offset < 20 then (if offset < 18 then (if offset < 17 then (namedLeaf016) else (namedLeaf017)) else (if offset < 19 then (namedLeaf018) else (namedLeaf019))) else (if offset < 22 then (if offset < 21 then (namedLeaf020) else (namedLeaf021)) else (if offset < 23 then (namedLeaf022) else (namedLeaf023)))) else (if offset < 28 then (if offset < 26 then (if offset < 25 then (namedLeaf024) else (namedLeaf025)) else (if offset < 27 then (namedLeaf026) else (namedLeaf027))) else (if offset < 30 then (if offset < 29 then (namedLeaf028) else (namedLeaf029)) else (if offset < 31 then (namedLeaf030) else (namedLeaf031)))))) else (if offset < 48 then (if offset < 40 then (if offset < 36 then (if offset < 34 then (if offset < 33 then (namedLeaf032) else (namedLeaf033)) else (if offset < 35 then (namedLeaf034) else (namedLeaf035))) else (if offset < 38 then (if offset < 37 then (namedLeaf036) else (namedLeaf037)) else (if offset < 39 then (namedLeaf038) else (namedLeaf039)))) else (if offset < 44 then (if offset < 42 then (if offset < 41 then (namedLeaf040) else (namedLeaf041)) else (if offset < 43 then (namedLeaf042) else (namedLeaf043))) else (if offset < 46 then (if offset < 45 then (namedLeaf044) else (namedLeaf045)) else (if offset < 47 then (namedLeaf046) else (namedLeaf047))))) else (if offset < 56 then (if offset < 52 then (if offset < 50 then (if offset < 49 then (namedLeaf048) else (namedLeaf049)) else (if offset < 51 then (namedLeaf050) else (namedLeaf051))) else (if offset < 54 then (if offset < 53 then (namedLeaf052) else (namedLeaf053)) else (if offset < 55 then (namedLeaf054) else (namedLeaf055)))) else (if offset < 60 then (if offset < 58 then (if offset < 57 then (namedLeaf056) else (namedLeaf057)) else (if offset < 59 then (namedLeaf058) else (namedLeaf059))) else (if offset < 62 then (if offset < 61 then (namedLeaf060) else (namedLeaf061)) else (if offset < 63 then (namedLeaf062) else (namedLeaf063))))))) else (if offset < 96 then (if offset < 80 then (if offset < 72 then (if offset < 68 then (if offset < 66 then (if offset < 65 then (namedLeaf064) else (namedLeaf065)) else (if offset < 67 then (namedLeaf066) else (namedLeaf067))) else (if offset < 70 then (if offset < 69 then (namedLeaf068) else (namedLeaf069)) else (if offset < 71 then (namedLeaf070) else (namedLeaf071)))) else (if offset < 76 then (if offset < 74 then (if offset < 73 then (namedLeaf072) else (namedLeaf073)) else (if offset < 75 then (namedLeaf074) else (namedLeaf075))) else (if offset < 78 then (if offset < 77 then (namedLeaf076) else (namedLeaf077)) else (if offset < 79 then (namedLeaf078) else (namedLeaf079))))) else (if offset < 88 then (if offset < 84 then (if offset < 82 then (if offset < 81 then (namedLeaf080) else (namedLeaf081)) else (if offset < 83 then (namedLeaf082) else (namedLeaf083))) else (if offset < 86 then (if offset < 85 then (namedLeaf084) else (namedLeaf085)) else (if offset < 87 then (namedLeaf086) else (namedLeaf087)))) else (if offset < 92 then (if offset < 90 then (if offset < 89 then (namedLeaf088) else (namedLeaf089)) else (if offset < 91 then (namedLeaf090) else (namedLeaf091))) else (if offset < 94 then (if offset < 93 then (namedLeaf092) else (namedLeaf093)) else (if offset < 95 then (namedLeaf094) else (namedLeaf095)))))) else (if offset < 112 then (if offset < 104 then (if offset < 100 then (if offset < 98 then (if offset < 97 then (namedLeaf096) else (namedLeaf097)) else (if offset < 99 then (namedLeaf098) else (namedLeaf099))) else (if offset < 102 then (if offset < 101 then (namedLeaf100) else (namedLeaf101)) else (if offset < 103 then (namedLeaf102) else (namedLeaf103)))) else (if offset < 108 then (if offset < 106 then (if offset < 105 then (namedLeaf104) else (namedLeaf105)) else (if offset < 107 then (namedLeaf106) else (namedLeaf107))) else (if offset < 110 then (if offset < 109 then (namedLeaf108) else (namedLeaf109)) else (if offset < 111 then (namedLeaf110) else (namedLeaf111))))) else (if offset < 120 then (if offset < 116 then (if offset < 114 then (if offset < 113 then (namedLeaf112) else (namedLeaf113)) else (if offset < 115 then (namedLeaf114) else (namedLeaf115))) else (if offset < 118 then (if offset < 117 then (namedLeaf116) else (namedLeaf117)) else (if offset < 119 then (namedLeaf118) else (namedLeaf119)))) else (if offset < 124 then (if offset < 122 then (if offset < 121 then (namedLeaf120) else (namedLeaf121)) else (if offset < 123 then (namedLeaf122) else (namedLeaf123))) else (if offset < 126 then (if offset < 125 then (namedLeaf124) else (namedLeaf125)) else (if offset < 127 then (namedLeaf126) else (namedLeaf127)))))))) else fallback

theorem point_checked (j : Fin 128) :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 (21504 + j.val))) (lookup j.val) = true := by
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

theorem correct (id : Fin 24698) (hlow : 21504 ≤ id.val) (hhigh : id.val < 21632) :
    leafCheck library (N4R2WordTree.catalog id) (lookup (id.val - 21504)) = true := by
  let j : Fin 128 := ⟨id.val - 21504, by omega⟩
  have hsum : 21504 + j.val = id.val := by dsimp [j]; omega
  have hindex : Fin.ofNat 24698 (21504 + j.val) = id := by
    apply Fin.ext
    simp only [Fin.ofNat, hsum, Nat.mod_eq_of_lt id.isLt]
  have hh := point_checked j
  rw [hindex] at hh
  exact hh

#print axioms point_checked
#print axioms correct
end Jsp404.N4R2OuterLeftData.LeafShard168
