import Jsp000404.N4R2OuterLeftReplay
import Jsp000404.N4R2WordCatalog

set_option autoImplicit false
set_option pp.fullNames true
set_option maxRecDepth 8192
set_option maxHeartbeats 0
set_option Elab.async false

namespace Jsp404.N4R2OuterLeftData.LeafShard015
open N4R2OuterLeftReplay

-- Cycle fingerprint 005a5663f9afdd769bbaf3681c0be281a6f7e18811ce593dbbc91bcf97f862b2.
def localCycle00000 : Cycle where
  length := 7
  data := {
    node := ![.distance 2 3, .distance 3 4, .distance 4 6, .distance 0 4, .distance 0 3, .distance 3 5, .theta 3, .distance 2 3]
    constant := ![-1, -1, -1, 0, -1, -1, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.triangle 25 0, .triangle 32 0, .triangle 13 0, .gapLower 0 4, .triangle 10 0, .corridorLower 3 5, .corridorUpper 2 3]

-- Cycle fingerprint 026353ddd71152ee152351de28463ce3ce66d6e24dcb5664be94057a8194bb6a.
def localCycle00001 : Cycle where
  length := 11
  data := {
    node := ![.theta 0, .zero, .theta 4, .distance 3 4, .distance 2 4, .distance 1 4, .distance 1 6, .distance 1 3, .distance 1 5, .distance 1 2, .distance 0 1, .theta 0]
    constant := ![0, 0, 3, 0, 0, 0, -2, 0, -2, -1, -1]
    coefficient := ![0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, true, false, true, false, false, false] }
  origin := ![.thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 16 2, .triangle 23 2, .gapLower 1 4, .triangle 20 2, .gapLower 1 2, .triangle 0 0, .corridorLower 0 1]

-- Cycle fingerprint 05ccb1bd1b7c7834bfc9a7b6f31698c4fa58b173b252ada9dbb1540bf045f72f.
def localCycle00002 : Cycle where
  length := 10
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 3, .distance 3 4, .distance 4 6, .distance 0 4, .distance 0 3, .distance 3 5, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, 0, -1, -1, -1, 0, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, true, false, true, false, true] }
  origin := ![.corridorUpper 2 3, .triangle 15 2, .triangle 19 0, .triangle 32 0, .triangle 13 0, .triangle 9 1, .triangle 10 0, .triangle 31 1, .corridorLower 4 5, .thetaNext 3]

-- Cycle fingerprint 06fb0575831741b26accd09933c89088e2946c78d061400bc47698e632ddfc2f.
def localCycle00003 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 3, .distance 3 4, .distance 0 3, .distance 0 5, .distance 5 6, .distance 3 5, .theta 3]
    constant := ![3, 0, -1, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 2, .triangle 19 0, .triangle 9 0, .triangle 10 2, .triangle 14 0, .triangle 33 0, .corridorLower 3 5]

-- Cycle fingerprint 086195412effa99637f00cc2573e1da5b78dae1a2aff2a7deb6783d951fdaf58.
def localCycle00004 : Cycle where
  length := 8
  data := {
    node := ![.distance 3 6, .distance 3 5, .theta 3, .theta 2, .theta 1, .distance 1 4, .distance 0 4, .distance 0 3, .distance 3 6]
    constant := ![0, -1, 0, 0, 1, 0, 0, -1]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![true, false, true, true, false, true, true, false] }
  origin := ![.triangle 33 1, .corridorLower 3 5, .thetaNext 2, .thetaNext 1, .gapLower 1 6, .triangle 2 2, .triangle 9 1, .triangle 11 0]

-- Cycle fingerprint 08aa5ff7cb9cbafdcfc8c446e6d4f7721d06293e38300f7de1015bdd5b7de669.
def localCycle00005 : Cycle where
  length := 9
  data := {
    node := ![.distance 3 4, .distance 1 3, .distance 1 6, .distance 1 5, .distance 1 2, .distance 0 1, .theta 0, .zero, .theta 4, .distance 3 4]
    constant := ![-1, -2, 0, -2, -1, -1, 0, 0, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1, 1]
    strict := ![false, false, true, false, false, false, false, false, false] }
  origin := ![.triangle 19 0, .gapLower 1 4, .triangle 24 1, .gapLower 1 2, .triangle 0 0, .corridorLower 0 1, .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4]

-- Cycle fingerprint 0a84a20adc524672dd0cc83312b4f2519ef8865090c793fbdcc3c6439c5c807d.
def localCycle00006 : Cycle where
  length := 9
  data := {
    node := ![.distance 2 6, .distance 1 6, .distance 1 5, .distance 0 5, .distance 3 5, .distance 4 5, .theta 4, .distance 3 4, .distance 2 3, .distance 2 6]
    constant := ![0, -3, 0, 0, 0, -1, 3, -1, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 0, 0]
    strict := ![true, false, true, true, true, false, false, false, true] }
  origin := ![.triangle 18 2, .gapLower 1 3, .triangle 3 2, .triangle 10 1, .triangle 31 1, .corridorLower 4 5, .corridorUpper 3 4, .triangle 25 0, .triangle 27 2]

-- Cycle fingerprint 13535f99b105865a8ff3e765a76cb48427542d979ee7df6d6b8854981fba1515.
def localCycle00007 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 2 3, .distance 2 4, .distance 4 6, .distance 3 4, .distance 0 3, .distance 3 5, .theta 3]
    constant := ![3, 0, -1, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 25 2, .triangle 29 0, .triangle 32 0, .triangle 9 0, .triangle 10 0, .corridorLower 3 5]

-- Cycle fingerprint 1394b105fdbbc1cdcb82d2c56a3873339e28e8baff651a3cff3c734da795cf19.
def localCycle00008 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 4, .distance 0 3, .distance 0 5, .distance 5 6, .distance 3 5, .theta 3]
    constant := ![3, -1, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 25 0, .triangle 9 0, .triangle 10 2, .triangle 14 0, .triangle 33 0, .corridorLower 3 5]

-- Cycle fingerprint 1589f49d9c5af7c08ab3961bee3480a833560ad1fa0bfdf7f6746a6f1e44a822.
def localCycle00009 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 3, .distance 3 6, .distance 0 3, .distance 3 5, .distance 4 5, .theta 4]
    constant := ![3, -1, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 0, .triangle 27 0, .triangle 11 0, .triangle 10 0, .triangle 31 1, .corridorLower 4 5]

-- Cycle fingerprint 1b5ae97bcb370d30f0175e0cb48a246061bbaa1ec6706340182d3f5df8bf0002.
def localCycle00010 : Cycle where
  length := 8
  data := {
    node := ![.theta 1, .zero, .theta 4, .distance 3 4, .distance 1 3, .distance 1 5, .distance 1 2, .distance 0 1, .theta 1]
    constant := ![0, 0, 3, -1, -2, 0, -1, -2]
    coefficient := ![0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, false] }
  origin := ![.thetaLower 1, .thetaUpper 4, .corridorUpper 3 4, .triangle 19 0, .gapLower 1 3, .triangle 17 1, .triangle 0 0, .gapLower 1 0]

-- Cycle fingerprint 1da52dc78e4aeb0f838e007f2219b2cfd8b16368598cdff17fb86a99383aacb6.
def localCycle00011 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 3, .distance 1 4, .distance 4 6, .distance 3 4, .distance 0 3, .distance 3 5, .theta 3]
    constant := ![3, 0, 0, -1, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 2, .triangle 19 2, .triangle 23 0, .triangle 32 0, .triangle 9 0, .triangle 10 0, .corridorLower 3 5]

-- Cycle fingerprint 1e2b8b194bf447d4fb64c69cec2467584381c06ee1a47aea6b6fccbc9ce51db9.
def localCycle00012 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 6, .distance 1 5, .distance 0 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 2 4, .distance 1 4, .distance 1 3, .distance 1 6]
    constant := ![-2, -1, -1, 0, 0, 3, 0, 0, -2, 0]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, true, false, true] }
  origin := ![.gapLower 1 3, .triangle 3 0, .corridorLower 0 1, .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 16 2, .gapLower 1 5, .triangle 21 2]

-- Cycle fingerprint 1ef7ec56d46fd0ac53344b7d55e8470adaa931561ac1f38bd2f949e10a799b23.
def localCycle00013 : Cycle where
  length := 6
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 3, .distance 2 5, .distance 5 6, .distance 4 5, .theta 4]
    constant := ![3, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 0, .triangle 26 2, .triangle 30 0, .triangle 34 0, .corridorLower 4 5]

-- Cycle fingerprint 1fa25d3c9b392cce1f75fe682bdac77dadc35743fa5247be8ee6bcdc40a42d1c.
def localCycle00014 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 3, .distance 2 5, .distance 5 6, .distance 3 6, .distance 0 3, .distance 3 5, .distance 4 5, .theta 4]
    constant := ![3, -1, 0, -1, 0, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 0, .triangle 26 2, .triangle 30 0, .triangle 33 2, .triangle 11 0, .triangle 10 0, .triangle 31 1, .corridorLower 4 5]

-- Cycle fingerprint 214d38929ca70dfe4f270a3dc868ebab55c273491bf178184cf286ad791a9f04.
def localCycle00015 : Cycle where
  length := 11
  data := {
    node := ![.theta 0, .zero, .theta 4, .distance 3 4, .distance 2 4, .distance 1 4, .distance 1 6, .distance 1 3, .distance 1 5, .distance 1 2, .distance 0 1, .theta 0]
    constant := ![0, 0, 3, 0, 0, 0, -2, -2, 0, -1, -1]
    coefficient := ![0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, true, false, false, true, false, false] }
  origin := ![.thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 16 2, .triangle 23 2, .gapLower 1 4, .gapLower 1 3, .triangle 17 1, .triangle 0 0, .corridorLower 0 1]

-- Cycle fingerprint 28fea3a39d9a11240b7bd8c40ce2d155f891e87e795567db5dafb2fe4c203453.
def localCycle00016 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 2 3, .distance 2 6, .distance 2 5, .distance 1 5, .distance 1 2, .distance 0 1]
    constant := ![-1, 0, 0, 3, -1, 0, 0, 0, -2, -2]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, true, false, false] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 25 0, .triangle 27 2, .triangle 30 1, .triangle 17 2, .gapLower 1 2, .gapLower 1 1]

-- Cycle fingerprint 2ad91aa6c36705a091ad063fc9df29faddcb70539726ea9205b22d210964e1da.
def localCycle00017 : Cycle where
  length := 9
  data := {
    node := ![.distance 2 6, .distance 1 6, .distance 1 3, .distance 0 3, .distance 3 5, .distance 4 5, .theta 4, .distance 3 4, .distance 2 4, .distance 2 6]
    constant := ![0, -3, 0, -1, 0, -1, 3, 0, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 0, 0]
    strict := ![true, false, true, false, true, false, false, true, true] }
  origin := ![.triangle 18 2, .gapLower 1 4, .triangle 1 2, .triangle 10 0, .triangle 31 1, .corridorLower 4 5, .corridorUpper 3 4, .triangle 25 2, .triangle 29 2]

-- Cycle fingerprint 2af71584599cd2c1e4b83ae593a98fde5023d76521d423b9691ffa541464f7f1.
def localCycle00018 : Cycle where
  length := 6
  data := {
    node := ![.theta 4, .distance 3 4, .distance 1 3, .distance 1 5, .distance 5 6, .distance 4 5, .theta 4]
    constant := ![3, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 19 0, .triangle 20 2, .triangle 24 0, .triangle 34 0, .corridorLower 4 5]

-- Cycle fingerprint 2af823b9eee0f9ded70739b2378307df7b29d24739b37e54f6ef2fd42932830b.
def localCycle00019 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 2, .distance 0 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 2 4, .distance 2 6, .distance 1 6, .distance 1 3, .distance 1 2]
    constant := ![-2, -1, 0, 0, 3, 0, 0, 0, -2, 0]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, true, false, true] }
  origin := ![.gapLower 1 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 29 2, .triangle 18 2, .gapLower 1 4, .triangle 15 1]

-- Cycle fingerprint 2e0c629a13115efc00e42a86bbaeff1f617de8ceba80c1fdc9ed14e36bb0d42f.
def localCycle00020 : Cycle where
  length := 10
  data := {
    node := ![.theta 3, .distance 2 3, .distance 2 4, .distance 2 5, .distance 5 6, .distance 3 6, .distance 0 3, .distance 3 5, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, 0, 0, -1, 0, -1, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, false, true, false, true] }
  origin := ![.corridorUpper 2 3, .triangle 25 2, .triangle 28 2, .triangle 30 0, .triangle 33 2, .triangle 11 0, .triangle 10 0, .triangle 31 1, .corridorLower 4 5, .thetaNext 3]

-- Cycle fingerprint 3145bac4a4da9f06c39c281872cf2ec95aa8896bc9cf97b68579d0f05e39cd62.
def localCycle00021 : Cycle where
  length := 6
  data := {
    node := ![.theta 4, .distance 3 4, .distance 0 3, .distance 0 5, .distance 5 6, .distance 4 5, .theta 4]
    constant := ![3, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 9 0, .triangle 10 2, .triangle 14 0, .triangle 34 0, .corridorLower 4 5]

-- Cycle fingerprint 31e58d2e7987c4d6bc8a2b928af8df5b3773821a2477be107221321ef9592b2a.
def localCycle00022 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 3, .distance 1 6, .distance 1 5, .distance 1 2, .distance 0 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 1 3]
    constant := ![0, -2, -2, -1, -1, 0, 0, 3, -1]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![true, false, false, false, false, false, false, false, false] }
  origin := ![.triangle 21 2, .gapLower 1 3, .gapLower 1 2, .triangle 0 0, .corridorLower 0 1, .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 19 0]

-- Cycle fingerprint 3702b46ef76977178992ac30d12e577182a161d9d20227d8af804bced8ddf56c.
def localCycle00023 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 2, .distance 0 1, .theta 1, .zero, .theta 4, .distance 3 4, .distance 2 4, .distance 1 4, .distance 1 6, .distance 1 3, .distance 1 2]
    constant := ![-1, -2, 0, 0, 3, 0, 0, 0, -2, 0]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, true, false, true] }
  origin := ![.triangle 0 0, .gapLower 1 0, .thetaLower 1, .thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 16 2, .triangle 23 2, .gapLower 1 4, .triangle 15 1]

-- Cycle fingerprint 3f0de987ee7ec2a7df53413973586ca15e21179d12b65b74f85c16cb454f600f.
def localCycle00024 : Cycle where
  length := 5
  data := {
    node := ![.distance 2 3, .distance 2 5, .distance 5 6, .distance 4 6, .distance 3 4, .distance 2 3]
    constant := ![0, 2, 0, -1, -1]
    coefficient := ![0, 0, 0, 0, 0]
    strict := ![true, true, true, false, false] }
  origin := ![.triangle 26 2, .gapUpper 5 5, .triangle 34 2, .triangle 32 0, .triangle 25 0]

-- Cycle fingerprint 4126ae261dc5640a9aa9d984747d3e21ca3fe3e8e0e3f0f2f0a29f0c5bcea9ba.
def localCycle00025 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .theta 1, .distance 1 4, .distance 0 4, .distance 0 3, .distance 3 5, .distance 4 5, .theta 4, .theta 3, .theta 2]
    constant := ![0, 1, 0, 0, -1, 0, -1, 0, 0]
    coefficient := ![0, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![true, false, true, true, false, true, false, true, true] }
  origin := ![.thetaNext 1, .gapLower 1 6, .triangle 2 2, .triangle 9 1, .triangle 10 0, .triangle 31 1, .corridorLower 4 5, .thetaNext 3, .thetaNext 2]

-- Cycle fingerprint 422e94d799399ff2948aafa7b8dd9752ea8abdb81339e47059aa5c3528a5f83a.
def localCycle00026 : Cycle where
  length := 6
  data := {
    node := ![.distance 1 2, .distance 1 5, .distance 5 6, .distance 4 6, .distance 3 4, .distance 2 3, .distance 1 2]
    constant := ![0, 2, 0, -1, -1, -1]
    coefficient := ![0, 0, 0, 0, 0, 0]
    strict := ![true, true, true, false, false, false] }
  origin := ![.triangle 17 2, .gapUpper 5 5, .triangle 34 2, .triangle 32 0, .triangle 25 0, .triangle 15 0]

-- Cycle fingerprint 43294bf66853e9c401059e782084861dbe16a9092fbc08b0c521707dcbfa567b.
def localCycle00027 : Cycle where
  length := 9
  data := {
    node := ![.distance 3 6, .distance 4 6, .distance 0 4, .distance 0 3, .distance 3 5, .distance 4 5, .theta 4, .distance 3 4, .distance 2 3, .distance 3 6]
    constant := ![0, -1, 0, -1, 0, -1, 3, -1, -1]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 0, 0]
    strict := ![true, false, false, false, true, false, false, false, false] }
  origin := ![.triangle 32 1, .triangle 13 0, .gapLower 0 4, .triangle 10 0, .triangle 31 1, .corridorLower 4 5, .corridorUpper 3 4, .triangle 25 0, .triangle 27 0]

-- Cycle fingerprint 4336545a4bb5ebd11157b05ab8c584afa1a8784c802f48ff17e8e9c29eb30b6e.
def localCycle00028 : Cycle where
  length := 3
  data := {
    node := ![.distance 0 1, .theta 1, .distance 1 4, .distance 0 1]
    constant := ![-2, 2, -1]
    coefficient := ![0, 1, 0]
    strict := ![false, false, false] }
  origin := ![.gapLower 1 0, .gapLower 1 6, .triangle 2 0]

-- Cycle fingerprint 450504e35f1d4a475b5d68f21e450b6fd3863a8df31e49b01e65ca45d1bdaf62.
def localCycle00029 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 4 6, .distance 2 6, .distance 1 2, .distance 2 4, .distance 2 3, .distance 3 5, .distance 4 5, .theta 4]
    constant := ![3, -1, 0, -1, -1, 0, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 32 0, .triangle 29 2, .triangle 18 0, .triangle 16 0, .triangle 25 1, .triangle 26 0, .triangle 31 1, .corridorLower 4 5]

-- Cycle fingerprint 48492397819d227504c8ea9d26f1032e94ccc74bc43d5a16994f1f8bc5f07689.
def localCycle00030 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 5, .distance 1 2, .distance 0 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 2 4, .distance 1 4, .distance 1 6, .distance 1 5]
    constant := ![-2, -1, -1, 0, 0, 3, 0, 0, -2, 0]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, true, false, true] }
  origin := ![.gapLower 1 2, .triangle 0 0, .corridorLower 0 1, .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 16 2, .gapLower 1 5, .triangle 24 1]

-- Cycle fingerprint 49d036f4b88d99667e525a6401a0bd8fb96a44bba6fca35279046882853b366e.
def localCycle00031 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 2 4, .distance 1 2, .distance 2 3, .distance 0 3, .distance 3 5, .distance 4 5, .theta 4, .zero]
    constant := ![0, 3, 0, -1, -1, -1, 0, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, true, false, true, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 29 0, .triangle 16 0, .triangle 15 0, .triangle 5 2, .triangle 10 0, .triangle 31 1, .corridorLower 4 5, .thetaLower 4]

-- Cycle fingerprint 4aab283d541731d74483d407f2af0cdda6929ecf60dcdc8d38dc1214a203c0f3.
def localCycle00032 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 1, .distance 1 4, .distance 1 3, .distance 0 3, .distance 3 6, .distance 4 6, .distance 4 5, .theta 4, .zero]
    constant := ![0, 2, -2, 0, -1, 0, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true, true, false, false] }
  origin := ![.thetaUpper 1, .gapLower 1 6, .gapLower 1 5, .triangle 1 2, .triangle 11 0, .triangle 32 1, .triangle 34 1, .corridorLower 4 5, .thetaLower 4]

-- Cycle fingerprint 4bbfeede3a1cd98bcec169439cb8f5e06e16360cf5cf7b40662061e3dacb53fa.
def localCycle00033 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 2, .distance 2 6, .distance 5 6, .distance 3 5, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, -1, -1, 0, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true, false, true] }
  origin := ![.corridorUpper 2 3, .triangle 15 0, .triangle 18 0, .triangle 30 1, .triangle 33 0, .triangle 31 1, .corridorLower 4 5, .thetaNext 3]

-- Cycle fingerprint 4be4da47fcf2ab44bb60d424c230b8013d707fd6a7b51d11006c95aab5e37b52.
def localCycle00034 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 4 6, .distance 1 4, .distance 0 4, .distance 0 3, .distance 3 5, .distance 4 5, .theta 4]
    constant := ![3, 0, -1, -1, 0, 0, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, true, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 29 0, .triangle 23 0, .triangle 2 2, .triangle 9 1, .triangle 10 0, .triangle 31 1, .corridorLower 4 5]

-- Cycle fingerprint 4cabf40c0faaf82d3d3e530592c08f884df79e8c170904b2f4cc246e87c2953a.
def localCycle00035 : Cycle where
  length := 11
  data := {
    node := ![.distance 0 1, .theta 1, .zero, .theta 4, .distance 3 4, .distance 2 4, .distance 1 4, .distance 1 3, .distance 1 6, .distance 1 5, .distance 1 2, .distance 0 1]
    constant := ![-2, 0, 0, 3, 0, 0, -2, 0, 0, 0, -1]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, false, true, true, false, false] }
  origin := ![.gapLower 1 0, .thetaLower 1, .thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 16 2, .gapLower 1 5, .triangle 21 2, .triangle 24 1, .gapLower 1 2, .triangle 0 0]

-- Cycle fingerprint 4d9747cce40cccce6dd1cdb6847951c6a1daef8f5c7ca1e55c7157a3b6d5b786.
def localCycle00036 : Cycle where
  length := 9
  data := {
    node := ![.distance 2 5, .distance 1 5, .distance 1 2, .distance 0 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 2 3, .distance 2 5]
    constant := ![0, -2, -2, -1, 0, 0, 3, -1, 0]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![true, false, false, false, false, false, false, false, true] }
  origin := ![.triangle 17 2, .gapLower 1 2, .gapLower 1 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 25 0, .triangle 26 2]

-- Cycle fingerprint 50727fa54f2557659886a5c31c88f5ca8430abc9f8205b69cd918182a551f8c0.
def localCycle00037 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 1 4, .distance 4 6, .distance 0 4, .distance 0 3, .distance 3 5, .distance 4 5, .theta 4]
    constant := ![3, 0, 0, -1, -1, 0, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, true, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 16 2, .triangle 23 0, .triangle 13 0, .triangle 9 1, .triangle 10 0, .triangle 31 1, .corridorLower 4 5]

-- Cycle fingerprint 52328c7075ee57691571e47a4d63b673c031a706f909aa559459eb3255ee33f9.
def localCycle00038 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 2 3, .distance 3 4, .distance 0 3, .distance 3 5, .distance 4 5, .theta 4, .zero]
    constant := ![0, 3, 0, 0, -1, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, false, true, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 27 0, .triangle 25 0, .triangle 9 0, .triangle 10 0, .triangle 31 1, .corridorLower 4 5, .thetaLower 4]

-- Cycle fingerprint 5477fcd0ede81eaecca337a0d8b12ba355f6104c3f549c27eef0e1c81536c626.
def localCycle00039 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 2, .distance 0 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 2 3, .distance 2 6, .distance 1 6, .distance 1 5, .distance 1 2]
    constant := ![-2, -1, 0, 0, 3, -1, 0, 0, -2, 0]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, true, false, true] }
  origin := ![.gapLower 1 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 25 0, .triangle 27 2, .triangle 18 2, .gapLower 1 3, .triangle 17 1]

-- Cycle fingerprint 5620c003cd5ca6873a37fba58f8b7e96a43934da6e2df479f0bcc3631a52d29f.
def localCycle00040 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 3 4, .distance 0 3, .distance 3 5, .distance 4 5, .distance 5 6, .theta 5, .theta 4]
    constant := ![3, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, true] }
  origin := ![.corridorUpper 3 4, .triangle 9 0, .triangle 10 0, .triangle 31 1, .triangle 34 0, .corridorLower 5 6, .thetaNext 4]

-- Cycle fingerprint 58ed01546dd632d8476d9a550f27ed731f5288505ed392ecc900300374ea9c17.
def localCycle00041 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 4 6, .distance 2 4, .distance 2 3, .distance 1 2, .distance 2 5, .distance 3 5, .distance 4 5, .theta 4]
    constant := ![3, -1, -1, 0, -1, -1, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 32 0, .triangle 29 0, .gapLower 2 4, .triangle 15 0, .triangle 17 0, .triangle 26 1, .triangle 31 1, .corridorLower 4 5]

-- Cycle fingerprint 5d75af5e11f63fd0318f65f540828f1cfc9e8474129fe8bb9dd5be12632a029e.
def localCycle00042 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 2, .distance 1 4, .distance 4 6, .distance 3 4, .distance 0 3, .distance 3 5, .theta 3]
    constant := ![3, -1, 0, -1, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 0, .triangle 16 2, .triangle 23 0, .triangle 32 0, .triangle 9 0, .triangle 10 0, .corridorLower 3 5]

-- Cycle fingerprint 5f8456e23c8c0a4d7f7107e1ff4b30b5afa4822913c3ded2a3094ca20e4c68a4.
def localCycle00043 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 3, .distance 3 6, .distance 3 4, .distance 0 3, .distance 3 5, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, 0, -1, 0, -1, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, true, false, true] }
  origin := ![.corridorUpper 2 3, .triangle 15 2, .triangle 21 0, .triangle 32 1, .triangle 9 0, .triangle 10 0, .triangle 31 1, .corridorLower 4 5, .thetaNext 3]

-- Cycle fingerprint 5faa39b5d7af068877165173a7efd964fc3aef3831d0da5c00c4ab5fadb74635.
def localCycle00044 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 2 3, .distance 1 2, .distance 2 5, .distance 0 2, .theta 0, .zero]
    constant := ![0, 3, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 25 0, .triangle 15 0, .triangle 17 0, .triangle 7 0, .corridorLower 0 2, .thetaLower 0]

-- Cycle fingerprint 6237fdb514faf0d2b84b70aa1dfddc15195febff37f43ce7c6fc4ea51f1a38a5.
def localCycle00045 : Cycle where
  length := 13
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 2 3, .distance 1 2, .distance 2 4, .distance 3 4, .distance 0 3, .distance 3 5, .distance 4 5, .theta 4, .zero]
    constant := ![0, 3, 0, 0, -1, -1, -1, 0, -1, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, true, false, false, true, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 27 0, .triangle 15 0, .triangle 16 0, .triangle 25 1, .triangle 9 0, .triangle 10 0, .triangle 31 1, .corridorLower 4 5, .thetaLower 4]

-- Cycle fingerprint 66d4d8cc0cfaeaf26e02416c4de885f5df9ea6e4b595a8341b9d41bcdc51ac8e.
def localCycle00046 : Cycle where
  length := 10
  data := {
    node := ![.theta 3, .distance 2 3, .distance 2 4, .distance 2 5, .distance 5 6, .distance 3 6, .distance 1 3, .distance 3 4, .distance 0 3, .distance 3 5, .theta 3]
    constant := ![3, 0, 0, -1, 0, -1, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 25 2, .triangle 28 2, .triangle 30 0, .triangle 33 2, .triangle 21 0, .triangle 19 0, .triangle 9 0, .triangle 10 0, .corridorLower 3 5]

-- Cycle fingerprint 680c2751dd2fe91a73b09949334e398a1671f14aa2fb33d069de1e363d106990.
def localCycle00047 : Cycle where
  length := 3
  data := {
    node := ![.distance 2 5, .distance 1 5, .distance 1 2, .distance 2 5]
    constant := ![0, -3, 2]
    coefficient := ![0, 0, 0]
    strict := ![false, false, true] }
  origin := ![.gapLower 5 4, .gapLower 1 2, .gapUpper 2 2]

-- Cycle fingerprint 685fcdd70faa84e83c1f1e187b55ec9f06bc61a27ae598f7d16f197f7cf71f15.
def localCycle00048 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 1 3, .distance 1 5, .distance 1 2, .distance 0 1, .theta 1, .zero]
    constant := ![0, 3, -1, 0, -2, -1, -2, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 19 0, .triangle 20 2, .gapLower 1 2, .triangle 0 0, .gapLower 1 0, .thetaLower 1]

-- Cycle fingerprint 6a1643d7026f8f99f8264df3a63f85f8ce8d772c6b93759c7bd58f69ecf8792b.
def localCycle00049 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 2 4, .distance 4 6, .distance 3 6, .distance 1 3, .distance 3 4, .distance 0 3, .distance 3 5, .theta 3]
    constant := ![3, 0, -1, 0, -1, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 25 2, .triangle 29 0, .triangle 32 2, .triangle 21 0, .triangle 19 0, .triangle 9 0, .triangle 10 0, .corridorLower 3 5]

-- Cycle fingerprint 6a663c36c5ded82e3deb491c8fffe572260607db100fa2ebc613a05c4b77d963.
def localCycle00050 : Cycle where
  length := 5
  data := {
    node := ![.distance 1 3, .distance 1 5, .distance 5 6, .distance 4 6, .distance 3 4, .distance 1 3]
    constant := ![0, 2, 0, -1, -1]
    coefficient := ![0, 0, 0, 0, 0]
    strict := ![true, true, true, false, false] }
  origin := ![.triangle 20 2, .gapUpper 5 5, .triangle 34 2, .triangle 32 0, .triangle 19 0]

-- Cycle fingerprint 6d64c9942f3455139f3cea6cd8a0bffd3f45d01e0757ddc4d313b9a218380c81.
def localCycle00051 : Cycle where
  length := 8
  data := {
    node := ![.distance 1 2, .distance 0 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 2 3, .distance 2 5, .distance 1 2]
    constant := ![-2, -1, 0, 0, 3, -1, 0, -1]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, false] }
  origin := ![.gapLower 1 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 25 0, .triangle 26 2, .triangle 17 0]

-- Cycle fingerprint 709103f85dabf1f26c1caa90282f00cf21f1bf7e7aa87be183992829d334bab4.
def localCycle00052 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 1 3, .distance 3 4, .distance 2 3, .distance 3 5, .distance 0 3, .distance 3 6, .theta 3]
    constant := ![3, -1, -1, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.corridorUpper 1 3, .triangle 19 0, .triangle 25 0, .triangle 26 0, .triangle 10 0, .triangle 11 0, .corridorLower 3 6]

-- Cycle fingerprint 73034bb7a7daa7ae2331323b3439b1deae1021a61323c2a895759c889c0bc8ac.
def localCycle00053 : Cycle where
  length := 11
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 3, .distance 2 5, .distance 1 2, .distance 2 6, .distance 5 6, .distance 3 6, .distance 0 3, .distance 3 5, .distance 4 5, .theta 4]
    constant := ![3, -1, 0, -1, -1, 0, 0, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, true, false, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 0, .triangle 26 2, .triangle 17 0, .triangle 18 0, .triangle 30 1, .triangle 33 2, .triangle 11 0, .triangle 10 0, .triangle 31 1, .corridorLower 4 5]

-- Cycle fingerprint 7514fcbd00898582fc52ab37e55de3779fd57051b4f0559fc76bea8f82468451.
def localCycle00054 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 3, .distance 1 5, .distance 5 6, .distance 4 6, .distance 3 6, .distance 2 3, .distance 3 4, .distance 1 3]
    constant := ![0, 2, 0, 0, -1, -1, -1]
    coefficient := ![0, 0, 0, 0, 0, 0, 0]
    strict := ![true, true, true, true, false, false, false] }
  origin := ![.triangle 20 2, .gapUpper 5 5, .triangle 34 2, .triangle 32 2, .triangle 27 0, .triangle 25 0, .triangle 19 0]

-- Cycle fingerprint 763e3978f735da511fbd62f7246ab3e382aa6895795fab6b1acdfc0fc9254bf1.
def localCycle00055 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 3 4, .distance 1 3, .distance 1 5, .distance 5 6, .distance 3 5, .distance 4 5, .theta 4]
    constant := ![3, -1, 0, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 19 0, .triangle 20 2, .triangle 24 0, .triangle 33 0, .triangle 31 1, .corridorLower 4 5]

-- Cycle fingerprint 76bbb4e2775917cd49c3f77548c28097235cfebf42dc1e2033b129aba49ddcb0.
def localCycle00056 : Cycle where
  length := 9
  data := {
    node := ![.distance 2 4, .distance 1 4, .distance 1 3, .distance 1 6, .distance 0 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 2 4]
    constant := ![0, -2, -2, -1, -1, 0, 0, 3, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![true, false, false, false, false, false, false, false, true] }
  origin := ![.triangle 16 2, .gapLower 1 5, .gapLower 1 4, .triangle 4 0, .corridorLower 0 1, .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 25 2]

-- Cycle fingerprint 783c7f2534cf08aa2f71c6dd246efc833ca2e1953cca9e80be11234dccc17338.
def localCycle00057 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 4, .distance 0 3, .distance 3 5, .distance 5 6, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, -1, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, true] }
  origin := ![.corridorUpper 2 3, .triangle 25 0, .triangle 9 0, .triangle 10 0, .triangle 33 0, .triangle 34 0, .corridorLower 4 5, .thetaNext 3]

-- Cycle fingerprint 78f93dee320114dd2e20e494032a1072c68f84526cb9b8f1784dbece0d6dd55e.
def localCycle00058 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 4, .distance 3 6, .distance 0 3, .distance 3 5, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, -1, 0, -1, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, false, true] }
  origin := ![.corridorUpper 2 3, .triangle 25 0, .triangle 32 2, .triangle 11 0, .triangle 10 0, .triangle 31 1, .corridorLower 4 5, .thetaNext 3]

-- Cycle fingerprint 7971330c902863125818df70a680cf36ecfd88cba861655c142a3b71ca263930.
def localCycle00059 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 4, .distance 1 3, .distance 1 5, .distance 5 6, .distance 3 6, .distance 0 3, .distance 3 5, .theta 3]
    constant := ![3, -1, -1, 0, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 25 0, .triangle 19 0, .triangle 20 2, .triangle 24 0, .triangle 33 2, .triangle 11 0, .triangle 10 0, .corridorLower 3 5]

-- Cycle fingerprint 7a2036e2a1267a39b6dedee4c33297f7efc1fb317413bf260488124bc2149435.
def localCycle00060 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 2 4, .distance 1 2, .distance 2 5, .distance 0 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, -1, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, true, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 29 0, .triangle 16 0, .triangle 17 0, .triangle 7 0, .triangle 0 1, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint 7a2cc5d26bc268e819cf7c1cc6277dee23f336591cd7ad1deaf012513745169b.
def localCycle00061 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 2, .distance 2 3, .distance 0 3, .distance 3 5, .distance 4 5, .theta 4, .distance 3 4, .distance 2 4, .distance 4 6, .distance 1 4, .distance 1 2]
    constant := ![-1, 0, -1, 0, -1, 3, 0, -1, -1, 0]
    coefficient := ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, true, false, false, false] }
  origin := ![.triangle 15 0, .triangle 5 2, .triangle 10 0, .triangle 31 1, .corridorLower 4 5, .corridorUpper 3 4, .triangle 25 2, .triangle 29 0, .triangle 23 0, .gapLower 1 4]

-- Cycle fingerprint 7a4aee3c1865bb4249b7973deeb9ba54af9e3d8f552fa400f6a3d846b91c32d5.
def localCycle00062 : Cycle where
  length := 9
  data := {
    node := ![.distance 2 5, .distance 1 2, .distance 0 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 2 3, .distance 2 6, .distance 2 5]
    constant := ![-1, -3, -1, 0, 0, 3, -1, 0, 0]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, true, true] }
  origin := ![.triangle 17 0, .gapLower 1 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 25 0, .triangle 27 2, .triangle 30 1]

-- Cycle fingerprint 7ab1d976d3cf9431f49dcc3275c569153a7183da13bd02e2bfb206e388d334b9.
def localCycle00063 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 2, .distance 2 4, .distance 3 4, .distance 4 6, .distance 0 4, .distance 0 3, .distance 3 5, .theta 3]
    constant := ![3, -1, -1, 0, -1, -1, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, true, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 0, .triangle 16 0, .triangle 25 1, .triangle 32 0, .triangle 13 0, .triangle 9 1, .triangle 10 0, .corridorLower 3 5]

-- Cycle fingerprint 7c484e4c9be6369cea851b3805679b26c8b708295639f00d9964d31fad7e91bb.
def localCycle00064 : Cycle where
  length := 11
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 2 4, .distance 1 4, .distance 1 3, .distance 1 6, .distance 1 5, .distance 1 2, .distance 0 1]
    constant := ![-1, 0, 0, 3, 0, 0, -2, 0, 0, 0, -2]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, false, true, true, false, false] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 16 2, .gapLower 1 5, .triangle 21 2, .triangle 24 1, .gapLower 1 2, .gapLower 1 1]

-- Cycle fingerprint 8030a3d1ce5b2c0381590fa44b943ad53b6d720881a25756c7c12519cc44ddc8.
def localCycle00065 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 3, .distance 3 4, .distance 3 6, .distance 0 3, .distance 3 5, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, 0, -1, 0, -1, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, true, false, true] }
  origin := ![.corridorUpper 2 3, .triangle 15 2, .triangle 19 0, .triangle 32 2, .triangle 11 0, .triangle 10 0, .triangle 31 1, .corridorLower 4 5, .thetaNext 3]

-- Cycle fingerprint 80c355abda3c1d8fe30d1c340dcca8147f11df0917f1cf4cc7e002f92b0d3ed2.
def localCycle00066 : Cycle where
  length := 8
  data := {
    node := ![.distance 4 5, .theta 4, .distance 3 4, .distance 2 3, .distance 1 3, .distance 1 5, .distance 0 5, .distance 3 5, .distance 4 5]
    constant := ![-1, 3, -1, 0, -3, 0, 0, 0]
    coefficient := ![0, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true, true, true] }
  origin := ![.corridorLower 4 5, .corridorUpper 3 4, .triangle 25 0, .triangle 15 2, .gapLower 1 3, .triangle 3 2, .triangle 10 1, .triangle 31 1]

-- Cycle fingerprint 82b9ba9495b268d85010da11849e219c29532b90c6ff4a6fd80d857e34911334.
def localCycle00067 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 6, .distance 1 5, .distance 1 2, .distance 0 1, .theta 1, .zero, .theta 4, .distance 3 4, .distance 1 3, .distance 1 6]
    constant := ![0, -2, -1, -2, 0, 0, 3, -1, 0]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![true, false, false, false, false, false, false, false, true] }
  origin := ![.triangle 24 1, .gapLower 1 2, .triangle 0 0, .gapLower 1 0, .thetaLower 1, .thetaUpper 4, .corridorUpper 3 4, .triangle 19 0, .triangle 21 2]

-- Cycle fingerprint 84cb98fceaed0995746b442e538f9e44c030bc32a41a57d217531e9f52cb6020.
def localCycle00068 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 4, .distance 1 3, .distance 1 5, .distance 5 6, .distance 3 5, .theta 3]
    constant := ![3, -1, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 25 0, .triangle 19 0, .triangle 20 2, .triangle 24 0, .triangle 33 0, .corridorLower 3 5]

-- Cycle fingerprint 867a75fc9adf6c032a482a02f03a5712fd247c4eb470c100f5ff9df3719d36b1.
def localCycle00069 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 4, .distance 1 3, .distance 3 6, .distance 4 6, .distance 0 4, .distance 0 3, .distance 3 5, .theta 3]
    constant := ![3, -1, -1, -1, 0, -1, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, true, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 25 0, .triangle 19 0, .triangle 21 0, .triangle 32 1, .triangle 13 0, .triangle 9 1, .triangle 10 0, .corridorLower 3 5]

-- Cycle fingerprint 8eefbdad5cc0179691f6c107183505bdf4eef5fa722964cb2dabb4b371959edf.
def localCycle00070 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 3 4, .distance 4 6, .distance 0 4, .distance 0 3, .distance 3 5, .distance 4 5, .theta 4]
    constant := ![3, -1, -1, 0, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 32 0, .triangle 13 0, .triangle 9 1, .triangle 10 0, .triangle 31 1, .corridorLower 4 5]

-- Cycle fingerprint 90510877d51f6d8f459d568d0e7491ae048453743647f345b0d8723d46a9b3d5.
def localCycle00071 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 3, .distance 1 2, .distance 0 1, .theta 1, .zero, .theta 4, .distance 3 4, .distance 2 4, .distance 1 4, .distance 1 6, .distance 1 3]
    constant := ![0, -1, -2, 0, 0, 3, 0, 0, -2, 0]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![true, false, false, false, false, false, true, true, false, true] }
  origin := ![.triangle 15 1, .triangle 0 0, .gapLower 1 0, .thetaLower 1, .thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 16 2, .gapLower 1 5, .triangle 21 1]

-- Cycle fingerprint 93fce1e9aaa66578333bdf97a3d35a5107cceefba31042ea40875d8c17f9bbc2.
def localCycle00072 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 2 4, .distance 2 5, .distance 5 6, .distance 3 6, .distance 0 3, .distance 3 5, .theta 3]
    constant := ![3, 0, 0, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 25 2, .triangle 28 2, .triangle 30 0, .triangle 33 2, .triangle 11 0, .triangle 10 0, .corridorLower 3 5]

-- Cycle fingerprint 95807b808ecce251b57627bd6e13ea913d9741c96df855044f7dffd244e0526c.
def localCycle00073 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 3, .distance 1 4, .distance 1 5, .distance 5 6, .distance 3 6, .distance 0 3, .distance 3 5, .theta 3]
    constant := ![3, 0, 0, 0, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, true, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 2, .triangle 19 2, .triangle 22 2, .triangle 24 0, .triangle 33 2, .triangle 11 0, .triangle 10 0, .corridorLower 3 5]

-- Cycle fingerprint 996a67679909d08c37ec605c599667bf3502eb11ec29a527b616f4a9c9834184.
def localCycle00074 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 1 3, .distance 1 6, .distance 0 6, .distance 3 6, .distance 4 6, .distance 4 5, .theta 4]
    constant := ![3, -1, -2, 0, 0, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, true, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 19 0, .gapLower 1 4, .triangle 4 2, .triangle 11 1, .triangle 32 1, .triangle 34 1, .corridorLower 4 5]

-- Cycle fingerprint 9b0ce93e88462f01af442f042d0be90d893311d46050de09a3cd0c73f87815fa.
def localCycle00075 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 3, .distance 3 4, .distance 0 3, .distance 3 6, .distance 4 6, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, 0, -1, -1, -1, 0, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, true, true, false, true] }
  origin := ![.corridorUpper 2 3, .triangle 15 2, .triangle 19 0, .triangle 9 0, .triangle 11 0, .triangle 32 1, .triangle 34 1, .corridorLower 4 5, .thetaNext 3]

-- Cycle fingerprint a0ec252534b08b739f616296a6d4b0e637ed2082da132b882e86f197cac2f06e.
def localCycle00076 : Cycle where
  length := 10
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 3, .distance 1 4, .distance 1 5, .distance 5 6, .distance 4 6, .distance 3 4, .distance 0 3, .distance 3 5, .theta 3]
    constant := ![3, 0, 0, 0, -1, 0, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, true, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 2, .triangle 19 2, .triangle 22 2, .triangle 24 0, .triangle 34 2, .triangle 32 0, .triangle 9 0, .triangle 10 0, .corridorLower 3 5]

-- Cycle fingerprint a2ff5cb3755d1e32664f633c7ad4da4da6dc55fd542d487509e2748060c7807a.
def localCycle00077 : Cycle where
  length := 9
  data := {
    node := ![.distance 2 4, .distance 1 4, .distance 1 6, .distance 0 6, .distance 0 3, .distance 3 5, .distance 4 5, .theta 4, .distance 3 4, .distance 2 4]
    constant := ![0, -3, 0, 0, -1, 0, -1, 3, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1, 0]
    strict := ![true, false, true, true, false, true, false, false, true] }
  origin := ![.triangle 16 2, .gapLower 1 5, .triangle 4 2, .triangle 11 1, .triangle 10 0, .triangle 31 1, .corridorLower 4 5, .corridorUpper 3 4, .triangle 25 2]

-- Cycle fingerprint a37ceb404672b18013b309cb7f3468e631d423e743152edf553efb3d882af275.
def localCycle00078 : Cycle where
  length := 9
  data := {
    node := ![.distance 2 3, .distance 3 6, .distance 1 3, .distance 1 2, .distance 2 4, .distance 3 4, .distance 0 3, .distance 3 5, .theta 3, .distance 2 3]
    constant := ![-1, -1, 0, -1, 0, -1, -1, -1, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![false, false, false, false, true, false, false, false, false] }
  origin := ![.triangle 27 0, .triangle 21 0, .gapLower 1 4, .triangle 16 0, .triangle 25 1, .triangle 9 0, .triangle 10 0, .corridorLower 3 5, .corridorUpper 2 3]

-- Cycle fingerprint a79f099c3bdc463c6bfe3da52e7b6509a6aef104b11fe7c5827dc7616653adce.
def localCycle00079 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 2, .distance 2 6, .distance 3 6, .distance 0 3, .distance 3 5, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, -1, -1, 0, -1, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, true, false, true] }
  origin := ![.corridorUpper 2 3, .triangle 15 0, .triangle 18 0, .triangle 27 1, .triangle 11 0, .triangle 10 0, .triangle 31 1, .corridorLower 4 5, .thetaNext 3]

-- Cycle fingerprint aaa066eb6d5d830b33f5844988bd0735e5f639a755e69f70d6fd4d4d5b923466.
def localCycle00080 : Cycle where
  length := 8
  data := {
    node := ![.theta 0, .zero, .theta 4, .distance 3 4, .distance 1 3, .distance 1 5, .distance 1 2, .distance 0 1, .theta 0]
    constant := ![0, 0, 3, -1, -2, -2, -1, -1]
    coefficient := ![0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 19 0, .gapLower 1 3, .gapLower 1 2, .triangle 0 0, .corridorLower 0 1]

-- Cycle fingerprint ac4051a17e464d9b7bd31bfcb88af3264e1685b1b2d469bc2a13b7b8fee80021.
def localCycle00081 : Cycle where
  length := 11
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 1 2, .distance 2 3, .distance 3 6, .distance 4 6, .distance 0 4, .distance 0 3, .distance 3 5, .distance 4 5, .theta 4]
    constant := ![3, 0, -1, -1, -1, 0, -1, 0, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, true, false, true, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 16 0, .triangle 15 0, .triangle 27 0, .triangle 32 1, .triangle 13 0, .triangle 9 1, .triangle 10 0, .triangle 31 1, .corridorLower 4 5]

-- Cycle fingerprint acfa68c92fe2451479c98e59bbf2928b7ac071983fd1546f51aa93a0ef1c5eac.
def localCycle00082 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 2, .distance 0 1, .theta 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 2 3, .distance 2 5, .distance 1 2]
    constant := ![-1, -3, 0, 0, 0, 3, -1, 0, -1]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, true, false] }
  origin := ![.triangle 0 0, .gapLower 1 0, .thetaNext 0, .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 25 0, .triangle 26 2, .triangle 17 0]

-- Cycle fingerprint adf1301a0828ca682ecfab6522233fc74df444851291243e314c3e43eec01cf0.
def localCycle00083 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 1 2, .distance 2 3, .distance 3 5, .distance 4 5, .theta 4]
    constant := ![3, 0, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 16 0, .triangle 15 0, .triangle 26 0, .triangle 31 1, .corridorLower 4 5]

-- Cycle fingerprint aed5eb686feccff0b5f2b6edbc5208f29a8d50840dc4b3644a3b35338db84b8f.
def localCycle00084 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 6, .distance 3 4, .distance 0 3, .distance 3 5, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, -1, 0, -1, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, false, true] }
  origin := ![.corridorUpper 2 3, .triangle 27 0, .triangle 32 1, .triangle 9 0, .triangle 10 0, .triangle 31 1, .corridorLower 4 5, .thetaNext 3]

-- Cycle fingerprint b42a5cebbf8abe145e5d18aae25bc2faf18f2885b39fd05d3685b212e048cf3a.
def localCycle00085 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 2 6, .distance 1 2, .distance 2 4, .distance 3 4, .distance 0 3, .distance 3 5, .theta 3]
    constant := ![3, 0, -1, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 27 2, .triangle 18 0, .triangle 16 0, .triangle 25 1, .triangle 9 0, .triangle 10 0, .corridorLower 3 5]

-- Cycle fingerprint b48ec7823cbc1ffea24fd5b2d3d461d116a358564174ff35bb7a6b7e3e8daa13.
def localCycle00086 : Cycle where
  length := 10
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 4, .distance 1 3, .distance 0 3, .distance 3 5, .distance 4 5, .distance 5 6, .theta 5, .theta 4, .theta 3]
    constant := ![3, -1, -1, 0, -1, 0, -1, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true, false, false, true, true] }
  origin := ![.corridorUpper 2 3, .triangle 25 0, .triangle 19 0, .triangle 1 2, .triangle 10 0, .triangle 31 1, .triangle 34 0, .corridorLower 5 6, .thetaNext 4, .thetaNext 3]

-- Cycle fingerprint b569a549922219a7f9808e156f4ba896757ae7a7c6426de5dab075cae533927d.
def localCycle00087 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 5, .distance 3 5, .distance 4 5, .theta 4, .distance 3 4, .distance 1 3, .distance 1 5, .distance 0 5]
    constant := ![0, 0, -1, 3, -1, -2, 0]
    coefficient := ![0, 0, 0, 1, 0, 0, 0]
    strict := ![true, true, false, false, false, false, true] }
  origin := ![.triangle 10 1, .triangle 31 1, .corridorLower 4 5, .corridorUpper 3 4, .triangle 19 0, .gapLower 1 3, .triangle 3 2]

-- Cycle fingerprint b74cc5c581e7bc20213bfdf613ca41f18e862f9d82eb3538726eabf87daade9e.
def localCycle00088 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 3 4, .distance 1 3, .distance 3 6, .distance 0 3, .distance 3 5, .distance 4 5, .theta 4]
    constant := ![3, -1, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 19 0, .triangle 21 0, .triangle 11 0, .triangle 10 0, .triangle 31 1, .corridorLower 4 5]

-- Cycle fingerprint b857449c11b2dd5e047ffe8f503acfde49ea9c7d3cefb8a302b17baf8af11bd0.
def localCycle00089 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 6, .distance 1 3, .distance 0 3, .distance 3 5, .distance 4 5, .theta 4, .theta 3, .theta 2, .theta 1, .distance 1 4, .distance 1 6]
    constant := ![-2, 0, -1, 0, -1, 0, 0, 0, 2, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0]
    strict := ![false, true, false, true, false, true, true, true, false, true] }
  origin := ![.gapLower 1 4, .triangle 1 2, .triangle 10 0, .triangle 31 1, .corridorLower 4 5, .thetaNext 3, .thetaNext 2, .thetaNext 1, .gapLower 1 6, .triangle 23 2]

-- Cycle fingerprint baa4608b9330bdf5c3b133374e1b6ee6801efda4e622a75935994d33f10b47d9.
def localCycle00090 : Cycle where
  length := 8
  data := {
    node := ![.distance 3 4, .distance 1 3, .distance 1 6, .distance 1 5, .distance 0 5, .distance 3 5, .distance 4 5, .theta 4, .distance 3 4]
    constant := ![-1, 0, -2, 0, 0, 0, -1, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, false, true, true, true, false, false] }
  origin := ![.triangle 19 0, .triangle 21 2, .gapLower 1 3, .triangle 3 2, .triangle 10 1, .triangle 31 1, .corridorLower 4 5, .corridorUpper 3 4]

-- Cycle fingerprint bcb4186d15bfcf98df4c66d7240997b5a56d9a79501f7a4ce8eec2ec83400839.
def localCycle00091 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 3, .distance 1 6, .distance 1 5, .distance 1 2, .distance 0 1, .theta 1, .zero, .theta 4, .distance 3 4, .distance 1 3]
    constant := ![0, -2, 0, -1, -2, 0, 0, 3, -1]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![true, false, true, false, false, false, false, false, false] }
  origin := ![.triangle 21 2, .gapLower 1 3, .triangle 17 1, .triangle 0 0, .gapLower 1 0, .thetaLower 1, .thetaUpper 4, .corridorUpper 3 4, .triangle 19 0]

-- Cycle fingerprint be75b5b284b7e495982baf455912cd23311dfea141a324dcab10acfaa8a9fed3.
def localCycle00092 : Cycle where
  length := 11
  data := {
    node := ![.distance 0 2, .distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 3 6, .distance 3 4, .distance 1 3, .distance 1 2, .distance 2 5, .distance 0 2]
    constant := ![0, -1, 0, 0, 3, -1, 0, -1, 0, -1, -1]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, false, false, false, false] }
  origin := ![.gapLower 0 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 27 0, .triangle 32 1, .triangle 19 0, .gapLower 1 3, .triangle 17 0, .triangle 7 0]

-- Cycle fingerprint c024c100ae04f6897ea0ffd6bb4286d6874bc4f801e9777b16b88d0eb71ec1f3.
def localCycle00093 : Cycle where
  length := 9
  data := {
    node := ![.distance 2 3, .distance 1 3, .distance 1 6, .distance 1 2, .distance 0 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 2 3]
    constant := ![0, -2, 0, -2, -1, 0, 0, 3, -1]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![true, false, true, false, false, false, false, false, false] }
  origin := ![.triangle 15 2, .gapLower 1 4, .triangle 18 1, .gapLower 1 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 25 0]

-- Cycle fingerprint c62a74f8111a44ab213b58d017abbad7d88f2eec4155cf42762fdc44c590241f.
def localCycle00094 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 2 4, .distance 2 5, .distance 5 6, .distance 4 6, .distance 3 4, .distance 0 3, .distance 3 5, .theta 3]
    constant := ![3, 0, 0, -1, 0, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 25 2, .triangle 28 2, .triangle 30 0, .triangle 34 2, .triangle 32 0, .triangle 9 0, .triangle 10 0, .corridorLower 3 5]

-- Cycle fingerprint c7c7666ec72642d6115cfde599064a78b7f85fe69ab663bfe7c80f117a13d809.
def localCycle00095 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 1, .distance 1 4, .distance 1 6, .distance 0 6, .distance 0 3, .distance 3 5, .distance 4 5, .theta 4, .zero]
    constant := ![0, 2, -2, 0, 0, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false, true, false, false] }
  origin := ![.thetaUpper 1, .gapLower 1 6, .gapLower 1 5, .triangle 4 2, .triangle 11 1, .triangle 10 0, .triangle 31 1, .corridorLower 4 5, .thetaLower 4]

-- Cycle fingerprint ccfd4d88dcb47fce0954bf3e85085f043bdc48f795cf1730fcc5d002cb4a19ec.
def localCycle00096 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 2, .distance 2 6, .distance 5 6, .distance 4 6, .distance 3 4, .distance 0 3, .distance 3 5, .theta 3]
    constant := ![3, -1, -1, 0, 0, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 0, .triangle 18 0, .triangle 30 1, .triangle 34 2, .triangle 32 0, .triangle 9 0, .triangle 10 0, .corridorLower 3 5]

-- Cycle fingerprint d1eca3127b3f292917e93f3840e3936737d751d9316064f7baf8cc304ee2084c.
def localCycle00097 : Cycle where
  length := 9
  data := {
    node := ![.distance 2 3, .distance 1 3, .distance 1 6, .distance 0 6, .distance 3 6, .distance 4 6, .distance 4 5, .theta 4, .distance 3 4, .distance 2 3]
    constant := ![0, -3, 0, 0, 0, 0, -1, 3, -1]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1, 0]
    strict := ![true, false, true, true, true, true, false, false, false] }
  origin := ![.triangle 15 2, .gapLower 1 4, .triangle 4 2, .triangle 11 1, .triangle 32 1, .triangle 34 1, .corridorLower 4 5, .corridorUpper 3 4, .triangle 25 0]

-- Cycle fingerprint d24416fb94192f46500c6018633c96bc02041570713c5d20167f03edcf609b6d.
def localCycle00098 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 4, .distance 4 6, .distance 0 4, .distance 0 3, .distance 3 5, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, -1, -1, -1, 0, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, true, false, true] }
  origin := ![.corridorUpper 2 3, .triangle 25 0, .triangle 32 0, .triangle 13 0, .triangle 9 1, .triangle 10 0, .triangle 31 1, .corridorLower 4 5, .thetaNext 3]

-- Cycle fingerprint d2d5ac11f74ffbb35c6c6b218fe82d9fae2c1ca765097be3e38e8429e91a1214.
def localCycle00099 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 4, .distance 1 3, .distance 3 6, .distance 0 3, .distance 3 5, .theta 3]
    constant := ![3, -1, -1, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 25 0, .triangle 19 0, .triangle 21 0, .triangle 11 0, .triangle 10 0, .corridorLower 3 5]

-- Cycle fingerprint d4b16e551737c7fc0e8ad7597ae92517452092b2d30e683da9d8dcf5c9bcf909.
def localCycle00100 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 2, .distance 0 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 1 3, .distance 1 6, .distance 1 5, .distance 1 2]
    constant := ![-1, -1, 0, 0, 3, -1, 0, 0, -2]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, true, false] }
  origin := ![.triangle 0 0, .corridorLower 0 1, .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 19 0, .triangle 21 2, .triangle 24 1, .gapLower 1 2]

-- Cycle fingerprint d4e61c66995aaa7ff56786efc40da203038f22e1e2031636c0725f48fb8722b0.
def localCycle00101 : Cycle where
  length := 9
  data := {
    node := ![.distance 2 4, .distance 1 4, .distance 1 6, .distance 1 3, .distance 0 3, .distance 3 5, .distance 4 5, .theta 4, .distance 3 4, .distance 2 4]
    constant := ![0, -2, -2, 0, -1, 0, -1, 3, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1, 0]
    strict := ![true, false, false, true, false, true, false, false, true] }
  origin := ![.triangle 16 2, .gapLower 1 5, .gapLower 1 4, .triangle 1 2, .triangle 10 0, .triangle 31 1, .corridorLower 4 5, .corridorUpper 3 4, .triangle 25 2]

-- Cycle fingerprint d52375e68db788f593c4f8422a3568640bb18f5e2d03a9312de2e869c0065ac6.
def localCycle00102 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 4, .distance 0 3, .distance 3 6, .distance 4 6, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, -1, -1, -1, 0, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, false, true] }
  origin := ![.corridorUpper 2 3, .triangle 25 0, .triangle 9 0, .triangle 11 0, .triangle 32 1, .triangle 34 1, .corridorLower 4 5, .thetaNext 3]

-- Cycle fingerprint d66699921845622a987d93a954de60a024071b4a3d638135adc2527e09b282fd.
def localCycle00103 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 6, .distance 1 3, .distance 3 4, .distance 0 3, .distance 3 5, .theta 3]
    constant := ![3, -1, -1, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 27 0, .triangle 21 0, .triangle 19 0, .triangle 9 0, .triangle 10 0, .corridorLower 3 5]

-- Cycle fingerprint da8104f05aedbe4ed1f580c12cfb91b59a10631a5564952788f87b6a5034a31c.
def localCycle00104 : Cycle where
  length := 6
  data := {
    node := ![.theta 4, .distance 3 4, .distance 0 3, .distance 3 5, .distance 5 6, .distance 4 5, .theta 4]
    constant := ![3, -1, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 9 0, .triangle 10 0, .triangle 33 0, .triangle 34 0, .corridorLower 4 5]

-- Cycle fingerprint de9705649ececdd5de7e38d50eb968a38e39c00a122522fc8984072ab0ca148e.
def localCycle00105 : Cycle where
  length := 11
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 2 4, .distance 1 4, .distance 1 3, .distance 1 6, .distance 1 5, .distance 1 2, .distance 0 1]
    constant := ![-1, 0, 0, 3, 0, 0, -2, 0, 0, -2, -1]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, false, true, true, false, false] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 16 2, .gapLower 1 5, .triangle 21 2, .triangle 24 1, .gapLower 1 2, .triangle 0 0]

-- Cycle fingerprint df4786f38947a95a284467ea40b8404cc74ccc35377ef97bd0533960e5b633aa.
def localCycle00106 : Cycle where
  length := 8
  data := {
    node := ![.theta 2, .distance 1 2, .distance 2 3, .distance 3 4, .distance 3 5, .distance 0 3, .distance 3 6, .theta 3, .theta 2]
    constant := ![3, -1, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, true] }
  origin := ![.corridorUpper 1 2, .triangle 15 0, .triangle 25 0, .triangle 31 2, .triangle 10 0, .triangle 11 0, .corridorLower 3 6, .thetaNext 2]

-- Cycle fingerprint e02f7efb18aeb85bffb72199b0cfb1ec5274afc23740f62997e3702b674ce1c8.
def localCycle00107 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 2, .distance 2 4, .distance 4 6, .distance 3 4, .distance 0 3, .distance 3 5, .theta 3]
    constant := ![3, -1, -1, -1, -1, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 0, .triangle 16 0, .triangle 29 0, .triangle 32 0, .gapLower 3 2, .triangle 10 0, .corridorLower 3 5]

-- Cycle fingerprint e30bf2910c175cb62dc433a85694c5da210b559b0a6488bc7540c3a6ef7ce50b.
def localCycle00108 : Cycle where
  length := 9
  data := {
    node := ![.distance 2 4, .distance 1 4, .distance 1 3, .distance 0 3, .distance 3 6, .distance 4 6, .distance 4 5, .theta 4, .distance 3 4, .distance 2 4]
    constant := ![0, -3, 0, -1, 0, 0, -1, 3, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1, 0]
    strict := ![true, false, true, false, true, true, false, false, true] }
  origin := ![.triangle 16 2, .gapLower 1 5, .triangle 1 2, .triangle 11 0, .triangle 32 1, .triangle 34 1, .corridorLower 4 5, .corridorUpper 3 4, .triangle 25 2]

-- Cycle fingerprint e679aeb0775d359346b4ac1f117e5724cc5508a57d31ac106cfd1c08f59cda8c.
def localCycle00109 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 3, .distance 1 5, .distance 0 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 2 4, .distance 1 4, .distance 1 6, .distance 1 3]
    constant := ![-2, -1, -1, 0, 0, 3, 0, 0, -2, 0]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, true, false, true] }
  origin := ![.gapLower 1 3, .triangle 3 0, .corridorLower 0 1, .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 16 2, .gapLower 1 5, .triangle 21 1]

-- Cycle fingerprint e7ddbf083fd3ea48c0e40f3c6dceeaeee19c9ebbc461ef59e54c3cb3ef8059db.
def localCycle00110 : Cycle where
  length := 11
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 3, .distance 1 2, .distance 2 6, .distance 3 6, .distance 4 6, .distance 0 4, .distance 0 3, .distance 3 5, .distance 4 5, .theta 4]
    constant := ![3, -1, -1, -1, 0, 0, -1, 0, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, false, true, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 0, .triangle 15 0, .triangle 18 0, .triangle 27 1, .triangle 32 1, .triangle 13 0, .triangle 9 1, .triangle 10 0, .triangle 31 1, .corridorLower 4 5]

-- Cycle fingerprint e8ba35ab1f430aa73eb812c2e9918c827369b0084b1f441ef23bb2dcda4eb5b3.
def localCycle00111 : Cycle where
  length := 8
  data := {
    node := ![.distance 3 4, .distance 1 3, .distance 1 5, .distance 1 2, .distance 0 1, .theta 0, .zero, .theta 4, .distance 3 4]
    constant := ![-1, 0, -2, -1, -1, 0, 0, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 1]
    strict := ![false, true, false, false, false, false, false, false] }
  origin := ![.triangle 19 0, .triangle 20 2, .gapLower 1 2, .triangle 0 0, .corridorLower 0 1, .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4]

-- Cycle fingerprint ea690ebad66241314570e52017e44f156f68cb549751b62bdebf3d7c9882421c.
def localCycle00112 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 1 3, .distance 3 4, .distance 0 3, .distance 3 5, .distance 4 5, .theta 4, .zero]
    constant := ![0, 3, 0, 0, -1, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, false, true, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 21 0, .triangle 19 0, .triangle 9 0, .triangle 10 0, .triangle 31 1, .corridorLower 4 5, .thetaLower 4]

-- Cycle fingerprint eac5669ffd40cc64d19701cd04b72bf74594bcc3d6542594131094a292c93d43.
def localCycle00113 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 3, .distance 2 5, .distance 1 2, .distance 2 6, .distance 5 6, .distance 4 5, .theta 4]
    constant := ![3, -1, 0, -1, -1, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 0, .triangle 26 2, .triangle 17 0, .triangle 18 0, .triangle 30 1, .triangle 34 0, .corridorLower 4 5]

-- Cycle fingerprint ecd20c5dbb8a4268308f9d4e1faf44327f5917760d797e9646825b1e65eb7e4c.
def localCycle00114 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 2 3, .distance 1 2, .distance 2 5, .distance 0 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, -1, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 25 0, .triangle 15 0, .triangle 17 0, .triangle 7 0, .triangle 0 1, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint ed8c5cb4d7bc8981e1c7d168896bb60515fa165747f8fec8905bf8d687feacab.
def localCycle00115 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 3, .distance 2 5, .distance 1 2, .distance 0 1, .theta 0, .zero, .theta 4]
    constant := ![3, -1, 0, -1, -3, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 1]
    strict := ![false, false, true, false, false, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 0, .triangle 26 2, .triangle 17 0, .gapLower 1 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 4]

-- Cycle fingerprint edf4d61aaa01c77454fb80084320bfc17519f199caa614b2e4d63edf69b9ad03.
def localCycle00116 : Cycle where
  length := 10
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 3, .distance 3 4, .distance 0 3, .distance 3 5, .distance 4 5, .distance 5 6, .theta 5, .theta 4, .theta 3]
    constant := ![3, 0, -1, -1, -1, 0, -1, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, true, false, false, true, true] }
  origin := ![.corridorUpper 2 3, .triangle 15 2, .triangle 19 0, .triangle 9 0, .triangle 10 0, .triangle 31 1, .triangle 34 0, .corridorLower 5 6, .thetaNext 4, .thetaNext 3]

-- Cycle fingerprint ee8b2204afd77912b49cc422559baf882ed9092fa26212e07f1f373768bb2163.
def localCycle00117 : Cycle where
  length := 6
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 2, .distance 2 6, .distance 5 6, .distance 3 5, .theta 3]
    constant := ![3, -1, -1, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 0, .triangle 18 0, .triangle 30 1, .triangle 33 0, .corridorLower 3 5]

-- Cycle fingerprint ef4cfe4a99231008ef49ba7099b0478f8e7685c127b57242abb814053657bbcf.
def localCycle00118 : Cycle where
  length := 9
  data := {
    node := ![.distance 2 4, .distance 1 4, .distance 1 6, .distance 1 2, .distance 0 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 2 4]
    constant := ![0, -2, 0, -2, -1, 0, 0, 3, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![true, false, true, false, false, false, false, false, true] }
  origin := ![.triangle 16 2, .gapLower 1 5, .triangle 18 1, .gapLower 1 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 25 2]

-- Cycle fingerprint ef8603d583effa170832eb60d788640469a7209a93c1f3f3f028bc75c8ec4286.
def localCycle00119 : Cycle where
  length := 9
  data := {
    node := ![.distance 2 3, .distance 1 3, .distance 1 5, .distance 1 2, .distance 0 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 2 3]
    constant := ![0, -2, 0, -2, -1, 0, 0, 3, -1]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![true, false, true, false, false, false, false, false, false] }
  origin := ![.triangle 15 2, .gapLower 1 3, .triangle 17 1, .gapLower 1 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 25 0]

-- Cycle fingerprint effaa402af5594c03f9bde11a84734b3921eb2c6edb9dcb63f27faff9161f226.
def localCycle00120 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 2, .distance 2 6, .distance 4 6, .distance 3 4, .distance 0 3, .distance 3 5, .theta 3]
    constant := ![3, -1, -1, 0, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 0, .triangle 18 0, .triangle 29 1, .triangle 32 0, .triangle 9 0, .triangle 10 0, .corridorLower 3 5]

-- Cycle fingerprint f485f63e7494db9808a463c3d9e00dad33855fb5645da5c09703df29ccbec281.
def localCycle00121 : Cycle where
  length := 9
  data := {
    node := ![.distance 2 5, .distance 1 2, .distance 0 1, .theta 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 2 3, .distance 2 5]
    constant := ![-1, -2, -2, 0, 0, 0, 3, -1, 0]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, true, false, false, false, false, true] }
  origin := ![.triangle 17 0, .gapLower 1 1, .gapLower 1 0, .thetaNext 0, .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 25 0, .triangle 26 2]

-- Cycle fingerprint f4e259719d7cc9df4796b783994b32141a63d14397e29d30d7f3c63d220d467e.
def localCycle00122 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 1 3, .distance 3 6, .distance 2 3, .distance 0 3, .distance 3 5, .distance 4 5, .theta 4]
    constant := ![3, -1, -1, -1, 0, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 19 0, .triangle 21 0, .triangle 27 0, .gapLower 3 2, .triangle 10 0, .triangle 31 1, .corridorLower 4 5]

-- Cycle fingerprint f576b89a899fabb7d370434b29e681c70a5b4bb6311fe496a32e0f41de072f07.
def localCycle00123 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 3, .distance 3 6, .distance 4 6, .distance 0 4, .distance 0 3, .distance 3 5, .distance 4 5, .theta 4]
    constant := ![3, -1, -1, 0, -1, 0, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 0, .triangle 27 0, .triangle 32 1, .triangle 13 0, .triangle 9 1, .triangle 10 0, .triangle 31 1, .corridorLower 4 5]

-- Cycle fingerprint f59b084ed943aca489795779784c9e671cf4e905f38075f5c257618a31cba424.
def localCycle00124 : Cycle where
  length := 9
  data := {
    node := ![.distance 3 4, .distance 1 3, .distance 1 6, .distance 1 5, .distance 1 2, .distance 0 1, .theta 1, .zero, .theta 4, .distance 3 4]
    constant := ![-1, -2, 0, 0, -1, -2, 0, 0, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1, 1]
    strict := ![false, false, true, true, false, false, false, false, false] }
  origin := ![.triangle 19 0, .gapLower 1 4, .triangle 24 1, .triangle 17 1, .triangle 0 0, .gapLower 1 0, .thetaLower 1, .thetaUpper 4, .corridorUpper 3 4]

-- Cycle fingerprint f5c1685e013c9c90ae745a5e0aa05f6a150db0a07a4e5f28ab9ccdc73a134436.
def localCycle00125 : Cycle where
  length := 10
  data := {
    node := ![.theta 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 2 3, .distance 2 6, .distance 2 5, .distance 1 2, .distance 0 1, .theta 1]
    constant := ![0, 0, 0, 3, -1, 0, 0, -1, -2, -2]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![true, false, false, false, false, true, true, false, false, false] }
  origin := ![.thetaNext 0, .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 25 0, .triangle 27 2, .triangle 30 1, .triangle 17 0, .gapLower 1 1, .gapLower 1 0]

-- Cycle fingerprint f5ebd9eb1d535c81b780118bf6b7c38242792b5619b6fb1bfa5ae243e4474fea.
def localCycle00126 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 2 3, .distance 2 6, .distance 2 5, .distance 1 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, -1, 0, 0, -1, -2, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 25 0, .triangle 27 2, .triangle 30 1, .triangle 17 0, .gapLower 1 1, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint f6ed8230b39601d3b9cae7c6b0c1a94cb2e0625b9c74bf7e006361f83eab05e1.
def localCycle00127 : Cycle where
  length := 8
  data := {
    node := ![.theta 0, .zero, .theta 4, .distance 3 4, .distance 1 3, .distance 1 6, .distance 1 5, .distance 0 1, .theta 0]
    constant := ![0, 0, 3, -1, -2, -2, -1, -1]
    coefficient := ![0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 19 0, .gapLower 1 4, .gapLower 1 3, .triangle 3 0, .corridorLower 0 1]

-- Cycle fingerprint f75918587eabedb1b0f5c373001b16fd0a71415dea341506f696fe965d9a90d7.
def localCycle00128 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 4 6, .distance 2 4, .distance 1 2, .distance 2 3, .distance 3 5, .distance 4 5, .theta 4]
    constant := ![3, -1, -1, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 32 0, .triangle 29 0, .triangle 16 0, .triangle 15 0, .triangle 26 0, .triangle 31 1, .corridorLower 4 5]

-- Cycle fingerprint f8531189eb0c4c77a3dfb7e99d7c730864b17660c02d765effb90e001a1a8a00.
def localCycle00129 : Cycle where
  length := 10
  data := {
    node := ![.theta 0, .zero, .theta 4, .distance 3 4, .distance 2 3, .distance 2 6, .distance 2 5, .distance 1 2, .distance 0 1, .theta 1, .theta 0]
    constant := ![0, 0, 3, -1, 0, 0, -1, -1, -3, 0]
    coefficient := ![0, 1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, false, false, false, true] }
  origin := ![.thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 25 0, .triangle 27 2, .triangle 30 1, .triangle 17 0, .triangle 0 0, .gapLower 1 0, .thetaNext 0]

-- Cycle fingerprint f9d07bc89d408c2d656905a001734c15ab97c3024779c0cabd76a5280fec2499.
def localCycle00130 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 2, .distance 2 6, .distance 3 6, .distance 3 4, .distance 0 3, .distance 3 5, .theta 3]
    constant := ![3, -1, -1, 0, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 0, .triangle 18 0, .triangle 27 1, .triangle 32 1, .triangle 9 0, .triangle 10 0, .corridorLower 3 5]

-- Cycle fingerprint fa65c67896c92e5fa9dacad56e276c5811ef8070551d95f36ca8c5ffd562d944.
def localCycle00131 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 1 2, .distance 2 6, .distance 2 3, .distance 0 3, .distance 3 5, .distance 4 5, .theta 4]
    constant := ![3, 0, -1, -1, 0, 0, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, false, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 16 0, .triangle 18 0, .triangle 27 1, .gapLower 3 2, .triangle 10 0, .triangle 31 1, .corridorLower 4 5]

-- Cycle fingerprint fa77864d27e59d451d8ca794d64d5b74bdfeecb62c41a18295d39addd5052387.
def localCycle00132 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 3, .distance 2 5, .distance 5 6, .distance 3 5, .distance 4 5, .theta 4]
    constant := ![3, -1, 0, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 0, .triangle 26 2, .triangle 30 0, .triangle 33 0, .triangle 31 1, .corridorLower 4 5]

-- Cycle fingerprint fcad58957fdc0db7cffbd384ded682e44e696cb132afc5123bb11f5f7ffd2aca.
def localCycle00133 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 3, .distance 2 5, .distance 1 2, .distance 2 6, .distance 3 6, .distance 4 6, .theta 4]
    constant := ![3, -1, 0, -1, -1, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 0, .triangle 26 2, .triangle 17 0, .triangle 18 0, .triangle 27 1, .triangle 32 1, .corridorLower 4 6]

-- Cycle fingerprint fdf162b872fd4259407bd146072e9c40a511bc1a5ca5cb77ff1040593f4157b7.
def localCycle00134 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 3, .distance 3 4, .distance 0 3, .distance 3 5, .distance 5 6, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, 0, -1, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false, false, true] }
  origin := ![.corridorUpper 2 3, .triangle 15 2, .triangle 19 0, .triangle 9 0, .triangle 10 0, .triangle 33 0, .triangle 34 0, .corridorLower 4 5, .thetaNext 3]

def library : Library := fun id => if id < 67 then (if id < 33 then (if id < 16 then (if id < 8 then (if id < 4 then (if id < 2 then (if id < 1 then (if id = 0 then some localCycle00000 else none) else (if id = 1 then some localCycle00001 else none)) else (if id < 3 then (if id = 2 then some localCycle00002 else none) else (if id = 3 then some localCycle00003 else none))) else (if id < 6 then (if id < 5 then (if id = 4 then some localCycle00004 else none) else (if id = 5 then some localCycle00005 else none)) else (if id < 7 then (if id = 6 then some localCycle00006 else none) else (if id = 7 then some localCycle00007 else none)))) else (if id < 12 then (if id < 10 then (if id < 9 then (if id = 8 then some localCycle00008 else none) else (if id = 9 then some localCycle00009 else none)) else (if id < 11 then (if id = 10 then some localCycle00010 else none) else (if id = 11 then some localCycle00011 else none))) else (if id < 14 then (if id < 13 then (if id = 12 then some localCycle00012 else none) else (if id = 13 then some localCycle00013 else none)) else (if id < 15 then (if id = 14 then some localCycle00014 else none) else (if id = 15 then some localCycle00015 else none))))) else (if id < 24 then (if id < 20 then (if id < 18 then (if id < 17 then (if id = 16 then some localCycle00016 else none) else (if id = 17 then some localCycle00017 else none)) else (if id < 19 then (if id = 18 then some localCycle00018 else none) else (if id = 19 then some localCycle00019 else none))) else (if id < 22 then (if id < 21 then (if id = 20 then some localCycle00020 else none) else (if id = 21 then some localCycle00021 else none)) else (if id < 23 then (if id = 22 then some localCycle00022 else none) else (if id = 23 then some localCycle00023 else none)))) else (if id < 28 then (if id < 26 then (if id < 25 then (if id = 24 then some localCycle00024 else none) else (if id = 25 then some localCycle00025 else none)) else (if id < 27 then (if id = 26 then some localCycle00026 else none) else (if id = 27 then some localCycle00027 else none))) else (if id < 30 then (if id < 29 then (if id = 28 then some localCycle00028 else none) else (if id = 29 then some localCycle00029 else none)) else (if id < 31 then (if id = 30 then some localCycle00030 else none) else (if id < 32 then (if id = 31 then some localCycle00031 else none) else (if id = 32 then some localCycle00032 else none))))))) else (if id < 50 then (if id < 41 then (if id < 37 then (if id < 35 then (if id < 34 then (if id = 33 then some localCycle00033 else none) else (if id = 34 then some localCycle00034 else none)) else (if id < 36 then (if id = 35 then some localCycle00035 else none) else (if id = 36 then some localCycle00036 else none))) else (if id < 39 then (if id < 38 then (if id = 37 then some localCycle00037 else none) else (if id = 38 then some localCycle00038 else none)) else (if id < 40 then (if id = 39 then some localCycle00039 else none) else (if id = 40 then some localCycle00040 else none)))) else (if id < 45 then (if id < 43 then (if id < 42 then (if id = 41 then some localCycle00041 else none) else (if id = 42 then some localCycle00042 else none)) else (if id < 44 then (if id = 43 then some localCycle00043 else none) else (if id = 44 then some localCycle00044 else none))) else (if id < 47 then (if id < 46 then (if id = 45 then some localCycle00045 else none) else (if id = 46 then some localCycle00046 else none)) else (if id < 48 then (if id = 47 then some localCycle00047 else none) else (if id < 49 then (if id = 48 then some localCycle00048 else none) else (if id = 49 then some localCycle00049 else none)))))) else (if id < 58 then (if id < 54 then (if id < 52 then (if id < 51 then (if id = 50 then some localCycle00050 else none) else (if id = 51 then some localCycle00051 else none)) else (if id < 53 then (if id = 52 then some localCycle00052 else none) else (if id = 53 then some localCycle00053 else none))) else (if id < 56 then (if id < 55 then (if id = 54 then some localCycle00054 else none) else (if id = 55 then some localCycle00055 else none)) else (if id < 57 then (if id = 56 then some localCycle00056 else none) else (if id = 57 then some localCycle00057 else none)))) else (if id < 62 then (if id < 60 then (if id < 59 then (if id = 58 then some localCycle00058 else none) else (if id = 59 then some localCycle00059 else none)) else (if id < 61 then (if id = 60 then some localCycle00060 else none) else (if id = 61 then some localCycle00061 else none))) else (if id < 64 then (if id < 63 then (if id = 62 then some localCycle00062 else none) else (if id = 63 then some localCycle00063 else none)) else (if id < 65 then (if id = 64 then some localCycle00064 else none) else (if id < 66 then (if id = 65 then some localCycle00065 else none) else (if id = 66 then some localCycle00066 else none)))))))) else (if id < 101 then (if id < 84 then (if id < 75 then (if id < 71 then (if id < 69 then (if id < 68 then (if id = 67 then some localCycle00067 else none) else (if id = 68 then some localCycle00068 else none)) else (if id < 70 then (if id = 69 then some localCycle00069 else none) else (if id = 70 then some localCycle00070 else none))) else (if id < 73 then (if id < 72 then (if id = 71 then some localCycle00071 else none) else (if id = 72 then some localCycle00072 else none)) else (if id < 74 then (if id = 73 then some localCycle00073 else none) else (if id = 74 then some localCycle00074 else none)))) else (if id < 79 then (if id < 77 then (if id < 76 then (if id = 75 then some localCycle00075 else none) else (if id = 76 then some localCycle00076 else none)) else (if id < 78 then (if id = 77 then some localCycle00077 else none) else (if id = 78 then some localCycle00078 else none))) else (if id < 81 then (if id < 80 then (if id = 79 then some localCycle00079 else none) else (if id = 80 then some localCycle00080 else none)) else (if id < 82 then (if id = 81 then some localCycle00081 else none) else (if id < 83 then (if id = 82 then some localCycle00082 else none) else (if id = 83 then some localCycle00083 else none)))))) else (if id < 92 then (if id < 88 then (if id < 86 then (if id < 85 then (if id = 84 then some localCycle00084 else none) else (if id = 85 then some localCycle00085 else none)) else (if id < 87 then (if id = 86 then some localCycle00086 else none) else (if id = 87 then some localCycle00087 else none))) else (if id < 90 then (if id < 89 then (if id = 88 then some localCycle00088 else none) else (if id = 89 then some localCycle00089 else none)) else (if id < 91 then (if id = 90 then some localCycle00090 else none) else (if id = 91 then some localCycle00091 else none)))) else (if id < 96 then (if id < 94 then (if id < 93 then (if id = 92 then some localCycle00092 else none) else (if id = 93 then some localCycle00093 else none)) else (if id < 95 then (if id = 94 then some localCycle00094 else none) else (if id = 95 then some localCycle00095 else none))) else (if id < 98 then (if id < 97 then (if id = 96 then some localCycle00096 else none) else (if id = 97 then some localCycle00097 else none)) else (if id < 99 then (if id = 98 then some localCycle00098 else none) else (if id < 100 then (if id = 99 then some localCycle00099 else none) else (if id = 100 then some localCycle00100 else none))))))) else (if id < 118 then (if id < 109 then (if id < 105 then (if id < 103 then (if id < 102 then (if id = 101 then some localCycle00101 else none) else (if id = 102 then some localCycle00102 else none)) else (if id < 104 then (if id = 103 then some localCycle00103 else none) else (if id = 104 then some localCycle00104 else none))) else (if id < 107 then (if id < 106 then (if id = 105 then some localCycle00105 else none) else (if id = 106 then some localCycle00106 else none)) else (if id < 108 then (if id = 107 then some localCycle00107 else none) else (if id = 108 then some localCycle00108 else none)))) else (if id < 113 then (if id < 111 then (if id < 110 then (if id = 109 then some localCycle00109 else none) else (if id = 110 then some localCycle00110 else none)) else (if id < 112 then (if id = 111 then some localCycle00111 else none) else (if id = 112 then some localCycle00112 else none))) else (if id < 115 then (if id < 114 then (if id = 113 then some localCycle00113 else none) else (if id = 114 then some localCycle00114 else none)) else (if id < 116 then (if id = 115 then some localCycle00115 else none) else (if id < 117 then (if id = 116 then some localCycle00116 else none) else (if id = 117 then some localCycle00117 else none)))))) else (if id < 126 then (if id < 122 then (if id < 120 then (if id < 119 then (if id = 118 then some localCycle00118 else none) else (if id = 119 then some localCycle00119 else none)) else (if id < 121 then (if id = 120 then some localCycle00120 else none) else (if id = 121 then some localCycle00121 else none))) else (if id < 124 then (if id < 123 then (if id = 122 then some localCycle00122 else none) else (if id = 123 then some localCycle00123 else none)) else (if id < 125 then (if id = 124 then some localCycle00124 else none) else (if id = 125 then some localCycle00125 else none)))) else (if id < 130 then (if id < 128 then (if id < 127 then (if id = 126 then some localCycle00126 else none) else (if id = 127 then some localCycle00127 else none)) else (if id < 129 then (if id = 128 then some localCycle00128 else none) else (if id = 129 then some localCycle00129 else none))) else (if id < 132 then (if id < 131 then (if id = 130 then some localCycle00130 else none) else (if id = 131 then some localCycle00131 else none)) else (if id < 133 then (if id = 132 then some localCycle00132 else none) else (if id < 134 then (if id = 133 then some localCycle00133 else none) else (if id = 134 then some localCycle00134 else none))))))))

def namedLeaf000 : LeafData := { rows := ![![1, 2, 6, 3, 5, 4], ![0, 6, 5, 4, 3, 2], ![0, 6, 5, 3, 4, 1], ![6, 0, 5, 2, 4, 1], ![6, 5, 0, 2, 3, 1], ![6, 4, 0, 3, 2, 1], ![5, 4, 3, 0, 2, 1]], proof := .tail 52 }

theorem namedLeaf000_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1920)) namedLeaf000 = true :=
  by decide +kernel

def namedLeaf001 : LeafData := { rows := ![![1, 2, 6, 3, 5, 4], ![0, 6, 5, 4, 3, 2], ![0, 6, 5, 4, 3, 1], ![6, 0, 5, 4, 2, 1], ![6, 5, 0, 3, 2, 1], ![6, 4, 0, 3, 2, 1], ![5, 4, 3, 0, 2, 1]], proof := .tail 106 }

theorem namedLeaf001_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1921)) namedLeaf001 = true :=
  by decide +kernel

def namedLeaf002 : LeafData := { rows := ![![1, 2, 5, 3, 4, 6], ![0, 2, 5, 3, 4, 6], ![0, 1, 5, 3, 4, 6], ![5, 0, 1, 2, 4, 6], ![5, 0, 1, 2, 3, 6], ![4, 3, 0, 1, 2, 6], ![0, 1, 2, 3, 4, 5]], proof := .tail 24 }

theorem namedLeaf002_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1922)) namedLeaf002 = true :=
  by decide +kernel

def namedLeaf003 : LeafData := { rows := ![![1, 2, 5, 3, 4, 6], ![0, 2, 5, 3, 4, 6], ![0, 1, 5, 3, 4, 6], ![5, 0, 1, 2, 6, 4], ![5, 0, 1, 2, 6, 3], ![4, 3, 0, 1, 2, 6], ![0, 1, 2, 4, 3, 5]], proof := .tail 70 }

theorem namedLeaf003_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1923)) namedLeaf003 = true :=
  by decide +kernel

def namedLeaf004 : LeafData := { rows := ![![1, 2, 5, 3, 4, 6], ![0, 2, 5, 3, 4, 6], ![0, 1, 5, 3, 6, 4], ![5, 0, 1, 2, 6, 4], ![5, 0, 1, 6, 2, 3], ![4, 3, 0, 1, 2, 6], ![0, 1, 4, 2, 3, 5]], proof := .tail 34 }

theorem namedLeaf004_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1924)) namedLeaf004 = true :=
  by decide +kernel

def namedLeaf005 : LeafData := { rows := ![![1, 2, 5, 3, 4, 6], ![0, 2, 5, 3, 4, 6], ![0, 1, 5, 6, 3, 4], ![5, 0, 1, 6, 2, 4], ![5, 0, 1, 6, 2, 3], ![4, 3, 0, 1, 2, 6], ![0, 1, 4, 3, 2, 5]], proof := .tail 123 }

theorem namedLeaf005_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1925)) namedLeaf005 = true :=
  by decide +kernel

def namedLeaf006 : LeafData := { rows := ![![1, 2, 5, 3, 4, 6], ![0, 2, 5, 3, 6, 4], ![0, 1, 5, 3, 6, 4], ![5, 0, 1, 2, 6, 4], ![5, 0, 6, 1, 2, 3], ![4, 3, 0, 1, 2, 6], ![0, 4, 1, 2, 3, 5]], proof := .tail 37 }

theorem namedLeaf006_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1926)) namedLeaf006 = true :=
  by decide +kernel

def namedLeaf007 : LeafData := { rows := ![![1, 2, 5, 3, 4, 6], ![0, 2, 5, 3, 6, 4], ![0, 1, 5, 6, 3, 4], ![5, 0, 1, 6, 2, 4], ![5, 0, 6, 1, 2, 3], ![4, 3, 0, 1, 2, 6], ![0, 4, 1, 3, 2, 5]], proof := .tail 9 }

theorem namedLeaf007_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1927)) namedLeaf007 = true :=
  by decide +kernel

def namedLeaf008 : LeafData := { rows := ![![1, 2, 5, 3, 4, 6], ![0, 2, 5, 6, 3, 4], ![0, 1, 5, 6, 3, 4], ![5, 0, 6, 1, 2, 4], ![5, 0, 6, 1, 2, 3], ![4, 3, 0, 1, 2, 6], ![0, 4, 3, 1, 2, 5]], proof := .tail 88 }

theorem namedLeaf008_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1928)) namedLeaf008 = true :=
  by decide +kernel

def namedLeaf009 : LeafData := { rows := ![![1, 2, 5, 3, 4, 6], ![0, 2, 5, 3, 4, 6], ![0, 1, 6, 5, 3, 4], ![5, 0, 1, 6, 2, 4], ![5, 0, 1, 6, 2, 3], ![4, 3, 0, 1, 6, 2], ![0, 1, 4, 3, 5, 2]], proof := .tail 14 }

theorem namedLeaf009_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1929)) namedLeaf009 = true :=
  by decide +kernel

def namedLeaf010 : LeafData := { rows := ![![1, 2, 5, 3, 4, 6], ![0, 2, 5, 3, 6, 4], ![0, 1, 6, 5, 3, 4], ![5, 0, 1, 6, 2, 4], ![5, 0, 6, 1, 2, 3], ![4, 3, 0, 1, 6, 2], ![0, 4, 1, 3, 5, 2]], proof := .tail 132 }

theorem namedLeaf010_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1930)) namedLeaf010 = true :=
  by decide +kernel

def namedLeaf011 : LeafData := { rows := ![![1, 2, 5, 3, 4, 6], ![0, 2, 5, 6, 3, 4], ![0, 1, 6, 5, 3, 4], ![5, 0, 6, 1, 2, 4], ![5, 0, 6, 1, 2, 3], ![4, 3, 0, 1, 6, 2], ![0, 4, 3, 1, 5, 2]], proof := .tail 132 }

theorem namedLeaf011_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1931)) namedLeaf011 = true :=
  by decide +kernel

def namedLeaf012 : LeafData := { rows := ![![1, 2, 5, 3, 4, 6], ![0, 2, 6, 5, 3, 4], ![0, 1, 6, 5, 3, 4], ![5, 0, 6, 1, 2, 4], ![5, 0, 6, 1, 2, 3], ![4, 3, 0, 6, 1, 2], ![0, 4, 3, 5, 1, 2]], proof := .tail 55 }

theorem namedLeaf012_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1932)) namedLeaf012 = true :=
  by decide +kernel

def namedLeaf013 : LeafData := { rows := ![![1, 2, 5, 3, 4, 6], ![0, 6, 2, 5, 3, 4], ![0, 6, 1, 5, 3, 4], ![5, 0, 6, 1, 2, 4], ![5, 0, 6, 1, 2, 3], ![4, 3, 0, 6, 1, 2], ![0, 4, 3, 5, 2, 1]], proof := .tail 53 }

theorem namedLeaf013_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1933)) namedLeaf013 = true :=
  by decide +kernel

def namedLeaf014 : LeafData := { rows := ![![1, 2, 5, 3, 6, 4], ![0, 2, 5, 3, 6, 4], ![0, 1, 5, 3, 6, 4], ![5, 0, 1, 2, 6, 4], ![5, 6, 0, 1, 2, 3], ![4, 3, 0, 1, 2, 6], ![4, 0, 1, 2, 3, 5]], proof := .low (![82, 115, 47, 66, 17, 77, 25, 121, 48, 10, 23, 71, 28, 36, 119, 19, 118, 51, 80, 1, 30, 111, 15, 109, 87, 101, 89, 95]) }

theorem namedLeaf014_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1934)) namedLeaf014 = true :=
  by decide +kernel

def namedLeaf015 : LeafData := { rows := ![![1, 2, 5, 3, 6, 4], ![0, 2, 5, 3, 6, 4], ![0, 1, 5, 6, 3, 4], ![5, 0, 1, 6, 2, 4], ![5, 6, 0, 1, 2, 3], ![4, 3, 0, 1, 2, 6], ![4, 0, 1, 3, 2, 5]], proof := .tail 9 }

theorem namedLeaf015_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1935)) namedLeaf015 = true :=
  by decide +kernel

def namedLeaf016 : LeafData := { rows := ![![1, 2, 5, 3, 6, 4], ![0, 2, 5, 3, 6, 4], ![0, 1, 6, 5, 3, 4], ![5, 0, 1, 6, 2, 4], ![5, 6, 0, 1, 2, 3], ![4, 3, 0, 1, 6, 2], ![4, 0, 1, 3, 5, 2]], proof := .tail 132 }

theorem namedLeaf016_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1936)) namedLeaf016 = true :=
  by decide +kernel

def namedLeaf017 : LeafData := { rows := ![![1, 2, 5, 3, 6, 4], ![0, 2, 5, 6, 3, 4], ![0, 1, 5, 6, 3, 4], ![5, 0, 6, 1, 2, 4], ![5, 6, 0, 1, 2, 3], ![4, 3, 0, 1, 2, 6], ![4, 0, 3, 1, 2, 5]], proof := .tail 88 }

theorem namedLeaf017_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1937)) namedLeaf017 = true :=
  by decide +kernel

def namedLeaf018 : LeafData := { rows := ![![1, 2, 5, 3, 6, 4], ![0, 2, 5, 6, 3, 4], ![0, 1, 6, 5, 3, 4], ![5, 0, 6, 1, 2, 4], ![5, 6, 0, 1, 2, 3], ![4, 3, 0, 1, 6, 2], ![4, 0, 3, 1, 5, 2]], proof := .tail 132 }

theorem namedLeaf018_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1938)) namedLeaf018 = true :=
  by decide +kernel

def namedLeaf019 : LeafData := { rows := ![![1, 2, 5, 3, 6, 4], ![0, 2, 6, 5, 3, 4], ![0, 1, 6, 5, 3, 4], ![5, 0, 6, 1, 2, 4], ![5, 6, 0, 1, 2, 3], ![4, 3, 0, 6, 1, 2], ![4, 0, 3, 5, 1, 2]], proof := .tail 55 }

theorem namedLeaf019_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1939)) namedLeaf019 = true :=
  by decide +kernel

def namedLeaf020 : LeafData := { rows := ![![1, 2, 5, 3, 6, 4], ![0, 6, 2, 5, 3, 4], ![0, 6, 1, 5, 3, 4], ![5, 0, 6, 1, 2, 4], ![5, 6, 0, 1, 2, 3], ![4, 3, 0, 6, 1, 2], ![4, 0, 3, 5, 2, 1]], proof := .tail 53 }

theorem namedLeaf020_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1940)) namedLeaf020 = true :=
  by decide +kernel

def namedLeaf021 : LeafData := { rows := ![![1, 2, 5, 6, 3, 4], ![0, 2, 5, 6, 3, 4], ![0, 1, 5, 6, 3, 4], ![5, 6, 0, 1, 2, 4], ![5, 6, 0, 1, 2, 3], ![4, 3, 0, 1, 2, 6], ![4, 3, 0, 1, 2, 5]], proof := .low (![129, 62, 47, 6, 97, 108, 4, 125, 67, 91, 124, 35, 28, 16, 39, 93, 64, 126, 22, 5, 105, 100, 127, 12, 90, 56, 74, 32]) }

theorem namedLeaf021_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1941)) namedLeaf021 = true :=
  by decide +kernel

def namedLeaf022 : LeafData := { rows := ![![1, 2, 5, 6, 3, 4], ![0, 2, 5, 6, 3, 4], ![0, 1, 6, 5, 3, 4], ![5, 6, 0, 1, 2, 4], ![5, 6, 0, 1, 2, 3], ![4, 3, 0, 1, 6, 2], ![4, 3, 0, 1, 5, 2]], proof := .tail 13 }

theorem namedLeaf022_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1942)) namedLeaf022 = true :=
  by decide +kernel

def namedLeaf023 : LeafData := { rows := ![![1, 2, 5, 6, 3, 4], ![0, 2, 6, 5, 3, 4], ![0, 1, 6, 5, 3, 4], ![5, 6, 0, 1, 2, 4], ![5, 6, 0, 1, 2, 3], ![4, 3, 0, 6, 1, 2], ![4, 3, 0, 5, 1, 2]], proof := .tail 18 }

theorem namedLeaf023_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1943)) namedLeaf023 = true :=
  by decide +kernel

def namedLeaf024 : LeafData := { rows := ![![1, 2, 6, 5, 3, 4], ![0, 2, 6, 5, 3, 4], ![0, 1, 6, 5, 3, 4], ![5, 6, 0, 1, 2, 4], ![5, 6, 0, 1, 2, 3], ![4, 3, 6, 0, 1, 2], ![4, 3, 5, 0, 1, 2]], proof := .tail 21 }

theorem namedLeaf024_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1944)) namedLeaf024 = true :=
  by decide +kernel

def namedLeaf025 : LeafData := { rows := ![![1, 2, 6, 5, 3, 4], ![0, 2, 6, 5, 3, 4], ![0, 1, 6, 5, 3, 4], ![6, 5, 0, 1, 2, 4], ![5, 6, 0, 1, 2, 3], ![4, 6, 3, 0, 1, 2], ![4, 5, 3, 0, 1, 2]], proof := .tail 104 }

theorem namedLeaf025_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1945)) namedLeaf025 = true :=
  by decide +kernel

def namedLeaf026 : LeafData := { rows := ![![1, 2, 6, 5, 3, 4], ![0, 2, 6, 5, 3, 4], ![0, 1, 6, 5, 3, 4], ![6, 5, 0, 1, 2, 4], ![6, 5, 0, 1, 2, 3], ![6, 4, 3, 0, 1, 2], ![5, 4, 3, 0, 1, 2]], proof := .tail 40 }

theorem namedLeaf026_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1946)) namedLeaf026 = true :=
  by decide +kernel

def namedLeaf027 : LeafData := { rows := ![![1, 2, 5, 6, 3, 4], ![0, 6, 2, 5, 3, 4], ![0, 6, 1, 5, 3, 4], ![5, 6, 0, 1, 2, 4], ![5, 6, 0, 1, 2, 3], ![4, 3, 0, 6, 1, 2], ![4, 3, 0, 5, 2, 1]], proof := .tail 113 }

theorem namedLeaf027_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1947)) namedLeaf027 = true :=
  by decide +kernel

def namedLeaf028 : LeafData := { rows := ![![1, 2, 6, 5, 3, 4], ![0, 6, 2, 5, 3, 4], ![0, 6, 1, 5, 3, 4], ![5, 6, 0, 1, 2, 4], ![5, 6, 0, 1, 2, 3], ![4, 3, 6, 0, 1, 2], ![4, 3, 5, 0, 2, 1]], proof := .tail 113 }

theorem namedLeaf028_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1948)) namedLeaf028 = true :=
  by decide +kernel

def namedLeaf029 : LeafData := { rows := ![![1, 2, 6, 5, 3, 4], ![0, 6, 2, 5, 3, 4], ![0, 6, 1, 5, 3, 4], ![6, 5, 0, 1, 2, 4], ![5, 6, 0, 1, 2, 3], ![4, 6, 3, 0, 1, 2], ![4, 5, 3, 0, 2, 1]], proof := .tail 104 }

theorem namedLeaf029_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1949)) namedLeaf029 = true :=
  by decide +kernel

def namedLeaf030 : LeafData := { rows := ![![1, 2, 6, 5, 3, 4], ![0, 6, 2, 5, 3, 4], ![0, 6, 1, 5, 3, 4], ![6, 5, 0, 1, 2, 4], ![6, 5, 0, 1, 2, 3], ![6, 4, 3, 0, 1, 2], ![5, 4, 3, 0, 2, 1]], proof := .tail 133 }

theorem namedLeaf030_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1950)) namedLeaf030 = true :=
  by decide +kernel

def namedLeaf031 : LeafData := { rows := ![![1, 2, 5, 3, 4, 6], ![0, 2, 5, 3, 4, 6], ![0, 1, 5, 4, 3, 6], ![5, 0, 1, 4, 2, 6], ![5, 0, 1, 3, 2, 6], ![4, 3, 0, 1, 2, 6], ![0, 1, 2, 3, 4, 5]], proof := .tail 38 }

theorem namedLeaf031_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1951)) namedLeaf031 = true :=
  by decide +kernel

def namedLeaf032 : LeafData := { rows := ![![1, 2, 5, 3, 4, 6], ![0, 2, 5, 3, 4, 6], ![0, 1, 5, 4, 6, 3], ![5, 0, 1, 4, 6, 2], ![5, 0, 1, 3, 2, 6], ![4, 3, 0, 1, 2, 6], ![0, 1, 3, 2, 4, 5]], proof := .tail 84 }

theorem namedLeaf032_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1952)) namedLeaf032 = true :=
  by decide +kernel

def namedLeaf033 : LeafData := { rows := ![![1, 2, 5, 3, 4, 6], ![0, 2, 5, 3, 4, 6], ![0, 1, 5, 6, 4, 3], ![5, 0, 1, 4, 6, 2], ![5, 0, 1, 3, 6, 2], ![4, 3, 0, 1, 2, 6], ![0, 1, 3, 4, 2, 5]], proof := .tail 7 }

theorem namedLeaf033_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1953)) namedLeaf033 = true :=
  by decide +kernel

def namedLeaf034 : LeafData := { rows := ![![1, 2, 5, 3, 4, 6], ![0, 2, 5, 3, 4, 6], ![0, 1, 5, 6, 4, 3], ![5, 0, 1, 6, 4, 2], ![5, 0, 1, 6, 3, 2], ![4, 3, 0, 1, 2, 6], ![0, 1, 4, 3, 2, 5]], proof := .tail 98 }

theorem namedLeaf034_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1954)) namedLeaf034 = true :=
  by decide +kernel

def namedLeaf035 : LeafData := { rows := ![![1, 2, 5, 3, 4, 6], ![0, 2, 5, 3, 6, 4], ![0, 1, 5, 6, 4, 3], ![5, 0, 1, 6, 4, 2], ![5, 0, 6, 1, 3, 2], ![4, 3, 0, 1, 2, 6], ![0, 4, 1, 3, 2, 5]], proof := .tail 98 }

theorem namedLeaf035_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1955)) namedLeaf035 = true :=
  by decide +kernel

def namedLeaf036 : LeafData := { rows := ![![1, 2, 5, 3, 4, 6], ![0, 2, 5, 6, 3, 4], ![0, 1, 5, 6, 4, 3], ![5, 0, 6, 1, 4, 2], ![5, 0, 6, 1, 3, 2], ![4, 3, 0, 1, 2, 6], ![0, 4, 3, 1, 2, 5]], proof := .tail 69 }

theorem namedLeaf036_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1956)) namedLeaf036 = true :=
  by decide +kernel

def namedLeaf037 : LeafData := { rows := ![![1, 2, 5, 3, 4, 6], ![0, 2, 5, 3, 4, 6], ![0, 1, 6, 5, 4, 3], ![5, 0, 1, 4, 6, 2], ![5, 0, 1, 3, 6, 2], ![4, 3, 0, 1, 6, 2], ![0, 1, 3, 4, 5, 2]], proof := .tail 94 }

theorem namedLeaf037_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1957)) namedLeaf037 = true :=
  by decide +kernel

def namedLeaf038 : LeafData := { rows := ![![1, 2, 5, 3, 4, 6], ![0, 2, 5, 3, 4, 6], ![0, 1, 6, 5, 4, 3], ![5, 0, 1, 6, 4, 2], ![5, 0, 1, 6, 3, 2], ![4, 3, 0, 1, 6, 2], ![0, 1, 4, 3, 5, 2]], proof := .tail 98 }

theorem namedLeaf038_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1958)) namedLeaf038 = true :=
  by decide +kernel

def namedLeaf039 : LeafData := { rows := ![![1, 2, 5, 3, 4, 6], ![0, 2, 5, 3, 6, 4], ![0, 1, 6, 5, 4, 3], ![5, 0, 1, 6, 4, 2], ![5, 0, 6, 1, 3, 2], ![4, 3, 0, 1, 6, 2], ![0, 4, 1, 3, 5, 2]], proof := .tail 98 }

theorem namedLeaf039_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1959)) namedLeaf039 = true :=
  by decide +kernel

def namedLeaf040 : LeafData := { rows := ![![1, 2, 5, 3, 4, 6], ![0, 2, 5, 6, 3, 4], ![0, 1, 6, 5, 4, 3], ![5, 0, 6, 1, 4, 2], ![5, 0, 6, 1, 3, 2], ![4, 3, 0, 1, 6, 2], ![0, 4, 3, 1, 5, 2]], proof := .tail 69 }

theorem namedLeaf040_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1960)) namedLeaf040 = true :=
  by decide +kernel

def namedLeaf041 : LeafData := { rows := ![![1, 2, 5, 3, 4, 6], ![0, 2, 6, 5, 3, 4], ![0, 1, 6, 5, 4, 3], ![5, 0, 6, 1, 4, 2], ![5, 0, 6, 1, 3, 2], ![4, 3, 0, 6, 1, 2], ![0, 4, 3, 5, 1, 2]], proof := .tail 59 }

theorem namedLeaf041_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1961)) namedLeaf041 = true :=
  by decide +kernel

def namedLeaf042 : LeafData := { rows := ![![1, 2, 5, 3, 4, 6], ![0, 6, 2, 5, 3, 4], ![0, 6, 1, 5, 4, 3], ![5, 0, 6, 1, 4, 2], ![5, 0, 6, 1, 3, 2], ![4, 3, 0, 6, 1, 2], ![0, 4, 3, 5, 2, 1]], proof := .tail 59 }

theorem namedLeaf042_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1962)) namedLeaf042 = true :=
  by decide +kernel

def namedLeaf043 : LeafData := { rows := ![![1, 2, 5, 3, 6, 4], ![0, 2, 5, 3, 6, 4], ![0, 1, 5, 6, 4, 3], ![5, 0, 1, 6, 4, 2], ![5, 6, 0, 1, 3, 2], ![4, 3, 0, 1, 2, 6], ![4, 0, 1, 3, 2, 5]], proof := .tail 58 }

theorem namedLeaf043_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1963)) namedLeaf043 = true :=
  by decide +kernel

def namedLeaf044 : LeafData := { rows := ![![1, 2, 5, 3, 6, 4], ![0, 2, 5, 3, 6, 4], ![0, 1, 6, 5, 4, 3], ![5, 0, 1, 6, 4, 2], ![5, 6, 0, 1, 3, 2], ![4, 3, 0, 1, 6, 2], ![4, 0, 1, 3, 5, 2]], proof := .tail 72 }

theorem namedLeaf044_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1964)) namedLeaf044 = true :=
  by decide +kernel

def namedLeaf045 : LeafData := { rows := ![![1, 2, 5, 3, 6, 4], ![0, 2, 5, 6, 3, 4], ![0, 1, 5, 6, 4, 3], ![5, 0, 6, 1, 4, 2], ![5, 6, 0, 1, 3, 2], ![4, 3, 0, 1, 2, 6], ![4, 0, 3, 1, 2, 5]], proof := .tail 99 }

theorem namedLeaf045_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1965)) namedLeaf045 = true :=
  by decide +kernel

def namedLeaf046 : LeafData := { rows := ![![1, 2, 5, 3, 6, 4], ![0, 2, 5, 6, 3, 4], ![0, 1, 6, 5, 4, 3], ![5, 0, 6, 1, 4, 2], ![5, 6, 0, 1, 3, 2], ![4, 3, 0, 1, 6, 2], ![4, 0, 3, 1, 5, 2]], proof := .tail 99 }

theorem namedLeaf046_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1966)) namedLeaf046 = true :=
  by decide +kernel

def namedLeaf047 : LeafData := { rows := ![![1, 2, 5, 3, 6, 4], ![0, 2, 6, 5, 3, 4], ![0, 1, 6, 5, 4, 3], ![5, 0, 6, 1, 4, 2], ![5, 6, 0, 1, 3, 2], ![4, 3, 0, 6, 1, 2], ![4, 0, 3, 5, 1, 2]], proof := .tail 59 }

theorem namedLeaf047_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1967)) namedLeaf047 = true :=
  by decide +kernel

def namedLeaf048 : LeafData := { rows := ![![1, 2, 5, 3, 6, 4], ![0, 6, 2, 5, 3, 4], ![0, 6, 1, 5, 4, 3], ![5, 0, 6, 1, 4, 2], ![5, 6, 0, 1, 3, 2], ![4, 3, 0, 6, 1, 2], ![4, 0, 3, 5, 2, 1]], proof := .tail 59 }

theorem namedLeaf048_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1968)) namedLeaf048 = true :=
  by decide +kernel

def namedLeaf049 : LeafData := { rows := ![![1, 2, 5, 6, 3, 4], ![0, 2, 5, 6, 3, 4], ![0, 1, 5, 6, 4, 3], ![5, 6, 0, 1, 4, 2], ![5, 6, 0, 1, 3, 2], ![4, 3, 0, 1, 2, 6], ![4, 3, 0, 1, 2, 5]], proof := .tail 102 }

theorem namedLeaf049_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1969)) namedLeaf049 = true :=
  by decide +kernel

def namedLeaf050 : LeafData := { rows := ![![1, 2, 5, 6, 3, 4], ![0, 2, 5, 6, 3, 4], ![0, 1, 6, 5, 4, 3], ![5, 6, 0, 1, 4, 2], ![5, 6, 0, 1, 3, 2], ![4, 3, 0, 1, 6, 2], ![4, 3, 0, 1, 5, 2]], proof := .tail 102 }

theorem namedLeaf050_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1970)) namedLeaf050 = true :=
  by decide +kernel

def namedLeaf051 : LeafData := { rows := ![![1, 2, 5, 6, 3, 4], ![0, 2, 6, 5, 3, 4], ![0, 1, 6, 5, 4, 3], ![5, 6, 0, 1, 4, 2], ![5, 6, 0, 1, 3, 2], ![4, 3, 0, 6, 1, 2], ![4, 3, 0, 5, 1, 2]], proof := .tail 68 }

theorem namedLeaf051_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1971)) namedLeaf051 = true :=
  by decide +kernel

def namedLeaf052 : LeafData := { rows := ![![1, 2, 6, 5, 3, 4], ![0, 2, 6, 5, 3, 4], ![0, 1, 6, 5, 4, 3], ![5, 6, 0, 1, 4, 2], ![5, 6, 0, 1, 3, 2], ![4, 3, 6, 0, 1, 2], ![4, 3, 5, 0, 1, 2]], proof := .tail 8 }

theorem namedLeaf052_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1972)) namedLeaf052 = true :=
  by decide +kernel

def namedLeaf053 : LeafData := { rows := ![![1, 2, 6, 5, 3, 4], ![0, 2, 6, 5, 3, 4], ![0, 1, 6, 5, 4, 3], ![6, 5, 0, 1, 4, 2], ![5, 6, 0, 1, 3, 2], ![4, 6, 3, 0, 1, 2], ![4, 5, 3, 0, 1, 2]], proof := .tail 57 }

theorem namedLeaf053_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1973)) namedLeaf053 = true :=
  by decide +kernel

def namedLeaf054 : LeafData := { rows := ![![1, 2, 6, 5, 3, 4], ![0, 2, 6, 5, 3, 4], ![0, 1, 6, 5, 4, 3], ![6, 5, 0, 1, 4, 2], ![6, 5, 0, 1, 3, 2], ![6, 4, 3, 0, 1, 2], ![5, 4, 3, 0, 1, 2]], proof := .tail 86 }

theorem namedLeaf054_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1974)) namedLeaf054 = true :=
  by decide +kernel

def namedLeaf055 : LeafData := { rows := ![![1, 2, 5, 6, 3, 4], ![0, 6, 2, 5, 3, 4], ![0, 6, 1, 5, 4, 3], ![5, 6, 0, 1, 4, 2], ![5, 6, 0, 1, 3, 2], ![4, 3, 0, 6, 1, 2], ![4, 3, 0, 5, 2, 1]], proof := .tail 68 }

theorem namedLeaf055_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1975)) namedLeaf055 = true :=
  by decide +kernel

def namedLeaf056 : LeafData := { rows := ![![1, 2, 6, 5, 3, 4], ![0, 6, 2, 5, 3, 4], ![0, 6, 1, 5, 4, 3], ![5, 6, 0, 1, 4, 2], ![5, 6, 0, 1, 3, 2], ![4, 3, 6, 0, 1, 2], ![4, 3, 5, 0, 2, 1]], proof := .tail 8 }

theorem namedLeaf056_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1976)) namedLeaf056 = true :=
  by decide +kernel

def namedLeaf057 : LeafData := { rows := ![![1, 2, 6, 5, 3, 4], ![0, 6, 2, 5, 3, 4], ![0, 6, 1, 5, 4, 3], ![6, 5, 0, 1, 4, 2], ![5, 6, 0, 1, 3, 2], ![4, 6, 3, 0, 1, 2], ![4, 5, 3, 0, 2, 1]], proof := .tail 57 }

theorem namedLeaf057_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1977)) namedLeaf057 = true :=
  by decide +kernel

def namedLeaf058 : LeafData := { rows := ![![1, 2, 6, 5, 3, 4], ![0, 6, 2, 5, 3, 4], ![0, 6, 1, 5, 4, 3], ![6, 5, 0, 1, 4, 2], ![6, 5, 0, 1, 3, 2], ![6, 4, 3, 0, 1, 2], ![5, 4, 3, 0, 2, 1]], proof := .tail 86 }

theorem namedLeaf058_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1978)) namedLeaf058 = true :=
  by decide +kernel

def namedLeaf059 : LeafData := { rows := ![![1, 2, 5, 3, 4, 6], ![0, 2, 5, 4, 3, 6], ![0, 1, 5, 4, 3, 6], ![5, 0, 4, 1, 2, 6], ![5, 0, 3, 1, 2, 6], ![4, 3, 0, 1, 2, 6], ![0, 1, 2, 3, 4, 5]], proof := .tail 112 }

theorem namedLeaf059_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1979)) namedLeaf059 = true :=
  by decide +kernel

def namedLeaf060 : LeafData := { rows := ![![1, 2, 5, 3, 4, 6], ![0, 2, 5, 4, 3, 6], ![0, 1, 5, 4, 6, 3], ![5, 0, 4, 1, 6, 2], ![5, 0, 3, 1, 2, 6], ![4, 3, 0, 1, 2, 6], ![0, 1, 3, 2, 4, 5]], proof := .tail 103 }

theorem namedLeaf060_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1980)) namedLeaf060 = true :=
  by decide +kernel

def namedLeaf061 : LeafData := { rows := ![![1, 2, 5, 3, 4, 6], ![0, 2, 5, 4, 3, 6], ![0, 1, 5, 6, 4, 3], ![5, 0, 4, 1, 6, 2], ![5, 0, 3, 1, 6, 2], ![4, 3, 0, 1, 2, 6], ![0, 1, 3, 4, 2, 5]], proof := .tail 49 }

theorem namedLeaf061_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1981)) namedLeaf061 = true :=
  by decide +kernel

def namedLeaf062 : LeafData := { rows := ![![1, 2, 5, 3, 4, 6], ![0, 2, 5, 4, 6, 3], ![0, 1, 5, 4, 6, 3], ![5, 0, 4, 6, 1, 2], ![5, 0, 3, 1, 2, 6], ![4, 3, 0, 1, 2, 6], ![0, 3, 1, 2, 4, 5]], proof := .tail 43 }

theorem namedLeaf062_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1982)) namedLeaf062 = true :=
  by decide +kernel

def namedLeaf063 : LeafData := { rows := ![![1, 2, 5, 3, 4, 6], ![0, 2, 5, 4, 6, 3], ![0, 1, 5, 6, 4, 3], ![5, 0, 4, 6, 1, 2], ![5, 0, 3, 1, 6, 2], ![4, 3, 0, 1, 2, 6], ![0, 3, 1, 4, 2, 5]], proof := .tail 7 }

theorem namedLeaf063_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1983)) namedLeaf063 = true :=
  by decide +kernel

def namedLeaf064 : LeafData := { rows := ![![1, 2, 5, 3, 4, 6], ![0, 2, 5, 6, 4, 3], ![0, 1, 5, 6, 4, 3], ![5, 0, 4, 6, 1, 2], ![5, 0, 3, 6, 1, 2], ![4, 3, 0, 1, 2, 6], ![0, 3, 4, 1, 2, 5]], proof := .tail 11 }

theorem namedLeaf064_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1984)) namedLeaf064 = true :=
  by decide +kernel

def namedLeaf065 : LeafData := { rows := ![![1, 2, 5, 3, 4, 6], ![0, 2, 5, 6, 4, 3], ![0, 1, 5, 6, 4, 3], ![5, 0, 6, 4, 1, 2], ![5, 0, 6, 3, 1, 2], ![4, 3, 0, 1, 2, 6], ![0, 4, 3, 1, 2, 5]], proof := .tail 2 }

theorem namedLeaf065_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1985)) namedLeaf065 = true :=
  by decide +kernel

def namedLeaf066 : LeafData := { rows := ![![1, 2, 5, 3, 4, 6], ![0, 2, 5, 4, 3, 6], ![0, 1, 6, 5, 4, 3], ![5, 0, 4, 1, 6, 2], ![5, 0, 3, 1, 6, 2], ![4, 3, 0, 1, 6, 2], ![0, 1, 3, 4, 5, 2]], proof := .tail 46 }

theorem namedLeaf066_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1986)) namedLeaf066 = true :=
  by decide +kernel

def namedLeaf067 : LeafData := { rows := ![![1, 2, 5, 3, 4, 6], ![0, 2, 5, 4, 6, 3], ![0, 1, 6, 5, 4, 3], ![5, 0, 4, 6, 1, 2], ![5, 0, 3, 1, 6, 2], ![4, 3, 0, 1, 6, 2], ![0, 3, 1, 4, 5, 2]], proof := .tail 94 }

theorem namedLeaf067_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1987)) namedLeaf067 = true :=
  by decide +kernel

def namedLeaf068 : LeafData := { rows := ![![1, 2, 5, 3, 4, 6], ![0, 2, 5, 6, 4, 3], ![0, 1, 6, 5, 4, 3], ![5, 0, 4, 6, 1, 2], ![5, 0, 3, 6, 1, 2], ![4, 3, 0, 1, 6, 2], ![0, 3, 4, 1, 5, 2]], proof := .tail 94 }

theorem namedLeaf068_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1988)) namedLeaf068 = true :=
  by decide +kernel

def namedLeaf069 : LeafData := { rows := ![![1, 2, 5, 3, 4, 6], ![0, 2, 5, 6, 4, 3], ![0, 1, 6, 5, 4, 3], ![5, 0, 6, 4, 1, 2], ![5, 0, 6, 3, 1, 2], ![4, 3, 0, 1, 6, 2], ![0, 4, 3, 1, 5, 2]], proof := .tail 2 }

theorem namedLeaf069_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1989)) namedLeaf069 = true :=
  by decide +kernel

def namedLeaf070 : LeafData := { rows := ![![1, 2, 5, 3, 4, 6], ![0, 2, 6, 5, 4, 3], ![0, 1, 6, 5, 4, 3], ![5, 0, 4, 6, 1, 2], ![5, 0, 3, 6, 1, 2], ![4, 3, 0, 6, 1, 2], ![0, 3, 4, 5, 1, 2]], proof := .tail 76 }

theorem namedLeaf070_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1990)) namedLeaf070 = true :=
  by decide +kernel

def namedLeaf071 : LeafData := { rows := ![![1, 2, 5, 3, 4, 6], ![0, 2, 6, 5, 4, 3], ![0, 1, 6, 5, 4, 3], ![5, 0, 6, 4, 1, 2], ![5, 0, 6, 3, 1, 2], ![4, 3, 0, 6, 1, 2], ![0, 4, 3, 5, 1, 2]], proof := .tail 2 }

theorem namedLeaf071_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1991)) namedLeaf071 = true :=
  by decide +kernel

def namedLeaf072 : LeafData := { rows := ![![1, 2, 5, 3, 4, 6], ![0, 6, 2, 5, 4, 3], ![0, 6, 1, 5, 4, 3], ![5, 0, 4, 6, 1, 2], ![5, 0, 3, 6, 1, 2], ![4, 3, 0, 6, 1, 2], ![0, 3, 4, 5, 2, 1]], proof := .tail 96 }

theorem namedLeaf072_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1992)) namedLeaf072 = true :=
  by decide +kernel

def namedLeaf073 : LeafData := { rows := ![![1, 2, 5, 3, 4, 6], ![0, 6, 2, 5, 4, 3], ![0, 6, 1, 5, 4, 3], ![5, 0, 6, 4, 1, 2], ![5, 0, 6, 3, 1, 2], ![4, 3, 0, 6, 1, 2], ![0, 4, 3, 5, 2, 1]], proof := .tail 33 }

theorem namedLeaf073_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1993)) namedLeaf073 = true :=
  by decide +kernel

def namedLeaf074 : LeafData := { rows := ![![1, 2, 5, 3, 6, 4], ![0, 2, 5, 6, 4, 3], ![0, 1, 5, 6, 4, 3], ![5, 0, 6, 4, 1, 2], ![5, 6, 0, 3, 1, 2], ![4, 3, 0, 1, 2, 6], ![4, 0, 3, 1, 2, 5]], proof := .tail 65 }

theorem namedLeaf074_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1994)) namedLeaf074 = true :=
  by decide +kernel

def namedLeaf075 : LeafData := { rows := ![![1, 2, 5, 3, 6, 4], ![0, 2, 5, 6, 4, 3], ![0, 1, 6, 5, 4, 3], ![5, 0, 6, 4, 1, 2], ![5, 6, 0, 3, 1, 2], ![4, 3, 0, 1, 6, 2], ![4, 0, 3, 1, 5, 2]], proof := .tail 20 }

theorem namedLeaf075_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1995)) namedLeaf075 = true :=
  by decide +kernel

def namedLeaf076 : LeafData := { rows := ![![1, 2, 5, 3, 6, 4], ![0, 2, 6, 5, 4, 3], ![0, 1, 6, 5, 4, 3], ![5, 0, 6, 4, 1, 2], ![5, 6, 0, 3, 1, 2], ![4, 3, 0, 6, 1, 2], ![4, 0, 3, 5, 1, 2]], proof := .tail 73 }

theorem namedLeaf076_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1996)) namedLeaf076 = true :=
  by decide +kernel

def namedLeaf077 : LeafData := { rows := ![![1, 2, 5, 3, 6, 4], ![0, 6, 2, 5, 4, 3], ![0, 6, 1, 5, 4, 3], ![5, 0, 6, 4, 1, 2], ![5, 6, 0, 3, 1, 2], ![4, 3, 0, 6, 1, 2], ![4, 0, 3, 5, 2, 1]], proof := .tail 33 }

theorem namedLeaf077_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1997)) namedLeaf077 = true :=
  by decide +kernel

def namedLeaf078 : LeafData := { rows := ![![1, 2, 5, 6, 3, 4], ![0, 2, 5, 6, 4, 3], ![0, 1, 5, 6, 4, 3], ![5, 6, 0, 4, 1, 2], ![5, 6, 0, 3, 1, 2], ![4, 3, 0, 1, 2, 6], ![4, 3, 0, 1, 2, 5]], proof := .tail 75 }

theorem namedLeaf078_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1998)) namedLeaf078 = true :=
  by decide +kernel

def namedLeaf079 : LeafData := { rows := ![![1, 2, 5, 6, 3, 4], ![0, 2, 5, 6, 4, 3], ![0, 1, 6, 5, 4, 3], ![5, 6, 0, 4, 1, 2], ![5, 6, 0, 3, 1, 2], ![4, 3, 0, 1, 6, 2], ![4, 3, 0, 1, 5, 2]], proof := .tail 75 }

theorem namedLeaf079_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1999)) namedLeaf079 = true :=
  by decide +kernel

def namedLeaf080 : LeafData := { rows := ![![1, 2, 5, 6, 3, 4], ![0, 2, 6, 5, 4, 3], ![0, 1, 6, 5, 4, 3], ![5, 6, 0, 4, 1, 2], ![5, 6, 0, 3, 1, 2], ![4, 3, 0, 6, 1, 2], ![4, 3, 0, 5, 1, 2]], proof := .tail 75 }

theorem namedLeaf080_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2000)) namedLeaf080 = true :=
  by decide +kernel

def namedLeaf081 : LeafData := { rows := ![![1, 2, 6, 5, 3, 4], ![0, 2, 6, 5, 4, 3], ![0, 1, 6, 5, 4, 3], ![5, 6, 0, 4, 1, 2], ![5, 6, 0, 3, 1, 2], ![4, 3, 6, 0, 1, 2], ![4, 3, 5, 0, 1, 2]], proof := .tail 3 }

theorem namedLeaf081_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2001)) namedLeaf081 = true :=
  by decide +kernel

def namedLeaf082 : LeafData := { rows := ![![1, 2, 6, 5, 3, 4], ![0, 2, 6, 5, 4, 3], ![0, 1, 6, 5, 4, 3], ![6, 5, 0, 4, 1, 2], ![5, 6, 0, 3, 1, 2], ![4, 6, 3, 0, 1, 2], ![4, 5, 3, 0, 1, 2]], proof := .tail 134 }

theorem namedLeaf082_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2002)) namedLeaf082 = true :=
  by decide +kernel

def namedLeaf083 : LeafData := { rows := ![![1, 2, 6, 5, 3, 4], ![0, 2, 6, 5, 4, 3], ![0, 1, 6, 5, 4, 3], ![6, 5, 0, 4, 1, 2], ![6, 5, 0, 3, 1, 2], ![6, 4, 3, 0, 1, 2], ![5, 4, 3, 0, 1, 2]], proof := .tail 116 }

theorem namedLeaf083_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2003)) namedLeaf083 = true :=
  by decide +kernel

def namedLeaf084 : LeafData := { rows := ![![1, 2, 5, 6, 3, 4], ![0, 6, 2, 5, 4, 3], ![0, 6, 1, 5, 4, 3], ![5, 6, 0, 4, 1, 2], ![5, 6, 0, 3, 1, 2], ![4, 3, 0, 6, 1, 2], ![4, 3, 0, 5, 2, 1]], proof := .tail 117 }

theorem namedLeaf084_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2004)) namedLeaf084 = true :=
  by decide +kernel

def namedLeaf085 : LeafData := { rows := ![![1, 2, 6, 5, 3, 4], ![0, 6, 2, 5, 4, 3], ![0, 6, 1, 5, 4, 3], ![5, 6, 0, 4, 1, 2], ![5, 6, 0, 3, 1, 2], ![4, 3, 6, 0, 1, 2], ![4, 3, 5, 0, 2, 1]], proof := .tail 3 }

theorem namedLeaf085_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2005)) namedLeaf085 = true :=
  by decide +kernel

def namedLeaf086 : LeafData := { rows := ![![1, 2, 6, 5, 3, 4], ![0, 6, 2, 5, 4, 3], ![0, 6, 1, 5, 4, 3], ![6, 5, 0, 4, 1, 2], ![5, 6, 0, 3, 1, 2], ![4, 6, 3, 0, 1, 2], ![4, 5, 3, 0, 2, 1]], proof := .tail 134 }

theorem namedLeaf086_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2006)) namedLeaf086 = true :=
  by decide +kernel

def namedLeaf087 : LeafData := { rows := ![![1, 2, 6, 5, 3, 4], ![0, 6, 2, 5, 4, 3], ![0, 6, 1, 5, 4, 3], ![6, 5, 0, 4, 1, 2], ![6, 5, 0, 3, 1, 2], ![6, 4, 3, 0, 1, 2], ![5, 4, 3, 0, 2, 1]], proof := .tail 116 }

theorem namedLeaf087_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2007)) namedLeaf087 = true :=
  by decide +kernel

def namedLeaf088 : LeafData := { rows := ![![1, 2, 5, 3, 4, 6], ![0, 5, 2, 3, 4, 6], ![0, 5, 1, 3, 4, 6], ![5, 0, 1, 2, 4, 6], ![5, 0, 1, 2, 3, 6], ![4, 3, 0, 2, 1, 6], ![0, 1, 2, 3, 4, 5]], proof := .tail 26 }

theorem namedLeaf088_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2008)) namedLeaf088 = true :=
  by decide +kernel

def namedLeaf089 : LeafData := { rows := ![![1, 2, 5, 3, 4, 6], ![0, 5, 2, 3, 4, 6], ![0, 5, 1, 3, 4, 6], ![5, 0, 1, 2, 6, 4], ![5, 0, 1, 2, 6, 3], ![4, 3, 0, 2, 1, 6], ![0, 1, 2, 4, 3, 5]], proof := .tail 41 }

theorem namedLeaf089_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2009)) namedLeaf089 = true :=
  by decide +kernel

def namedLeaf090 : LeafData := { rows := ![![1, 2, 5, 3, 4, 6], ![0, 5, 2, 3, 4, 6], ![0, 5, 1, 3, 6, 4], ![5, 0, 1, 2, 6, 4], ![5, 0, 1, 6, 2, 3], ![4, 3, 0, 2, 1, 6], ![0, 1, 4, 2, 3, 5]], proof := .tail 44 }

theorem namedLeaf090_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2010)) namedLeaf090 = true :=
  by decide +kernel

def namedLeaf091 : LeafData := { rows := ![![1, 2, 5, 3, 4, 6], ![0, 5, 2, 3, 4, 6], ![0, 5, 1, 6, 3, 4], ![5, 0, 1, 6, 2, 4], ![5, 0, 1, 6, 2, 3], ![4, 3, 0, 2, 1, 6], ![0, 1, 4, 3, 2, 5]], proof := .tail 27 }

theorem namedLeaf091_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2011)) namedLeaf091 = true :=
  by decide +kernel

def namedLeaf092 : LeafData := { rows := ![![1, 2, 5, 3, 4, 6], ![0, 5, 2, 3, 4, 6], ![0, 5, 1, 4, 3, 6], ![5, 0, 1, 4, 2, 6], ![5, 0, 1, 3, 2, 6], ![4, 3, 0, 2, 1, 6], ![0, 1, 2, 3, 4, 5]], proof := .tail 54 }

theorem namedLeaf092_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2012)) namedLeaf092 = true :=
  by decide +kernel

def namedLeaf093 : LeafData := { rows := ![![1, 2, 5, 3, 4, 6], ![0, 5, 2, 3, 4, 6], ![0, 5, 1, 4, 6, 3], ![5, 0, 1, 4, 6, 2], ![5, 0, 1, 3, 2, 6], ![4, 3, 0, 2, 1, 6], ![0, 1, 3, 2, 4, 5]], proof := .tail 92 }

theorem namedLeaf093_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2013)) namedLeaf093 = true :=
  by decide +kernel

def namedLeaf094 : LeafData := { rows := ![![1, 2, 5, 3, 4, 6], ![0, 5, 2, 3, 4, 6], ![0, 5, 1, 6, 4, 3], ![5, 0, 1, 4, 6, 2], ![5, 0, 1, 3, 6, 2], ![4, 3, 0, 2, 1, 6], ![0, 1, 3, 4, 2, 5]], proof := .tail 7 }

theorem namedLeaf094_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2014)) namedLeaf094 = true :=
  by decide +kernel

def namedLeaf095 : LeafData := { rows := ![![1, 2, 5, 3, 4, 6], ![0, 5, 2, 3, 4, 6], ![0, 5, 1, 6, 4, 3], ![5, 0, 1, 6, 4, 2], ![5, 0, 1, 6, 3, 2], ![4, 3, 0, 2, 1, 6], ![0, 1, 4, 3, 2, 5]], proof := .tail 0 }

theorem namedLeaf095_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2015)) namedLeaf095 = true :=
  by decide +kernel

def namedLeaf096 : LeafData := { rows := ![![1, 2, 5, 3, 4, 6], ![0, 5, 2, 3, 6, 4], ![0, 5, 1, 3, 6, 4], ![5, 0, 1, 2, 6, 4], ![5, 0, 6, 1, 2, 3], ![4, 3, 0, 2, 1, 6], ![0, 4, 1, 2, 3, 5]], proof := .tail 114 }

theorem namedLeaf096_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2016)) namedLeaf096 = true :=
  by decide +kernel

def namedLeaf097 : LeafData := { rows := ![![1, 2, 5, 3, 4, 6], ![0, 5, 2, 3, 6, 4], ![0, 5, 1, 6, 3, 4], ![5, 0, 1, 6, 2, 4], ![5, 0, 6, 1, 2, 3], ![4, 3, 0, 2, 1, 6], ![0, 4, 1, 3, 2, 5]], proof := .tail 9 }

theorem namedLeaf097_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2017)) namedLeaf097 = true :=
  by decide +kernel

def namedLeaf098 : LeafData := { rows := ![![1, 2, 5, 3, 4, 6], ![0, 5, 2, 3, 6, 4], ![0, 5, 1, 6, 4, 3], ![5, 0, 1, 6, 4, 2], ![5, 0, 6, 1, 3, 2], ![4, 3, 0, 2, 1, 6], ![0, 4, 1, 3, 2, 5]], proof := .tail 98 }

theorem namedLeaf098_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2018)) namedLeaf098 = true :=
  by decide +kernel

def namedLeaf099 : LeafData := { rows := ![![1, 2, 5, 3, 4, 6], ![0, 5, 2, 6, 3, 4], ![0, 5, 1, 6, 3, 4], ![5, 0, 6, 1, 2, 4], ![5, 0, 6, 1, 2, 3], ![4, 3, 0, 2, 1, 6], ![0, 4, 3, 1, 2, 5]], proof := .tail 88 }

theorem namedLeaf099_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2019)) namedLeaf099 = true :=
  by decide +kernel

def namedLeaf100 : LeafData := { rows := ![![1, 2, 5, 3, 4, 6], ![0, 5, 2, 6, 3, 4], ![0, 5, 1, 6, 4, 3], ![5, 0, 6, 1, 4, 2], ![5, 0, 6, 1, 3, 2], ![4, 3, 0, 2, 1, 6], ![0, 4, 3, 1, 2, 5]], proof := .tail 69 }

theorem namedLeaf100_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2020)) namedLeaf100 = true :=
  by decide +kernel

def namedLeaf101 : LeafData := { rows := ![![1, 2, 5, 3, 4, 6], ![0, 5, 2, 4, 3, 6], ![0, 5, 1, 4, 3, 6], ![5, 0, 4, 1, 2, 6], ![5, 0, 3, 1, 2, 6], ![4, 3, 0, 2, 1, 6], ![0, 1, 2, 3, 4, 5]], proof := .tail 112 }

theorem namedLeaf101_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2021)) namedLeaf101 = true :=
  by decide +kernel

def namedLeaf102 : LeafData := { rows := ![![1, 2, 5, 3, 4, 6], ![0, 5, 2, 4, 3, 6], ![0, 5, 1, 4, 6, 3], ![5, 0, 4, 1, 6, 2], ![5, 0, 3, 1, 2, 6], ![4, 3, 0, 2, 1, 6], ![0, 1, 3, 2, 4, 5]], proof := .tail 103 }

theorem namedLeaf102_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2022)) namedLeaf102 = true :=
  by decide +kernel

def namedLeaf103 : LeafData := { rows := ![![1, 2, 5, 3, 4, 6], ![0, 5, 2, 4, 3, 6], ![0, 5, 1, 6, 4, 3], ![5, 0, 4, 1, 6, 2], ![5, 0, 3, 1, 6, 2], ![4, 3, 0, 2, 1, 6], ![0, 1, 3, 4, 2, 5]], proof := .tail 49 }

theorem namedLeaf103_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2023)) namedLeaf103 = true :=
  by decide +kernel

def namedLeaf104 : LeafData := { rows := ![![1, 2, 5, 3, 4, 6], ![0, 5, 2, 4, 6, 3], ![0, 5, 1, 4, 6, 3], ![5, 0, 4, 6, 1, 2], ![5, 0, 3, 1, 2, 6], ![4, 3, 0, 2, 1, 6], ![0, 3, 1, 2, 4, 5]], proof := .tail 60 }

theorem namedLeaf104_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2024)) namedLeaf104 = true :=
  by decide +kernel

def namedLeaf105 : LeafData := { rows := ![![1, 2, 5, 3, 4, 6], ![0, 5, 2, 4, 6, 3], ![0, 5, 1, 6, 4, 3], ![5, 0, 4, 6, 1, 2], ![5, 0, 3, 1, 6, 2], ![4, 3, 0, 2, 1, 6], ![0, 3, 1, 4, 2, 5]], proof := .tail 7 }

theorem namedLeaf105_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2025)) namedLeaf105 = true :=
  by decide +kernel

def namedLeaf106 : LeafData := { rows := ![![1, 2, 5, 3, 4, 6], ![0, 5, 2, 6, 4, 3], ![0, 5, 1, 6, 4, 3], ![5, 0, 4, 6, 1, 2], ![5, 0, 3, 6, 1, 2], ![4, 3, 0, 2, 1, 6], ![0, 3, 4, 1, 2, 5]], proof := .tail 11 }

theorem namedLeaf106_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2026)) namedLeaf106 = true :=
  by decide +kernel

def namedLeaf107 : LeafData := { rows := ![![1, 2, 5, 3, 4, 6], ![0, 5, 2, 6, 4, 3], ![0, 5, 1, 6, 4, 3], ![5, 0, 6, 4, 1, 2], ![5, 0, 6, 3, 1, 2], ![4, 3, 0, 2, 1, 6], ![0, 4, 3, 1, 2, 5]], proof := .tail 2 }

theorem namedLeaf107_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2027)) namedLeaf107 = true :=
  by decide +kernel

def namedLeaf108 : LeafData := { rows := ![![1, 2, 5, 3, 4, 6], ![0, 5, 6, 2, 3, 4], ![0, 5, 6, 1, 3, 4], ![5, 0, 6, 1, 2, 4], ![5, 0, 6, 1, 2, 3], ![4, 3, 0, 2, 1, 6], ![0, 4, 3, 2, 1, 5]], proof := .tail 110 }

theorem namedLeaf108_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2028)) namedLeaf108 = true :=
  by decide +kernel

def namedLeaf109 : LeafData := { rows := ![![1, 2, 5, 3, 4, 6], ![0, 5, 6, 2, 3, 4], ![0, 5, 6, 1, 4, 3], ![5, 0, 6, 1, 4, 2], ![5, 0, 6, 1, 3, 2], ![4, 3, 0, 2, 1, 6], ![0, 4, 3, 2, 1, 5]], proof := .tail 69 }

theorem namedLeaf109_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2029)) namedLeaf109 = true :=
  by decide +kernel

def namedLeaf110 : LeafData := { rows := ![![1, 2, 5, 3, 4, 6], ![0, 5, 6, 2, 4, 3], ![0, 5, 6, 1, 4, 3], ![5, 0, 4, 6, 1, 2], ![5, 0, 3, 6, 1, 2], ![4, 3, 0, 2, 1, 6], ![0, 3, 4, 2, 1, 5]], proof := .tail 120 }

theorem namedLeaf110_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2030)) namedLeaf110 = true :=
  by decide +kernel

def namedLeaf111 : LeafData := { rows := ![![1, 2, 5, 3, 4, 6], ![0, 5, 6, 2, 4, 3], ![0, 5, 6, 1, 4, 3], ![5, 0, 6, 4, 1, 2], ![5, 0, 6, 3, 1, 2], ![4, 3, 0, 2, 1, 6], ![0, 4, 3, 2, 1, 5]], proof := .tail 79 }

theorem namedLeaf111_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2031)) namedLeaf111 = true :=
  by decide +kernel

def namedLeaf112 : LeafData := { rows := ![![1, 2, 5, 3, 4, 6], ![0, 5, 4, 2, 3, 6], ![0, 5, 4, 1, 3, 6], ![5, 0, 4, 1, 2, 6], ![5, 0, 3, 2, 1, 6], ![4, 3, 0, 2, 1, 6], ![0, 1, 2, 3, 4, 5]], proof := .tail 45 }

theorem namedLeaf112_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2032)) namedLeaf112 = true :=
  by decide +kernel

def namedLeaf113 : LeafData := { rows := ![![1, 2, 5, 3, 4, 6], ![0, 5, 4, 2, 3, 6], ![0, 5, 4, 1, 6, 3], ![5, 0, 4, 1, 6, 2], ![5, 0, 3, 2, 1, 6], ![4, 3, 0, 2, 1, 6], ![0, 1, 3, 2, 4, 5]], proof := .tail 78 }

theorem namedLeaf113_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2033)) namedLeaf113 = true :=
  by decide +kernel

def namedLeaf114 : LeafData := { rows := ![![1, 2, 5, 3, 4, 6], ![0, 5, 4, 2, 6, 3], ![0, 5, 4, 1, 6, 3], ![5, 0, 4, 6, 1, 2], ![5, 0, 3, 2, 1, 6], ![4, 3, 0, 2, 1, 6], ![0, 3, 1, 2, 4, 5]], proof := .tail 85 }

theorem namedLeaf114_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2034)) namedLeaf114 = true :=
  by decide +kernel

def namedLeaf115 : LeafData := { rows := ![![1, 2, 5, 3, 4, 6], ![0, 5, 4, 6, 2, 3], ![0, 5, 4, 6, 1, 3], ![5, 0, 4, 6, 1, 2], ![5, 0, 3, 2, 1, 6], ![4, 3, 0, 2, 1, 6], ![0, 3, 2, 1, 4, 5]], proof := .tail 130 }

theorem namedLeaf115_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2035)) namedLeaf115 = true :=
  by decide +kernel

def namedLeaf116 : LeafData := { rows := ![![1, 2, 5, 3, 4, 6], ![0, 5, 6, 4, 2, 3], ![0, 5, 4, 6, 1, 3], ![5, 0, 4, 6, 1, 2], ![5, 0, 3, 2, 6, 1], ![4, 3, 0, 2, 1, 6], ![0, 3, 2, 4, 1, 5]], proof := .tail 42 }

theorem namedLeaf116_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2036)) namedLeaf116 = true :=
  by decide +kernel

def namedLeaf117 : LeafData := { rows := ![![1, 2, 5, 3, 4, 6], ![0, 5, 6, 4, 2, 3], ![0, 5, 6, 4, 1, 3], ![5, 0, 4, 6, 1, 2], ![5, 0, 3, 6, 2, 1], ![4, 3, 0, 2, 1, 6], ![0, 3, 4, 2, 1, 5]], proof := .tail 107 }

theorem namedLeaf117_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2037)) namedLeaf117 = true :=
  by decide +kernel

def namedLeaf118 : LeafData := { rows := ![![1, 2, 5, 3, 4, 6], ![0, 5, 6, 4, 2, 3], ![0, 5, 6, 4, 1, 3], ![5, 0, 6, 4, 1, 2], ![5, 0, 6, 3, 2, 1], ![4, 3, 0, 2, 1, 6], ![0, 4, 3, 2, 1, 5]], proof := .tail 63 }

theorem namedLeaf118_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2038)) namedLeaf118 = true :=
  by decide +kernel

def namedLeaf119 : LeafData := { rows := ![![1, 2, 5, 3, 4, 6], ![0, 5, 3, 2, 4, 6], ![0, 5, 3, 1, 4, 6], ![5, 0, 2, 1, 4, 6], ![5, 0, 1, 2, 3, 6], ![4, 3, 0, 2, 1, 6], ![0, 1, 2, 3, 4, 5]], proof := .tail 31 }

theorem namedLeaf119_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2039)) namedLeaf119 = true :=
  by decide +kernel

def namedLeaf120 : LeafData := { rows := ![![1, 2, 5, 3, 4, 6], ![0, 5, 3, 2, 4, 6], ![0, 5, 3, 1, 4, 6], ![5, 0, 2, 1, 6, 4], ![5, 0, 1, 2, 6, 3], ![4, 3, 0, 2, 1, 6], ![0, 1, 2, 4, 3, 5]], proof := .tail 128 }

theorem namedLeaf120_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2040)) namedLeaf120 = true :=
  by decide +kernel

def namedLeaf121 : LeafData := { rows := ![![1, 2, 5, 3, 4, 6], ![0, 5, 3, 2, 4, 6], ![0, 5, 3, 1, 6, 4], ![5, 0, 2, 1, 6, 4], ![5, 0, 1, 6, 2, 3], ![4, 3, 0, 2, 1, 6], ![0, 1, 4, 2, 3, 5]], proof := .tail 61 }

theorem namedLeaf121_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2041)) namedLeaf121 = true :=
  by decide +kernel

def namedLeaf122 : LeafData := { rows := ![![1, 2, 5, 3, 4, 6], ![0, 5, 3, 2, 6, 4], ![0, 5, 3, 1, 6, 4], ![5, 0, 2, 1, 6, 4], ![5, 0, 6, 1, 2, 3], ![4, 3, 0, 2, 1, 6], ![0, 4, 1, 2, 3, 5]], proof := .tail 83 }

theorem namedLeaf122_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2042)) namedLeaf122 = true :=
  by decide +kernel

def namedLeaf123 : LeafData := { rows := ![![1, 2, 5, 3, 4, 6], ![0, 5, 3, 6, 2, 4], ![0, 5, 3, 6, 1, 4], ![5, 0, 2, 1, 6, 4], ![5, 0, 6, 1, 2, 3], ![4, 3, 0, 2, 1, 6], ![0, 4, 2, 1, 3, 5]], proof := .tail 131 }

theorem namedLeaf123_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2043)) namedLeaf123 = true :=
  by decide +kernel

def namedLeaf124 : LeafData := { rows := ![![1, 2, 5, 3, 4, 6], ![0, 5, 6, 3, 2, 4], ![0, 5, 3, 6, 1, 4], ![5, 0, 2, 6, 1, 4], ![5, 0, 6, 1, 2, 3], ![4, 3, 0, 2, 1, 6], ![0, 4, 2, 3, 1, 5]], proof := .tail 122 }

theorem namedLeaf124_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2044)) namedLeaf124 = true :=
  by decide +kernel

def namedLeaf125 : LeafData := { rows := ![![1, 2, 5, 3, 4, 6], ![0, 5, 6, 3, 2, 4], ![0, 5, 6, 3, 1, 4], ![5, 0, 6, 2, 1, 4], ![5, 0, 6, 1, 2, 3], ![4, 3, 0, 2, 1, 6], ![0, 4, 3, 2, 1, 5]], proof := .tail 81 }

theorem namedLeaf125_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2045)) namedLeaf125 = true :=
  by decide +kernel

def namedLeaf126 : LeafData := { rows := ![![1, 2, 5, 3, 4, 6], ![0, 5, 3, 4, 2, 6], ![0, 5, 3, 4, 1, 6], ![5, 0, 2, 1, 4, 6], ![5, 0, 2, 1, 3, 6], ![4, 3, 0, 2, 1, 6], ![0, 1, 2, 3, 4, 5]], proof := .tail 50 }

theorem namedLeaf126_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2046)) namedLeaf126 = true :=
  by decide +kernel

def namedLeaf127 : LeafData := { rows := ![![1, 2, 5, 3, 4, 6], ![0, 5, 3, 4, 2, 6], ![0, 5, 3, 4, 1, 6], ![5, 0, 2, 1, 6, 4], ![5, 0, 2, 1, 6, 3], ![4, 3, 0, 2, 1, 6], ![0, 1, 2, 4, 3, 5]], proof := .tail 29 }

theorem namedLeaf127_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2047)) namedLeaf127 = true :=
  by decide +kernel

def fallback : LeafData := { rows := fun _ _ => 0, proof := .tail 0 }
def lookup (offset : ℕ) : LeafData :=
  if offset < 128 then (if offset < 64 then (if offset < 32 then (if offset < 16 then (if offset < 8 then (if offset < 4 then (if offset < 2 then (if offset < 1 then (namedLeaf000) else (namedLeaf001)) else (if offset < 3 then (namedLeaf002) else (namedLeaf003))) else (if offset < 6 then (if offset < 5 then (namedLeaf004) else (namedLeaf005)) else (if offset < 7 then (namedLeaf006) else (namedLeaf007)))) else (if offset < 12 then (if offset < 10 then (if offset < 9 then (namedLeaf008) else (namedLeaf009)) else (if offset < 11 then (namedLeaf010) else (namedLeaf011))) else (if offset < 14 then (if offset < 13 then (namedLeaf012) else (namedLeaf013)) else (if offset < 15 then (namedLeaf014) else (namedLeaf015))))) else (if offset < 24 then (if offset < 20 then (if offset < 18 then (if offset < 17 then (namedLeaf016) else (namedLeaf017)) else (if offset < 19 then (namedLeaf018) else (namedLeaf019))) else (if offset < 22 then (if offset < 21 then (namedLeaf020) else (namedLeaf021)) else (if offset < 23 then (namedLeaf022) else (namedLeaf023)))) else (if offset < 28 then (if offset < 26 then (if offset < 25 then (namedLeaf024) else (namedLeaf025)) else (if offset < 27 then (namedLeaf026) else (namedLeaf027))) else (if offset < 30 then (if offset < 29 then (namedLeaf028) else (namedLeaf029)) else (if offset < 31 then (namedLeaf030) else (namedLeaf031)))))) else (if offset < 48 then (if offset < 40 then (if offset < 36 then (if offset < 34 then (if offset < 33 then (namedLeaf032) else (namedLeaf033)) else (if offset < 35 then (namedLeaf034) else (namedLeaf035))) else (if offset < 38 then (if offset < 37 then (namedLeaf036) else (namedLeaf037)) else (if offset < 39 then (namedLeaf038) else (namedLeaf039)))) else (if offset < 44 then (if offset < 42 then (if offset < 41 then (namedLeaf040) else (namedLeaf041)) else (if offset < 43 then (namedLeaf042) else (namedLeaf043))) else (if offset < 46 then (if offset < 45 then (namedLeaf044) else (namedLeaf045)) else (if offset < 47 then (namedLeaf046) else (namedLeaf047))))) else (if offset < 56 then (if offset < 52 then (if offset < 50 then (if offset < 49 then (namedLeaf048) else (namedLeaf049)) else (if offset < 51 then (namedLeaf050) else (namedLeaf051))) else (if offset < 54 then (if offset < 53 then (namedLeaf052) else (namedLeaf053)) else (if offset < 55 then (namedLeaf054) else (namedLeaf055)))) else (if offset < 60 then (if offset < 58 then (if offset < 57 then (namedLeaf056) else (namedLeaf057)) else (if offset < 59 then (namedLeaf058) else (namedLeaf059))) else (if offset < 62 then (if offset < 61 then (namedLeaf060) else (namedLeaf061)) else (if offset < 63 then (namedLeaf062) else (namedLeaf063))))))) else (if offset < 96 then (if offset < 80 then (if offset < 72 then (if offset < 68 then (if offset < 66 then (if offset < 65 then (namedLeaf064) else (namedLeaf065)) else (if offset < 67 then (namedLeaf066) else (namedLeaf067))) else (if offset < 70 then (if offset < 69 then (namedLeaf068) else (namedLeaf069)) else (if offset < 71 then (namedLeaf070) else (namedLeaf071)))) else (if offset < 76 then (if offset < 74 then (if offset < 73 then (namedLeaf072) else (namedLeaf073)) else (if offset < 75 then (namedLeaf074) else (namedLeaf075))) else (if offset < 78 then (if offset < 77 then (namedLeaf076) else (namedLeaf077)) else (if offset < 79 then (namedLeaf078) else (namedLeaf079))))) else (if offset < 88 then (if offset < 84 then (if offset < 82 then (if offset < 81 then (namedLeaf080) else (namedLeaf081)) else (if offset < 83 then (namedLeaf082) else (namedLeaf083))) else (if offset < 86 then (if offset < 85 then (namedLeaf084) else (namedLeaf085)) else (if offset < 87 then (namedLeaf086) else (namedLeaf087)))) else (if offset < 92 then (if offset < 90 then (if offset < 89 then (namedLeaf088) else (namedLeaf089)) else (if offset < 91 then (namedLeaf090) else (namedLeaf091))) else (if offset < 94 then (if offset < 93 then (namedLeaf092) else (namedLeaf093)) else (if offset < 95 then (namedLeaf094) else (namedLeaf095)))))) else (if offset < 112 then (if offset < 104 then (if offset < 100 then (if offset < 98 then (if offset < 97 then (namedLeaf096) else (namedLeaf097)) else (if offset < 99 then (namedLeaf098) else (namedLeaf099))) else (if offset < 102 then (if offset < 101 then (namedLeaf100) else (namedLeaf101)) else (if offset < 103 then (namedLeaf102) else (namedLeaf103)))) else (if offset < 108 then (if offset < 106 then (if offset < 105 then (namedLeaf104) else (namedLeaf105)) else (if offset < 107 then (namedLeaf106) else (namedLeaf107))) else (if offset < 110 then (if offset < 109 then (namedLeaf108) else (namedLeaf109)) else (if offset < 111 then (namedLeaf110) else (namedLeaf111))))) else (if offset < 120 then (if offset < 116 then (if offset < 114 then (if offset < 113 then (namedLeaf112) else (namedLeaf113)) else (if offset < 115 then (namedLeaf114) else (namedLeaf115))) else (if offset < 118 then (if offset < 117 then (namedLeaf116) else (namedLeaf117)) else (if offset < 119 then (namedLeaf118) else (namedLeaf119)))) else (if offset < 124 then (if offset < 122 then (if offset < 121 then (namedLeaf120) else (namedLeaf121)) else (if offset < 123 then (namedLeaf122) else (namedLeaf123))) else (if offset < 126 then (if offset < 125 then (namedLeaf124) else (namedLeaf125)) else (if offset < 127 then (namedLeaf126) else (namedLeaf127)))))))) else fallback

theorem point_checked (j : Fin 128) :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 (1920 + j.val))) (lookup j.val) = true := by
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

theorem correct (id : Fin 24698) (hlow : 1920 ≤ id.val) (hhigh : id.val < 2048) :
    leafCheck library (N4R2WordTree.catalog id) (lookup (id.val - 1920)) = true := by
  let j : Fin 128 := ⟨id.val - 1920, by omega⟩
  have hsum : 1920 + j.val = id.val := by dsimp [j]; omega
  have hindex : Fin.ofNat 24698 (1920 + j.val) = id := by
    apply Fin.ext
    simp only [Fin.ofNat, hsum, Nat.mod_eq_of_lt id.isLt]
  have hh := point_checked j
  rw [hindex] at hh
  exact hh

#print axioms point_checked
#print axioms correct
end Jsp404.N4R2OuterLeftData.LeafShard015
