import Jsp000404.N4R2OuterLeftReplay
import Jsp000404.N4R2WordCatalog

set_option autoImplicit false
set_option pp.fullNames true
set_option maxRecDepth 8192
set_option maxHeartbeats 0
set_option Elab.async false

namespace Jsp404.N4R2OuterLeftData.LeafShard002
open N4R2OuterLeftReplay

-- Cycle fingerprint 000dd8a23d7a09303bf55136b7fa09959c636739bc516003b076f04b89fbfc88.
def localCycle00000 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 2, .distance 2 6, .distance 4 6, .distance 4 5, .distance 3 4, .theta 3]
    constant := ![3, -1, -1, 0, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 0, .triangle 18 0, .triangle 29 1, .triangle 34 1, .triangle 31 0, .corridorLower 3 4]

-- Cycle fingerprint 00988dbc7eac616b6b514404a9f4df03bbce0fc47a03644466bc49c83bcea593.
def localCycle00001 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 3 5, .distance 2 3, .distance 3 6, .distance 1 3, .distance 1 2, .distance 2 4, .distance 3 4, .theta 3]
    constant := ![4, -1, -1, -1, 0, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, true, false] }
  origin := ![.gapLower 3 6, .triangle 26 0, .triangle 27 0, .triangle 21 0, .triangle 15 1, .triangle 16 0, .triangle 25 1, .corridorLower 3 4]

-- Cycle fingerprint 02ec389b3c7ba3fcbd5eb0ee5a1fa65ee42da7038b90fdc8467f20c5ff222046.
def localCycle00002 : Cycle where
  length := 11
  data := {
    node := ![.theta 3, .distance 2 3, .distance 2 4, .distance 2 5, .distance 5 6, .distance 1 5, .distance 1 2, .distance 0 1, .theta 1, .theta 0, .zero, .theta 3]
    constant := ![3, 0, 0, -1, -1, 0, -2, -2, 0, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, true, false, false, false, false, false, true, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 25 2, .triangle 28 2, .triangle 30 0, .triangle 24 0, .gapLower 1 2, .gapLower 1 1, .gapLower 1 0, .thetaNext 0, .thetaLower 0, .thetaUpper 3]

-- Cycle fingerprint 0312c781bf66036f3137f4ef2d62ed89b86ad49e3320b12eb91a4935d4b6b1f4.
def localCycle00003 : Cycle where
  length := 15
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 2 3, .distance 1 2, .distance 2 5, .distance 3 5, .distance 4 5, .distance 0 4, .distance 0 3, .distance 0 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, 0, -1, -1, -1, 0, 0, -1, 0, 0, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, true, true, false, true, true, true, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 27 0, .triangle 15 0, .triangle 17 0, .triangle 26 1, .triangle 31 1, .triangle 12 0, .triangle 9 1, .triangle 5 1, .triangle 0 1, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint 03f7ac870d26a8686894dc38a883ea61fe764b41e7b0afce2acf4d04664ceec6.
def localCycle00004 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 5, .distance 0 1, .theta 1, .zero, .theta 3, .distance 2 3, .distance 1 2, .distance 1 5]
    constant := ![-2, -2, 0, 0, 3, -1, 0]
    coefficient := ![0, 0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, false, false, false, true] }
  origin := ![.gapLower 1 1, .gapLower 1 0, .thetaLower 1, .thetaUpper 3, .corridorUpper 2 3, .triangle 15 0, .triangle 17 2]

-- Cycle fingerprint 0486913b356b2a59228ebf2b6ecca4584d26658af56df9fe289375abdb72e331.
def localCycle00005 : Cycle where
  length := 14
  data := {
    node := ![.distance 1 4, .distance 1 6, .distance 1 2, .distance 2 5, .distance 3 5, .distance 4 5, .distance 0 4, .distance 0 3, .distance 0 1, .theta 1, .zero, .theta 3, .distance 2 3, .distance 1 3, .distance 1 4]
    constant := ![-2, 0, -1, 0, 0, -1, 0, 0, -2, 0, 0, 3, 0, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![false, true, false, true, true, false, false, true, false, false, false, false, true, true] }
  origin := ![.gapLower 1 4, .triangle 18 1, .triangle 17 0, .triangle 26 1, .triangle 31 1, .triangle 12 0, .gapLower 0 3, .triangle 1 1, .gapLower 1 0, .thetaLower 1, .thetaUpper 3, .corridorUpper 2 3, .triangle 15 2, .triangle 19 2]

-- Cycle fingerprint 0611b0b6cd563623eb224ec84cbabe8c83591210f5fe1736f1e27681d6d038b0.
def localCycle00006 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 3, .distance 2 3, .distance 1 2, .distance 1 6, .distance 1 5, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, -1, 0, -2, -2, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, false] }
  origin := ![.thetaUpper 3, .corridorUpper 2 3, .triangle 15 0, .triangle 18 2, .gapLower 1 2, .gapLower 1 1, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint 07c1272ce01bd56bbdcfd7212a487b0908a510f6a91bc9a1f99afea3200eec07.
def localCycle00007 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 3, .distance 2 3, .distance 3 5, .distance 1 3, .distance 3 6, .distance 3 4, .distance 0 3, .theta 0, .zero]
    constant := ![0, 3, -1, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, false, false] }
  origin := ![.thetaUpper 3, .corridorUpper 2 3, .triangle 26 0, .triangle 20 0, .triangle 21 0, .triangle 32 1, .triangle 9 0, .corridorLower 0 3, .thetaLower 0]

-- Cycle fingerprint 08e981218163a0e28e04c3ec13d54613b568252b43e7733dafa9df43e4f0744e.
def localCycle00008 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 3, .distance 2 3, .distance 1 2, .distance 1 6, .distance 1 5, .distance 0 1, .theta 1, .zero]
    constant := ![0, 3, -1, 0, -2, -1, -2, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, false] }
  origin := ![.thetaUpper 3, .corridorUpper 2 3, .triangle 15 0, .triangle 18 2, .gapLower 1 2, .triangle 3 0, .gapLower 1 0, .thetaLower 1]

-- Cycle fingerprint 0ef393964cd49a072133accba5e03b4b3a5ab12adb46f20b87cc1c5102feb36d.
def localCycle00009 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 2 4, .distance 1 2, .distance 2 5, .distance 4 5, .distance 3 4, .distance 4 6, .theta 4]
    constant := ![3, -1, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false] }
  origin := ![.corridorUpper 2 4, .triangle 16 0, .triangle 17 0, .triangle 28 1, .triangle 31 0, .triangle 32 0, .corridorLower 4 6]

-- Cycle fingerprint 0fa836f785ab200d7fca18409d6cad9e5f127df096dd558a25b8f601d831f332.
def localCycle00010 : Cycle where
  length := 8
  data := {
    node := ![.distance 4 5, .distance 0 4, .distance 0 3, .distance 0 1, .theta 1, .distance 1 3, .distance 3 4, .distance 4 6, .distance 4 5]
    constant := ![-1, 0, 0, -2, 2, -1, -1, 0]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, true] }
  origin := ![.triangle 12 0, .gapLower 0 3, .triangle 1 1, .gapLower 1 0, .gapLower 1 6, .triangle 19 0, .triangle 32 0, .triangle 34 1]

-- Cycle fingerprint 11045ccc97c1645505d5312dd9fecaf5fc14a2ffe474b16bab1616b1ccd43087.
def localCycle00011 : Cycle where
  length := 5
  data := {
    node := ![.distance 1 2, .distance 2 6, .distance 5 6, .distance 1 6, .distance 1 5, .distance 1 2]
    constant := ![2, 0, 0, -2, -2]
    coefficient := ![0, 0, 0, 0, 0]
    strict := ![true, false, false, false, false] }
  origin := ![.gapUpper 2 2, .gapLower 6 5, .gapLower 6 4, .gapLower 1 3, .gapLower 1 2]

-- Cycle fingerprint 110a8c2a9d4c6434100aef3317e786b3f9d2d203a7067149d361bdb8c17323e9.
def localCycle00012 : Cycle where
  length := 11
  data := {
    node := ![.distance 5 6, .distance 3 5, .distance 0 3, .distance 0 2, .theta 0, .zero, .theta 1, .distance 1 3, .distance 1 4, .distance 1 5, .distance 1 6, .distance 5 6]
    constant := ![-1, -1, 0, -1, 0, 0, 2, 0, 0, -2, 0]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, true, true, false, true] }
  origin := ![.triangle 33 0, .triangle 10 0, .gapLower 0 2, .corridorLower 0 2, .thetaLower 0, .thetaUpper 1, .gapLower 1 6, .triangle 19 2, .triangle 22 2, .gapLower 1 3, .triangle 24 1]

-- Cycle fingerprint 12a52e899d7d946357340a287df441310b14da0bffd19273838b8af270418ed9.
def localCycle00013 : Cycle where
  length := 6
  data := {
    node := ![.distance 1 2, .distance 2 5, .distance 5 6, .distance 4 6, .distance 1 4, .distance 1 5, .distance 1 2]
    constant := ![2, 2, 0, -1, -3, 0]
    coefficient := ![0, 0, 0, 0, 0, 0]
    strict := ![true, true, true, false, false, true] }
  origin := ![.gapUpper 2 2, .gapUpper 5 5, .triangle 34 2, .triangle 23 0, .gapLower 1 3, .triangle 17 1]

-- Cycle fingerprint 133b7a7f568d2ee78017f739b79fc6433c54be3c0f6399cd5369867b00d7dd91.
def localCycle00014 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .theta 1, .distance 1 3, .distance 1 4, .distance 1 5, .distance 5 6, .distance 3 5, .distance 0 3, .distance 0 2, .theta 2]
    constant := ![0, 1, 0, 0, -1, -1, -1, 0, 0]
    coefficient := ![0, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![true, false, true, true, false, false, false, false, false] }
  origin := ![.thetaNext 1, .gapLower 1 6, .triangle 19 2, .triangle 22 2, .triangle 24 0, .triangle 33 0, .triangle 10 0, .gapLower 0 2, .gapLower 2 0]

-- Cycle fingerprint 13fc633c0ad6b371757e3cb6cb76bed3c8cd534a9d08fc0ba8c604349063b445.
def localCycle00015 : Cycle where
  length := 11
  data := {
    node := ![.distance 3 5, .distance 4 5, .distance 0 4, .distance 0 3, .theta 3, .distance 2 3, .distance 1 3, .distance 1 4, .distance 1 6, .distance 1 2, .distance 2 5, .distance 3 5]
    constant := ![0, -1, 0, 0, 3, 0, -2, 0, -2, -1, 0]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0]
    strict := ![true, false, false, false, false, true, false, true, false, false, true] }
  origin := ![.triangle 31 1, .triangle 12 0, .gapLower 0 3, .gapLower 3 0, .corridorUpper 2 3, .triangle 15 2, .gapLower 1 5, .triangle 23 2, .gapLower 1 3, .triangle 17 0, .triangle 26 1]

-- Cycle fingerprint 14a349495405ac50552a3011acd3d06185c6d053e1670121c33b9cd7d2b7ecf3.
def localCycle00016 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 6, .distance 3 5, .distance 1 3, .distance 1 2, .distance 2 4, .distance 3 4, .theta 3]
    constant := ![3, -1, 0, -1, 0, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 27 0, .triangle 33 1, .triangle 20 0, .triangle 15 1, .triangle 16 0, .triangle 25 1, .corridorLower 3 4]

-- Cycle fingerprint 172c4f7481207d7c9e0f6c940f81fa100f4e5c7d7f252e456c906bc2dd5247b1.
def localCycle00017 : Cycle where
  length := 9
  data := {
    node := ![.distance 2 3, .distance 1 3, .distance 1 6, .distance 1 4, .distance 1 5, .distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3]
    constant := ![0, -2, 0, -2, -1, -1, 0, 0, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1, 1]
    strict := ![true, false, true, false, false, false, false, false, false] }
  origin := ![.triangle 15 2, .gapLower 1 5, .triangle 23 1, .gapLower 1 3, .triangle 3 0, .corridorLower 0 1, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3]

-- Cycle fingerprint 174ae4beae2d9e20e73862a9ea70b2cafb792de60539bebc8fbb4ea64e84ab05.
def localCycle00018 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 2, .distance 1 6, .distance 1 5, .distance 0 1, .theta 0, .zero, .theta 3]
    constant := ![3, -1, 0, 0, -3, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 1]
    strict := ![false, false, true, true, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 0, .triangle 18 2, .triangle 24 1, .gapLower 1 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 3]

-- Cycle fingerprint 1757460e89e6f01bcb198308753f242223162f4d47aed8b6ce0b30c16cfe8bd9.
def localCycle00019 : Cycle where
  length := 14
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 2 3, .distance 1 2, .distance 2 6, .distance 3 6, .distance 4 6, .distance 4 5, .distance 0 4, .distance 0 3, .distance 0 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, -1, -1, -1, 0, 0, 0, -1, 0, 0, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, true, false, true, true, true, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 25 0, .triangle 15 0, .triangle 18 0, .triangle 27 1, .triangle 32 1, .triangle 34 1, .triangle 12 0, .triangle 9 1, .triangle 5 1, .triangle 0 1, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint 187cc0e4a853b6e5b313c0dc51546dc88b85abb696df198754f7d857700db22b.
def localCycle00020 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 3, .distance 2 3, .distance 3 4, .distance 1 3, .distance 3 5, .distance 4 5, .distance 5 6, .distance 0 5, .theta 0, .zero]
    constant := ![0, 3, -1, -1, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, false, false, false] }
  origin := ![.thetaUpper 3, .corridorUpper 2 3, .triangle 25 0, .triangle 19 0, .triangle 20 0, .triangle 31 1, .triangle 34 0, .triangle 14 0, .corridorLower 0 5, .thetaLower 0]

-- Cycle fingerprint 194f57d604075c1c6886f6bc3eff12c8028724402f6beef752068244a351db72.
def localCycle00021 : Cycle where
  length := 14
  data := {
    node := ![.zero, .theta 3, .distance 2 3, .distance 3 4, .distance 1 3, .distance 3 5, .distance 4 5, .distance 5 6, .distance 0 5, .distance 0 4, .distance 0 3, .distance 0 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, -1, -1, -1, 0, -1, -1, 0, 0, 0, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, false, true, true, true, true, false, false] }
  origin := ![.thetaUpper 3, .corridorUpper 2 3, .triangle 25 0, .triangle 19 0, .triangle 20 0, .triangle 31 1, .triangle 34 0, .triangle 14 0, .triangle 12 1, .triangle 9 1, .triangle 5 1, .triangle 0 1, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint 197b29e41fa7246389f06bc36abe5e335d9c03e32dc6175b91cee5327484c938.
def localCycle00022 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 3, .distance 2 3, .distance 3 6, .distance 3 4, .distance 1 3, .distance 3 5, .distance 4 5, .distance 0 4, .theta 0, .zero]
    constant := ![0, 3, -1, 0, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, true, false, false, false] }
  origin := ![.thetaUpper 3, .corridorUpper 2 3, .triangle 27 0, .triangle 32 1, .triangle 19 0, .triangle 20 0, .triangle 31 1, .triangle 12 0, .corridorLower 0 4, .thetaLower 0]

-- Cycle fingerprint 1af6660d60f65af8e5901b0f5488e9922f9134481c6910af75b8eb59c7450c93.
def localCycle00023 : Cycle where
  length := 4
  data := {
    node := ![.distance 1 5, .distance 1 2, .distance 2 6, .distance 5 6, .distance 1 5]
    constant := ![-3, 2, 0, -1]
    coefficient := ![0, 0, 0, 0]
    strict := ![false, true, false, false] }
  origin := ![.gapLower 1 2, .gapUpper 2 2, .gapLower 6 5, .triangle 24 0]

-- Cycle fingerprint 1b0f15d20b6e7b795cdcb2dca30080376be6908d3049fce1ceb6d2473df1e342.
def localCycle00024 : Cycle where
  length := 5
  data := {
    node := ![.distance 1 2, .distance 2 6, .distance 5 6, .distance 1 6, .distance 1 5, .distance 1 2]
    constant := ![2, 0, 0, -2, 0]
    coefficient := ![0, 0, 0, 0, 0]
    strict := ![true, false, true, false, true] }
  origin := ![.gapUpper 2 2, .gapLower 6 5, .triangle 24 2, .gapLower 1 3, .triangle 17 1]

-- Cycle fingerprint 1b2566cc18402032866fbe1f98a4e6110a4853f1238e0828deabcd62848823ef.
def localCycle00025 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 5 6, .distance 3 5, .distance 2 3, .distance 1 2, .distance 2 4, .distance 3 4, .distance 0 3, .theta 0, .zero]
    constant := ![0, 3, -1, -1, -1, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, true, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 34 0, .triangle 33 0, .triangle 26 0, .triangle 15 0, .triangle 16 0, .triangle 25 1, .triangle 9 0, .corridorLower 0 3, .thetaLower 0]

-- Cycle fingerprint 1b7c46c5c3b44417b6cbbe4fa628a19eaf9e71b3e1d3d17b512062bff941040f.
def localCycle00026 : Cycle where
  length := 6
  data := {
    node := ![.theta 1, .zero, .theta 3, .distance 2 3, .distance 1 2, .distance 0 1, .theta 1]
    constant := ![0, 0, 3, -1, -2, -2]
    coefficient := ![0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.thetaLower 1, .thetaUpper 3, .corridorUpper 2 3, .triangle 15 0, .gapLower 1 1, .gapLower 1 0]

-- Cycle fingerprint 1b9de4f5bddbe86fd77caa67a5bdbad23b5a80d541899aa68ac4212e1c6ea873.
def localCycle00027 : Cycle where
  length := 12
  data := {
    node := ![.distance 0 4, .distance 0 3, .theta 0, .zero, .theta 1, .distance 1 3, .distance 1 4, .distance 1 2, .distance 2 6, .distance 3 6, .distance 4 6, .distance 4 5, .distance 0 4]
    constant := ![0, -1, 0, 0, 2, 0, -2, -1, 0, 0, 0, -1]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, false, true, true, true, false] }
  origin := ![.gapLower 0 3, .corridorLower 0 3, .thetaLower 0, .thetaUpper 1, .gapLower 1 6, .triangle 19 2, .gapLower 1 4, .triangle 18 0, .triangle 27 1, .triangle 32 1, .triangle 34 1, .triangle 12 0]

-- Cycle fingerprint 1d2938958239ccdc44a2b9513f673f5f08934b578c4af0f138bf2ec252b17a83.
def localCycle00028 : Cycle where
  length := 8
  data := {
    node := ![.distance 1 2, .distance 0 1, .theta 0, .zero, .theta 6, .distance 5 6, .distance 4 6, .distance 2 4, .distance 1 2]
    constant := ![-2, -1, 0, 0, 3, 0, -1, -1]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, false] }
  origin := ![.gapLower 1 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 29 0, .triangle 16 0]

-- Cycle fingerprint 1dbfe66f9a8a5314850ed079a6948b4d0d3b91d638ef0d6a7bef8a0344304ba0.
def localCycle00029 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 4, .distance 1 3, .distance 3 5, .distance 5 6, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, -1, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, true] }
  origin := ![.corridorUpper 2 3, .triangle 25 0, .triangle 19 0, .triangle 20 0, .triangle 33 0, .triangle 34 0, .corridorLower 4 5, .thetaNext 3]

-- Cycle fingerprint 1dd1a99ff3202ad8ebbddd2af646141058dbced4692dcf49971f56a12596d9c3.
def localCycle00030 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 3, .distance 2 3, .distance 3 4, .distance 1 3, .distance 3 6, .distance 4 6, .distance 4 5, .distance 0 4, .theta 0, .zero]
    constant := ![0, 3, -1, -1, -1, 0, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, false, false, false] }
  origin := ![.thetaUpper 3, .corridorUpper 2 3, .triangle 25 0, .triangle 19 0, .triangle 21 0, .triangle 32 1, .triangle 34 1, .triangle 12 0, .corridorLower 0 4, .thetaLower 0]

-- Cycle fingerprint 208328a2fabc9318a3adeec5bc0d263864627e8b1a8b0a06c9418d8ca10ad5f6.
def localCycle00031 : Cycle where
  length := 12
  data := {
    node := ![.distance 0 4, .distance 0 3, .theta 0, .zero, .theta 1, .distance 1 3, .distance 1 4, .distance 1 2, .distance 2 6, .distance 3 6, .distance 4 6, .distance 4 5, .distance 0 4]
    constant := ![0, -1, 0, 0, 2, -2, 0, -1, 0, 0, 0, -1]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, false, true, true, true, false] }
  origin := ![.gapLower 0 3, .corridorLower 0 3, .thetaLower 0, .thetaUpper 1, .gapLower 1 6, .gapLower 1 5, .triangle 16 1, .triangle 18 0, .triangle 27 1, .triangle 32 1, .triangle 34 1, .triangle 12 0]

-- Cycle fingerprint 237d5070fc3f7ae483a1b86aa9baa1d2172b620647b3c3fc329676465a9d221c.
def localCycle00032 : Cycle where
  length := 12
  data := {
    node := ![.distance 4 6, .distance 4 5, .distance 0 4, .distance 0 3, .distance 0 1, .theta 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 1 3, .distance 3 4, .distance 4 6]
    constant := ![0, -1, 0, 0, -3, 0, 0, 0, 3, 0, -1, -1]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![true, false, false, true, false, true, false, false, false, true, false, false] }
  origin := ![.triangle 34 1, .triangle 12 0, .gapLower 0 3, .triangle 1 1, .gapLower 1 0, .thetaNext 0, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 15 2, .triangle 19 0, .triangle 32 0]

-- Cycle fingerprint 23da01ee4b26c7f54961d988f131382330c79cb44ed8be4058309b3a40666ba0.
def localCycle00033 : Cycle where
  length := 13
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 2 3, .distance 1 2, .distance 2 4, .distance 3 4, .distance 0 3, .distance 0 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, 0, -1, -1, -1, 0, -1, 0, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, true, false, true, true, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 27 0, .triangle 15 0, .triangle 16 0, .triangle 25 1, .triangle 9 0, .triangle 5 1, .triangle 0 1, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint 2489359457ccb53dea061f1de7f57660705b25362b4f83a38c98bf89867bdb26.
def localCycle00034 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 3, .distance 1 4, .distance 1 6, .distance 1 5, .distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 1 3]
    constant := ![0, -2, -2, -1, -1, 0, 0, 3, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![true, false, false, false, false, false, false, false, true] }
  origin := ![.triangle 19 2, .gapLower 1 4, .gapLower 1 3, .triangle 3 0, .corridorLower 0 1, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 15 2]

-- Cycle fingerprint 24ba3179a9053286c661b3b2af700606300372f9dedd7d8de48e8b70d1ac4eea.
def localCycle00035 : Cycle where
  length := 3
  data := {
    node := ![.distance 5 6, .distance 1 5, .distance 1 6, .distance 5 6]
    constant := ![2, -3, 0]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.gapUpper 5 4, .gapLower 1 3, .triangle 24 1]

-- Cycle fingerprint 26458611282b0488e7a55dfa7e5d5ecd8761c0cdd0c79cc7d8d1903e7d06ad14.
def localCycle00036 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 3, .distance 1 4, .distance 0 1, .theta 1, .zero, .theta 3, .distance 2 3, .distance 1 3]
    constant := ![-2, -1, -2, 0, 0, 3, 0]
    coefficient := ![0, 0, 0, 0, 1, 1, 0]
    strict := ![false, false, false, false, false, false, true] }
  origin := ![.gapLower 1 5, .triangle 2 0, .gapLower 1 0, .thetaLower 1, .thetaUpper 3, .corridorUpper 2 3, .triangle 15 2]

-- Cycle fingerprint 2654d76553b36f5f18517180e7847a28fe8ef0d0c05a4583fe5ed1cfad619e7d.
def localCycle00037 : Cycle where
  length := 13
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 3, .distance 1 2, .distance 2 6, .distance 3 6, .distance 3 4, .distance 0 3, .distance 0 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, -1, -1, -1, 0, 0, -1, 0, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, true, true, false, true, true, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 0, .triangle 15 0, .triangle 18 0, .triangle 27 1, .triangle 32 1, .triangle 9 0, .triangle 5 1, .triangle 0 1, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint 287bea02c8e599a9102104f050bdcce05756b09faf2462873d9678e49aed30be.
def localCycle00038 : Cycle where
  length := 13
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 3, .distance 2 6, .distance 1 2, .distance 2 4, .distance 3 4, .distance 0 3, .distance 0 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, -1, 0, -1, -1, 0, -1, 0, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false, true, false, true, true, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 0, .triangle 27 2, .triangle 18 0, .triangle 16 0, .triangle 25 1, .triangle 9 0, .triangle 5 1, .triangle 0 1, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint 28db2d48469496830c523a3b9a3a2174dbd009e0dce30c8791bcee645ec4bd70.
def localCycle00039 : Cycle where
  length := 6
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 2, .distance 2 6, .distance 4 6, .distance 3 4, .theta 3]
    constant := ![3, -1, -1, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 0, .triangle 18 0, .triangle 29 1, .triangle 32 0, .corridorLower 3 4]

-- Cycle fingerprint 29057015d64b2bab694a6dd01e0e569c2a197b26775a96a8bb18a277247473ad.
def localCycle00040 : Cycle where
  length := 9
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 4, .distance 2 3, .distance 1 2, .distance 2 6, .distance 3 6, .distance 4 6, .distance 5 6, .theta 5]
    constant := ![3, -1, -1, -1, -1, 0, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, true, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 0, .triangle 25 0, .triangle 15 0, .triangle 18 0, .triangle 27 1, .triangle 32 1, .triangle 34 1, .corridorLower 5 6]

-- Cycle fingerprint 292bf4752e3f9d66c4a4acc7b04e7720108825aca665bd50d1cb58fc7191fe9d.
def localCycle00041 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 4, .distance 1 6, .distance 1 2, .distance 0 1, .theta 1, .zero, .theta 3, .distance 2 3, .distance 1 3, .distance 1 4]
    constant := ![0, -2, -1, -2, 0, 0, 3, 0, 0]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![true, false, false, false, false, false, false, true, true] }
  origin := ![.triangle 23 2, .gapLower 1 3, .triangle 0 0, .gapLower 1 0, .thetaLower 1, .thetaUpper 3, .corridorUpper 2 3, .triangle 15 2, .triangle 19 2]

-- Cycle fingerprint 29f523a73dc0dd011697371eb87963440e14706c4b9dbf88272a701b46c17a13.
def localCycle00042 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 4, .distance 1 6, .distance 1 5, .distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 1 3, .distance 1 4]
    constant := ![0, -3, -1, -1, 0, 0, 3, 0, 0]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![true, false, false, false, false, false, false, true, true] }
  origin := ![.triangle 23 2, .gapLower 1 3, .triangle 3 0, .corridorLower 0 1, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 15 2, .triangle 19 2]

-- Cycle fingerprint 2a84e0af2bddc83de40dadfb29288a1c6bf05493b81766d6d51c9756dacad159.
def localCycle00043 : Cycle where
  length := 5
  data := {
    node := ![.distance 1 2, .distance 2 6, .distance 5 6, .distance 1 6, .distance 1 5, .distance 1 2]
    constant := ![2, 0, 0, -3, 0]
    coefficient := ![0, 0, 0, 0, 0]
    strict := ![true, false, false, false, true] }
  origin := ![.gapUpper 2 2, .gapLower 6 5, .gapLower 6 4, .gapLower 1 3, .triangle 17 1]

-- Cycle fingerprint 2b2a185e2fd120d4a3bf85921e7a289db442748c8bb489c87e5625c4dfb566dd.
def localCycle00044 : Cycle where
  length := 13
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 2 3, .distance 3 5, .distance 1 3, .distance 1 2, .distance 2 4, .distance 0 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, 0, -1, -1, -1, 0, -1, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, true, false, false, true, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 27 0, .triangle 26 0, .triangle 20 0, .triangle 15 1, .triangle 16 0, .triangle 6 0, .triangle 0 1, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint 2bce6387ae51baf26d1f4395ceddca69b39c9c3b254dfbcc3855bc4161b2933d.
def localCycle00045 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 2, .distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 1 3, .distance 1 4, .distance 1 5, .distance 1 6, .distance 1 2]
    constant := ![-2, -1, 0, 0, 3, 0, 0, 0, -2, 0]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, true, false, true] }
  origin := ![.gapLower 1 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 15 2, .triangle 19 2, .triangle 22 2, .gapLower 1 3, .triangle 18 1]

-- Cycle fingerprint 2f27772198e6ce0006d5eb4bd28be686844cd0071e330caf952f90cf3bbcef00.
def localCycle00046 : Cycle where
  length := 12
  data := {
    node := ![.theta 1, .zero, .theta 3, .distance 2 3, .distance 1 3, .distance 1 6, .distance 3 6, .distance 3 4, .distance 4 5, .distance 0 4, .distance 0 3, .distance 0 1, .theta 1]
    constant := ![0, 0, 3, 0, -2, 0, 0, -1, -1, 0, 0, -2]
    coefficient := ![0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true, true, false, false, false, true, false] }
  origin := ![.thetaLower 1, .thetaUpper 3, .corridorUpper 2 3, .triangle 15 2, .gapLower 1 5, .triangle 21 1, .triangle 32 1, .triangle 31 0, .triangle 12 0, .gapLower 0 3, .triangle 1 1, .gapLower 1 0]

-- Cycle fingerprint 308564eb3dd52db6cf5776dc0c7066b55a650518effca4a9fab0f0acb975f25a.
def localCycle00047 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 5 6, .distance 2 5, .distance 3 5, .distance 1 3, .distance 1 2, .distance 2 4, .distance 3 4, .distance 0 3, .theta 0, .zero]
    constant := ![0, 3, -1, -1, 0, -1, 0, -1, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, true, false, true, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 34 0, .triangle 30 0, .triangle 26 1, .triangle 20 0, .triangle 15 1, .triangle 16 0, .triangle 25 1, .triangle 9 0, .corridorLower 0 3, .thetaLower 0]

-- Cycle fingerprint 31c2206412be8aafa78cbeead9f69e0a25752ac8f89e8fe08edf9d5aa5eaecd2.
def localCycle00048 : Cycle where
  length := 6
  data := {
    node := ![.theta 4, .distance 3 4, .distance 1 3, .distance 3 5, .distance 5 6, .distance 4 5, .theta 4]
    constant := ![3, -1, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 19 0, .triangle 20 0, .triangle 33 0, .triangle 34 0, .corridorLower 4 5]

-- Cycle fingerprint 3299c5d4d5c46f9159d043ad5d6f42e79ca98c4f01cc018eaf61daa556d78b59.
def localCycle00049 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 3, .distance 2 3, .distance 2 4, .distance 4 6, .distance 3 4, .distance 4 5, .distance 0 4, .theta 0, .zero]
    constant := ![0, 3, 0, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false, false] }
  origin := ![.thetaUpper 3, .corridorUpper 2 3, .triangle 25 2, .triangle 29 0, .triangle 32 0, .triangle 31 0, .triangle 12 0, .corridorLower 0 4, .thetaLower 0]

-- Cycle fingerprint 330f50ac250701369fedcd689a701331cc1be3d3543e93ee768e2a1b57a20af6.
def localCycle00050 : Cycle where
  length := 6
  data := {
    node := ![.theta 4, .distance 2 4, .distance 1 4, .distance 4 5, .distance 3 4, .distance 4 6, .theta 4]
    constant := ![3, 0, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false] }
  origin := ![.corridorUpper 2 4, .triangle 16 2, .triangle 22 0, .triangle 31 0, .triangle 32 0, .corridorLower 4 6]

-- Cycle fingerprint 3329bc0c72ffd3ce4c1cfa12fef0fc0b53b547427012ef59d83bb2b3c09f6360.
def localCycle00051 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 3, .distance 1 2, .distance 2 5, .distance 3 5, .distance 5 6, .distance 4 5, .theta 4]
    constant := ![3, -1, -1, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 0, .triangle 15 0, .triangle 17 0, .triangle 26 1, .triangle 33 0, .triangle 34 0, .corridorLower 4 5]

-- Cycle fingerprint 336970a0422c9d2db1757044a1c2a328effe4d6d72de20ff50dc19fb24407a7e.
def localCycle00052 : Cycle where
  length := 8
  data := {
    node := ![.distance 4 5, .distance 0 4, .distance 0 3, .distance 0 1, .theta 1, .distance 1 3, .distance 3 6, .distance 3 4, .distance 4 5]
    constant := ![-1, 0, 0, -2, 2, -1, 0, -1]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![false, false, true, false, false, false, true, false] }
  origin := ![.triangle 12 0, .gapLower 0 3, .triangle 1 1, .gapLower 1 0, .gapLower 1 6, .triangle 21 0, .triangle 32 1, .triangle 31 0]

-- Cycle fingerprint 36588321b9c53ef53abaf9caed1921857b2570a0990ab63ce3ba4ccef51cca0f.
def localCycle00053 : Cycle where
  length := 13
  data := {
    node := ![.distance 0 3, .distance 0 2, .distance 0 1, .theta 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 1 3, .distance 1 4, .distance 1 5, .distance 5 6, .distance 3 5, .distance 0 3]
    constant := ![0, 0, -3, 0, 0, 0, 3, 0, 0, 0, -1, -1, -1]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, false, true, true, true, false, false, false] }
  origin := ![.gapLower 0 2, .triangle 0 1, .gapLower 1 0, .thetaNext 0, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 15 2, .triangle 19 2, .triangle 22 2, .triangle 24 0, .triangle 33 0, .triangle 10 0]

-- Cycle fingerprint 3cbc9a3929176f34e5df7f77f560ce02c61d838529f936284566ed3f10063471.
def localCycle00054 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 2 4, .distance 2 5, .distance 5 6, .distance 1 5, .distance 1 2, .distance 0 1]
    constant := ![-1, 0, 0, 3, 0, 0, -1, -1, -2, -2]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, false, false, false, false] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 25 2, .triangle 28 2, .triangle 30 0, .triangle 24 0, .gapLower 1 2, .gapLower 1 1]

-- Cycle fingerprint 3cec7ebf7a45414217e093be2806b1b3ebd0f5b0c20ffae5882a87c6eef29f34.
def localCycle00055 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 5, .distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 1 2, .distance 1 5]
    constant := ![-3, -1, 0, 0, 3, -1, 0]
    coefficient := ![0, 0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, false, false, false, true] }
  origin := ![.gapLower 1 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 15 0, .triangle 17 2]

-- Cycle fingerprint 3d82be007ce4f6ebb63ec9c7cda2e61df6f2976f9af6dc2353af28ecee29744c.
def localCycle00056 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 5, .distance 2 5, .distance 3 5, .distance 4 5, .distance 0 4, .distance 0 3, .theta 3, .distance 2 3, .distance 1 2, .distance 1 6, .distance 1 5]
    constant := ![0, 0, 0, -1, 0, 0, 3, -1, -2, -2]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![true, true, true, false, false, false, false, false, false, false] }
  origin := ![.triangle 17 1, .triangle 26 1, .triangle 31 1, .triangle 12 0, .gapLower 0 3, .gapLower 3 0, .corridorUpper 2 3, .triangle 15 0, .gapLower 1 3, .gapLower 1 2]

-- Cycle fingerprint 3dbe551122f8947322f827df98068866c44f1067cdba1c21cf383ef2ed742ac8.
def localCycle00057 : Cycle where
  length := 9
  data := {
    node := ![.distance 2 4, .distance 1 2, .distance 0 1, .theta 1, .theta 0, .zero, .theta 6, .distance 5 6, .distance 4 6, .distance 2 4]
    constant := ![-1, -2, -2, 0, 0, 0, 3, 0, -1]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, true, false, false, false, true, false] }
  origin := ![.triangle 16 0, .gapLower 1 1, .gapLower 1 0, .thetaNext 0, .thetaLower 0, .thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 29 0]

-- Cycle fingerprint 3e8b37d242c1553a9abb326db5823a6848ec8c0530b9b80506a83c0588417b40.
def localCycle00058 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 3, .distance 2 3, .distance 1 3, .distance 1 4, .distance 1 5, .distance 5 6, .distance 3 5, .distance 0 3, .distance 0 2, .distance 0 1, .theta 1, .zero]
    constant := ![0, 3, 0, 0, -2, -1, -1, -1, 0, 0, -2, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, false, false, true, false, false] }
  origin := ![.thetaUpper 3, .corridorUpper 2 3, .triangle 15 2, .triangle 19 2, .gapLower 1 4, .triangle 24 0, .triangle 33 0, .triangle 10 0, .gapLower 0 2, .triangle 0 1, .gapLower 1 0, .thetaLower 1]

-- Cycle fingerprint 402e27edfeb0f1f242e2a4393770ab59ac96d4f74fcd332894fc7d851a4abb52.
def localCycle00059 : Cycle where
  length := 14
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 2 3, .distance 2 6, .distance 1 2, .distance 2 5, .distance 3 5, .distance 4 5, .distance 0 4, .distance 0 3, .distance 0 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, -1, 0, -1, -1, 0, 0, -1, 0, 0, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, true, true, false, true, true, true, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 25 0, .triangle 27 2, .triangle 18 0, .triangle 17 0, .triangle 26 1, .triangle 31 1, .triangle 12 0, .triangle 9 1, .triangle 5 1, .triangle 0 1, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint 40545932fa7aa145e1e42b7fa600c16b40f51c3eb25a2bbddf8361857b0b1fbe.
def localCycle00060 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 2 3, .distance 2 4, .distance 4 6, .distance 3 4, .distance 1 3, .distance 3 5, .theta 3]
    constant := ![3, 0, -1, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 25 2, .triangle 29 0, .triangle 32 0, .triangle 19 0, .triangle 20 0, .corridorLower 3 5]

-- Cycle fingerprint 4218351976c71e9ae1459738fa2452122377e945c5a1b27e8b1c8e5b413b0176.
def localCycle00061 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 3, .distance 2 3, .distance 1 3, .distance 3 4, .distance 3 5, .distance 5 6, .distance 4 5, .distance 0 4, .theta 0, .zero]
    constant := ![0, 3, 0, -1, 0, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false, false, false, false] }
  origin := ![.thetaUpper 3, .corridorUpper 2 3, .triangle 15 2, .triangle 19 0, .triangle 31 2, .triangle 33 0, .triangle 34 0, .triangle 12 0, .corridorLower 0 4, .thetaLower 0]

-- Cycle fingerprint 422e94d799399ff2948aafa7b8dd9752ea8abdb81339e47059aa5c3528a5f83a.
def localCycle00062 : Cycle where
  length := 6
  data := {
    node := ![.distance 1 2, .distance 1 5, .distance 5 6, .distance 4 6, .distance 3 4, .distance 2 3, .distance 1 2]
    constant := ![0, 2, 0, -1, -1, -1]
    coefficient := ![0, 0, 0, 0, 0, 0]
    strict := ![true, true, true, false, false, false] }
  origin := ![.triangle 17 2, .gapUpper 5 5, .triangle 34 2, .triangle 32 0, .triangle 25 0, .triangle 15 0]

-- Cycle fingerprint 43ea03350251aa6ed34fe0aadba2df70daeb06de652353eb4b222563a45fef78.
def localCycle00063 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 3, .distance 3 5, .distance 1 3, .distance 3 6, .distance 4 6, .theta 4]
    constant := ![3, -1, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 0, .triangle 26 0, .triangle 20 0, .triangle 21 0, .triangle 32 1, .corridorLower 4 6]

-- Cycle fingerprint 43ea07541204ce2a0e6c0d412bb3cfc097a627bf69aeb123a944e50bcf71b232.
def localCycle00064 : Cycle where
  length := 13
  data := {
    node := ![.distance 2 3, .distance 1 3, .distance 1 6, .distance 1 4, .distance 3 4, .distance 4 5, .distance 0 4, .distance 0 3, .distance 0 2, .distance 0 1, .theta 1, .zero, .theta 3, .distance 2 3]
    constant := ![0, 0, -2, 0, -1, -1, 0, 0, 0, -2, 0, 0, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1]
    strict := ![true, true, false, true, false, false, false, true, true, false, false, false, false] }
  origin := ![.triangle 15 2, .triangle 21 2, .gapLower 1 4, .triangle 19 1, .triangle 31 0, .triangle 12 0, .gapLower 0 3, .triangle 5 1, .triangle 0 1, .gapLower 1 0, .thetaLower 1, .thetaUpper 3, .corridorUpper 2 3]

-- Cycle fingerprint 448df974faa3d439b38045ef21dae422072eba09c88373f2ace027a45067f301.
def localCycle00065 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 4, .distance 1 5, .distance 5 6, .distance 3 5, .theta 3, .distance 2 3, .distance 1 3, .distance 1 4]
    constant := ![-3, -1, -1, -1, 3, 0, 0]
    coefficient := ![0, 0, 0, 0, 1, 0, 0]
    strict := ![false, false, false, false, false, true, true] }
  origin := ![.gapLower 1 4, .triangle 24 0, .triangle 33 0, .corridorLower 3 5, .corridorUpper 2 3, .triangle 15 2, .triangle 19 2]

-- Cycle fingerprint 46232c1dc41517265ba0e4a38987861ad2dd459a0ec2b00dc4f0c5941ef957b5.
def localCycle00066 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 2 3, .distance 1 2, .distance 2 6, .distance 3 6, .distance 0 3, .distance 0 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, -1, -1, -1, 0, -1, 0, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, true, true, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 25 0, .triangle 15 0, .triangle 18 0, .triangle 27 1, .triangle 11 0, .triangle 5 1, .triangle 0 1, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint 46d1309cfe7c3446e8586c1bc8c745eb516923d056c17cd3068605d2346b518c.
def localCycle00067 : Cycle where
  length := 5
  data := {
    node := ![.theta 4, .distance 2 4, .distance 4 5, .distance 3 4, .distance 4 6, .theta 4]
    constant := ![3, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false] }
  origin := ![.corridorUpper 2 4, .triangle 28 0, .triangle 31 0, .triangle 32 0, .corridorLower 4 6]

-- Cycle fingerprint 4827cc05af1f0ae1a24a2f33cbf9b72621c08880ab3a08033f9ee40a501cad08.
def localCycle00068 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 5, .distance 1 2, .distance 0 1, .theta 1, .zero, .theta 3, .distance 2 3, .distance 1 3, .distance 1 4, .distance 1 6, .distance 1 5]
    constant := ![0, -1, -2, 0, 0, 3, 0, 0, -2, 0]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![true, false, false, false, false, false, true, true, false, true] }
  origin := ![.triangle 17 1, .triangle 0 0, .gapLower 1 0, .thetaLower 1, .thetaUpper 3, .corridorUpper 2 3, .triangle 15 2, .triangle 19 2, .gapLower 1 4, .triangle 24 1]

-- Cycle fingerprint 4a89c7c97e813c715424c4690d8ff6ebee9c45a314ca966efe9d426d24969f30.
def localCycle00069 : Cycle where
  length := 9
  data := {
    node := ![.distance 2 3, .distance 1 3, .distance 1 4, .distance 1 2, .distance 1 5, .distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3]
    constant := ![0, -2, 0, 0, -2, -1, 0, 0, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1, 1]
    strict := ![true, false, true, true, false, false, false, false, false] }
  origin := ![.triangle 15 2, .gapLower 1 5, .triangle 16 1, .triangle 17 2, .gapLower 1 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3]

-- Cycle fingerprint 4b1c76ee4ad2f564955c29719c21f4532bf9e196263e0a1ead8c76e54b038e61.
def localCycle00070 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 3, .distance 0 1, .theta 1, .zero, .theta 3, .distance 2 3, .distance 1 2, .distance 2 5, .distance 3 5, .distance 0 3]
    constant := ![0, -3, 0, 0, 3, -1, -1, 0, 0]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![true, false, false, false, false, false, false, true, false] }
  origin := ![.triangle 1 1, .gapLower 1 0, .thetaLower 1, .thetaUpper 3, .corridorUpper 2 3, .triangle 15 0, .triangle 17 0, .triangle 26 1, .gapLower 3 1]

-- Cycle fingerprint 4b2e0fd824bec015c44d475d0cfbae26ccebbf975a946d519dd5cd8aeb38cd73.
def localCycle00071 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 3, .distance 1 2, .distance 1 4, .distance 4 6, .distance 2 4, .distance 0 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, -1, -1, 0, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, false, false, false, true, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 0, .triangle 15 0, .triangle 16 2, .triangle 23 0, .triangle 29 0, .triangle 6 0, .triangle 0 1, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint 4b4c015c790f266e80bac5d57692ae7a7250183636597e43ac23e0c10437db6e.
def localCycle00072 : Cycle where
  length := 12
  data := {
    node := ![.theta 1, .zero, .theta 3, .distance 2 3, .distance 1 3, .distance 1 4, .distance 1 5, .distance 5 6, .distance 3 5, .distance 0 3, .distance 0 2, .distance 0 1, .theta 1]
    constant := ![0, 0, 3, 0, -2, 0, -1, -1, -1, 0, 0, -2]
    coefficient := ![0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true, false, false, false, false, true, false] }
  origin := ![.thetaLower 1, .thetaUpper 3, .corridorUpper 2 3, .triangle 15 2, .gapLower 1 5, .triangle 22 2, .triangle 24 0, .triangle 33 0, .triangle 10 0, .gapLower 0 2, .triangle 0 1, .gapLower 1 0]

-- Cycle fingerprint 4b83ee833fb570453d86298d3c43763f54bc50fe1b2e65e208d2fe5b79f31892.
def localCycle00073 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 3, .distance 1 4, .distance 1 5, .distance 5 6, .distance 3 5, .theta 3, .distance 2 3, .distance 1 3]
    constant := ![-2, 0, -1, -1, -1, 3, 0]
    coefficient := ![0, 0, 0, 0, 0, 1, 0]
    strict := ![false, true, false, false, false, false, true] }
  origin := ![.gapLower 1 5, .triangle 22 2, .triangle 24 0, .triangle 33 0, .corridorLower 3 5, .corridorUpper 2 3, .triangle 15 2]

-- Cycle fingerprint 4d9853aee088ca5d8f551c5672f8c6bb24026e60a336ff55444e3170bae292fa.
def localCycle00074 : Cycle where
  length := 16
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 3, .distance 1 2, .distance 2 6, .distance 3 6, .distance 4 6, .distance 5 6, .distance 0 5, .distance 0 4, .distance 0 3, .distance 0 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, -1, -1, -1, 0, 0, 0, -1, 0, 0, 0, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, true, true, true, false, true, true, true, true, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 0, .triangle 15 0, .triangle 18 0, .triangle 27 1, .triangle 32 1, .triangle 34 1, .triangle 14 0, .triangle 12 1, .triangle 9 1, .triangle 5 1, .triangle 0 1, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint 4f8cf8ab17969fbf0cde9cdb1804bfc21b9e20a8d8b6516f6c3de0e3b9f81659.
def localCycle00075 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .theta 1, .zero, .theta 3, .distance 2 3, .distance 1 3, .distance 1 4, .distance 1 5, .distance 1 6, .distance 1 2, .distance 0 1]
    constant := ![-2, 0, 0, 3, 0, 0, 0, 0, -2, -1]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, true, true, false, false] }
  origin := ![.gapLower 1 0, .thetaLower 1, .thetaUpper 3, .corridorUpper 2 3, .triangle 15 2, .triangle 19 2, .triangle 22 2, .triangle 24 2, .gapLower 1 2, .triangle 0 0]

-- Cycle fingerprint 50049a39a11dc73249b0d67c763ee42fbdd4a4059b5b4943143ea16e0550609d.
def localCycle00076 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 2 5, .distance 1 5, .distance 1 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, -1, 0, -2, -2, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 30 0, .triangle 17 2, .gapLower 1 2, .gapLower 1 1, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint 50855cc6b5e46ab056afc5b0337b89ff1f1aed722e8f2cfb1f6aeef7bef19b04.
def localCycle00077 : Cycle where
  length := 13
  data := {
    node := ![.zero, .theta 3, .distance 2 3, .distance 1 3, .distance 3 4, .distance 4 5, .distance 5 6, .distance 0 5, .distance 0 4, .distance 0 3, .distance 0 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, -1, -1, -1, -1, 0, 0, 0, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, true, true, true, true, false, false] }
  origin := ![.thetaUpper 3, .corridorUpper 2 3, .triangle 15 2, .triangle 19 0, .triangle 31 0, .triangle 34 0, .triangle 14 0, .triangle 12 1, .triangle 9 1, .triangle 5 1, .triangle 0 1, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint 50a76d2bb01e85381c09072e5797636937b53d1757e4a01afe5315bb1b9f464a.
def localCycle00078 : Cycle where
  length := 3
  data := {
    node := ![.distance 2 4, .distance 1 4, .distance 1 2, .distance 2 4]
    constant := ![0, -3, 2]
    coefficient := ![0, 0, 0]
    strict := ![false, false, true] }
  origin := ![.gapLower 4 5, .gapLower 1 4, .gapUpper 2 4]

-- Cycle fingerprint 50ff39a545a749802b010675704d52e6640d008e663e343f5ae2598647bc7414.
def localCycle00079 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 3, .distance 1 4, .distance 1 5, .distance 5 6, .distance 3 5, .theta 3, .distance 2 3, .distance 1 3]
    constant := ![-2, -2, -1, -1, -1, 3, 0]
    coefficient := ![0, 0, 0, 0, 0, 1, 0]
    strict := ![false, false, false, false, false, false, true] }
  origin := ![.gapLower 1 5, .gapLower 1 4, .triangle 24 0, .triangle 33 0, .corridorLower 3 5, .corridorUpper 2 3, .triangle 15 2]

-- Cycle fingerprint 51a840e6711260f4d07bb221acba27c68d815316b774b95ec8ee3bbb2517df2f.
def localCycle00080 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 2, .distance 2 6, .distance 5 6, .distance 4 5, .distance 3 4, .theta 3]
    constant := ![3, -1, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 0, .triangle 18 0, .triangle 30 1, .triangle 34 0, .triangle 31 0, .corridorLower 3 4]

-- Cycle fingerprint 542489924184c72d0053c6dcb621a0a4807e679e3111d431a85f79559acdedd1.
def localCycle00081 : Cycle where
  length := 9
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 2 3, .distance 1 2, .distance 2 4, .distance 4 6, .distance 3 6, .distance 5 6, .theta 5]
    constant := ![3, 0, -1, -1, -1, -1, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, true, true, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 26 0, .triangle 15 0, .triangle 16 0, .triangle 29 0, .triangle 32 2, .triangle 33 1, .corridorLower 5 6]

-- Cycle fingerprint 54ca3878f49c2bd843547607fa2cb44ba4a02d6a7a200b2f34d8fdb8385c02ca.
def localCycle00082 : Cycle where
  length := 9
  data := {
    node := ![.distance 2 3, .distance 1 3, .distance 1 6, .distance 1 5, .distance 1 2, .distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3]
    constant := ![0, -2, 0, -2, -1, -1, 0, 0, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1, 1]
    strict := ![true, false, true, false, false, false, false, false, false] }
  origin := ![.triangle 15 2, .gapLower 1 5, .triangle 24 1, .gapLower 1 2, .triangle 0 0, .corridorLower 0 1, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3]

-- Cycle fingerprint 54dfb730917bf502f663cd13eec79cd9027ba22b1ba6b0a8fbdab2137e987e22.
def localCycle00083 : Cycle where
  length := 11
  data := {
    node := ![.distance 4 5, .distance 3 4, .theta 3, .distance 2 3, .distance 2 4, .distance 4 6, .distance 3 6, .distance 1 3, .distance 1 4, .distance 1 2, .distance 2 5, .distance 4 5]
    constant := ![-1, -1, 3, 0, -1, 0, -1, 0, 0, -1, 0]
    coefficient := ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true, false, false, false, false, true] }
  origin := ![.triangle 31 0, .corridorLower 3 4, .corridorUpper 2 3, .triangle 25 2, .triangle 29 0, .triangle 32 2, .triangle 21 0, .gapLower 1 4, .gapLower 1 3, .triangle 17 0, .triangle 28 1]

-- Cycle fingerprint 553a0730f2d5a52e5899fe10cb6801c379396ef82b0a02b7a1a5714435fdb317.
def localCycle00084 : Cycle where
  length := 9
  data := {
    node := ![.distance 2 3, .distance 1 3, .distance 1 4, .distance 1 2, .distance 1 6, .distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3]
    constant := ![0, -2, 0, -2, -1, -1, 0, 0, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1, 1]
    strict := ![true, false, true, false, false, false, false, false, false] }
  origin := ![.triangle 15 2, .gapLower 1 5, .triangle 16 1, .gapLower 1 3, .triangle 4 0, .corridorLower 0 1, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3]

-- Cycle fingerprint 5665f0680b4c18da8e8e80fb05905da9c237343259a8371ef17c7db361a6e497.
def localCycle00085 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 2, .distance 0 1, .theta 0, .zero, .theta 6, .distance 5 6, .distance 2 5, .distance 1 2]
    constant := ![-3, -1, 0, 0, 3, -1, -1]
    coefficient := ![0, 0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 1 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 6, .corridorUpper 5 6, .triangle 30 0, .triangle 17 0]

-- Cycle fingerprint 56f0a65acce2930db37b81a6e774d6eebb9a1026e9e319f1bdea7a63a7835ad8.
def localCycle00086 : Cycle where
  length := 12
  data := {
    node := ![.distance 0 4, .distance 0 3, .theta 0, .zero, .theta 1, .distance 1 3, .distance 1 4, .distance 1 6, .distance 1 2, .distance 2 5, .distance 3 5, .distance 4 5, .distance 0 4]
    constant := ![0, -1, 0, 0, 2, 0, 0, -2, -1, 0, 0, -1]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, false, false, true, true, false] }
  origin := ![.gapLower 0 3, .corridorLower 0 3, .thetaLower 0, .thetaUpper 1, .gapLower 1 6, .triangle 19 2, .triangle 23 2, .gapLower 1 3, .triangle 17 0, .triangle 26 1, .triangle 31 1, .triangle 12 0]

-- Cycle fingerprint 58c0bf72641e937f6434982edf41c3ee1cd449926058e77bfbd5467fe99c091d.
def localCycle00087 : Cycle where
  length := 10
  data := {
    node := ![.distance 2 4, .distance 2 5, .distance 5 6, .distance 1 5, .distance 1 2, .distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 2 4]
    constant := ![0, -1, -1, 0, -2, -1, 0, 0, 3, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![true, false, false, false, false, false, false, false, false, true] }
  origin := ![.triangle 28 2, .triangle 30 0, .triangle 24 0, .gapLower 1 2, .gapLower 1 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 25 2]

-- Cycle fingerprint 58ed01546dd632d8476d9a550f27ed731f5288505ed392ecc900300374ea9c17.
def localCycle00088 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 4 6, .distance 2 4, .distance 2 3, .distance 1 2, .distance 2 5, .distance 3 5, .distance 4 5, .theta 4]
    constant := ![3, -1, -1, 0, -1, -1, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 32 0, .triangle 29 0, .gapLower 2 4, .triangle 15 0, .triangle 17 0, .triangle 26 1, .triangle 31 1, .corridorLower 4 5]

-- Cycle fingerprint 5984d6fa43d19e033670444fa0564bf849ca4806eec6a880766877f1afc8465d.
def localCycle00089 : Cycle where
  length := 3
  data := {
    node := ![.distance 2 6, .distance 1 6, .distance 1 2, .distance 2 6]
    constant := ![0, -3, 2]
    coefficient := ![0, 0, 0]
    strict := ![false, false, true] }
  origin := ![.gapLower 6 5, .gapLower 1 2, .gapUpper 2 2]

-- Cycle fingerprint 5a941e346afd4c95099e97495dae529c0f16e725bd4a1aea120c7eabe8f0e1fa.
def localCycle00090 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 6, .distance 3 6, .distance 3 4, .distance 4 5, .distance 0 4, .distance 0 3, .theta 0, .zero, .theta 1, .distance 1 3, .distance 1 6]
    constant := ![0, 0, -1, -1, 0, -1, 0, 0, 2, -2]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![true, true, false, false, false, false, false, false, false, false] }
  origin := ![.triangle 21 1, .triangle 32 1, .triangle 31 0, .triangle 12 0, .gapLower 0 3, .corridorLower 0 3, .thetaLower 0, .thetaUpper 1, .gapLower 1 6, .gapLower 1 5]

-- Cycle fingerprint 5c2d655195b4f3011be548e807215faedc557e62daabedd75936d3848221bdef.
def localCycle00091 : Cycle where
  length := 9
  data := {
    node := ![.distance 2 3, .distance 3 6, .distance 1 3, .distance 1 2, .distance 2 5, .distance 3 5, .distance 4 5, .theta 4, .distance 3 4, .distance 2 3]
    constant := ![-1, -1, 0, -1, 0, 0, -1, 3, -1]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1, 0]
    strict := ![false, false, false, false, true, true, false, false, false] }
  origin := ![.triangle 27 0, .triangle 21 0, .gapLower 1 3, .triangle 17 0, .triangle 26 1, .triangle 31 1, .corridorLower 4 5, .corridorUpper 3 4, .triangle 25 0]

-- Cycle fingerprint 5c5f31992d733c23ca381660d973decc6636788c5b155f75b6a4271c15453da7.
def localCycle00092 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 3, .distance 3 5, .distance 1 3, .distance 3 6, .distance 5 6, .distance 4 5, .theta 4]
    constant := ![3, -1, -1, -1, -1, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 0, .triangle 26 0, .triangle 20 0, .triangle 21 0, .triangle 33 1, .triangle 34 0, .corridorLower 4 5]

-- Cycle fingerprint 5fe643747ad66ead08adda477ade93c7976aaadce7576cbeaeae5dfb389202c0.
def localCycle00093 : Cycle where
  length := 3
  data := {
    node := ![.distance 5 6, .distance 1 6, .distance 1 5, .distance 5 6]
    constant := ![0, -3, 2]
    coefficient := ![0, 0, 0]
    strict := ![false, false, true] }
  origin := ![.gapLower 6 5, .gapLower 1 2, .gapUpper 5 5]

-- Cycle fingerprint 60131d6bd0d3767f084359b89ec45c391b3756f8ca0dfb243bcd87bb4ba30540.
def localCycle00094 : Cycle where
  length := 12
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 5, .distance 1 3, .distance 1 2, .distance 2 4, .distance 3 4, .distance 4 6, .distance 5 6, .distance 0 5, .distance 0 4, .distance 0 3, .theta 3]
    constant := ![3, -1, -1, 0, -1, 0, -1, 0, -1, 0, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, true, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 26 0, .triangle 20 0, .gapLower 1 4, .triangle 16 0, .triangle 25 1, .triangle 32 0, .triangle 34 1, .triangle 14 0, .gapLower 0 4, .gapLower 0 3, .gapLower 3 0]

-- Cycle fingerprint 606f07878008c78de53138b2c5e66e356665e1ea249dddbfa301a6223580e11c.
def localCycle00095 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 6, .distance 1 5, .distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 1 3, .distance 1 4, .distance 1 2, .distance 1 6]
    constant := ![0, -2, -1, 0, 0, 3, 0, 0, -2, 0]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![true, false, false, false, false, false, true, true, false, true] }
  origin := ![.triangle 24 1, .gapLower 1 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 15 2, .triangle 19 2, .gapLower 1 4, .triangle 18 2]

-- Cycle fingerprint 6091a3a394d934954ed3b0ce8e42dc24f5dd8930bcc8dcb45f347e1b8a54eec8.
def localCycle00096 : Cycle where
  length := 6
  data := {
    node := ![.distance 1 4, .distance 1 6, .distance 1 5, .distance 1 2, .theta 1, .distance 1 3, .distance 1 4]
    constant := ![0, -2, 0, -1, 2, 0]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![true, false, true, false, false, true] }
  origin := ![.triangle 23 2, .gapLower 1 3, .triangle 17 1, .corridorLower 1 2, .gapLower 1 6, .triangle 19 2]

-- Cycle fingerprint 60fe0a698a71cfa8e759256fc3a81c82b05a9dff174f1fd6bdc81d2ac6ede3dd.
def localCycle00097 : Cycle where
  length := 5
  data := {
    node := ![.distance 1 4, .distance 1 6, .distance 1 5, .theta 1, .distance 1 3, .distance 1 4]
    constant := ![0, -2, -1, 2, 0]
    coefficient := ![0, 0, 0, 1, 0]
    strict := ![true, false, false, false, true] }
  origin := ![.triangle 23 2, .gapLower 1 3, .corridorLower 1 5, .gapLower 1 6, .triangle 19 2]

-- Cycle fingerprint 6376bb8e69fd3ea53548a1dc185f4e49108a8fc9a114f62cf97226ea3afd2344.
def localCycle00098 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 2, .distance 2 5, .distance 4 5, .distance 5 6, .distance 3 5, .distance 3 4, .theta 3]
    constant := ![3, -1, -1, 0, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 0, .triangle 17 0, .triangle 28 1, .triangle 34 0, .triangle 33 0, .gapLower 3 2, .corridorLower 3 4]

-- Cycle fingerprint 649ff1b1af4735113c14c0f678b90b1efc9b6f068665f72f8a93f0e4ea088360.
def localCycle00099 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 5, .distance 1 3, .distance 3 4, .distance 4 6, .distance 5 6, .distance 0 5, .distance 0 3, .theta 3]
    constant := ![3, -1, -1, -1, -1, 0, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 26 0, .triangle 20 0, .triangle 19 0, .triangle 32 0, .triangle 34 1, .triangle 14 0, .triangle 10 1, .gapLower 3 0]

-- Cycle fingerprint 67e53915e54e3d52776c6f8ac42e43b7f2f0f95ed47429e764bab1af2139af8d.
def localCycle00100 : Cycle where
  length := 11
  data := {
    node := ![.distance 4 6, .distance 4 5, .distance 0 4, .distance 0 3, .theta 3, .distance 2 3, .distance 1 3, .distance 1 4, .distance 1 2, .distance 2 6, .distance 3 6, .distance 4 6]
    constant := ![0, -1, 0, 0, 3, 0, -2, -2, -1, 0, 0]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0]
    strict := ![true, false, false, false, false, true, false, false, false, true, true] }
  origin := ![.triangle 34 1, .triangle 12 0, .gapLower 0 3, .gapLower 3 0, .corridorUpper 2 3, .triangle 15 2, .gapLower 1 5, .gapLower 1 4, .triangle 18 0, .triangle 27 1, .triangle 32 1]

-- Cycle fingerprint 680c2751dd2fe91a73b09949334e398a1671f14aa2fb33d069de1e363d106990.
def localCycle00101 : Cycle where
  length := 3
  data := {
    node := ![.distance 2 5, .distance 1 5, .distance 1 2, .distance 2 5]
    constant := ![0, -3, 2]
    coefficient := ![0, 0, 0]
    strict := ![false, false, true] }
  origin := ![.gapLower 5 4, .gapLower 1 2, .gapUpper 2 2]

-- Cycle fingerprint 699aa5c564f49b60f2e6efc324f8df957a5e284d38798e9447d1027b4529f74c.
def localCycle00102 : Cycle where
  length := 11
  data := {
    node := ![.distance 3 5, .distance 4 5, .theta 4, .distance 3 4, .distance 2 3, .distance 3 6, .distance 4 6, .distance 1 4, .distance 1 3, .distance 1 2, .distance 2 5, .distance 3 5]
    constant := ![0, -1, 3, -1, -1, 0, -1, 0, 0, -1, 0]
    coefficient := ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![true, false, false, false, false, true, false, false, false, false, true] }
  origin := ![.triangle 31 1, .corridorLower 4 5, .corridorUpper 3 4, .triangle 25 0, .triangle 27 0, .triangle 32 1, .triangle 23 0, .gapLower 1 4, .gapLower 1 3, .triangle 17 0, .triangle 26 1]

-- Cycle fingerprint 6a1864bef040aee89c04787d7bb11d74c68e37fd3016cf98a071d9f28af07a1c.
def localCycle00103 : Cycle where
  length := 8
  data := {
    node := ![.theta 6, .distance 5 6, .distance 4 6, .distance 2 4, .distance 1 2, .distance 0 1, .theta 0, .zero, .theta 6]
    constant := ![3, 0, -1, -1, -3, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, false, false, false, false, false, false] }
  origin := ![.corridorUpper 5 6, .triangle 34 2, .triangle 29 0, .triangle 16 0, .gapLower 1 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 6]

-- Cycle fingerprint 6b5d3998cf5b0c6f5a3719daa42448e17af3e178fa8d75453046a61dff82d450.
def localCycle00104 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 3, .distance 2 3, .distance 3 4, .distance 3 5, .distance 1 3, .distance 3 6, .distance 5 6, .distance 4 5, .distance 0 4, .theta 0, .zero]
    constant := ![0, 3, -1, 0, -1, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, true, false, false, false, false] }
  origin := ![.thetaUpper 3, .corridorUpper 2 3, .triangle 25 0, .triangle 31 2, .triangle 20 0, .triangle 21 0, .triangle 33 1, .triangle 34 0, .triangle 12 0, .corridorLower 0 4, .thetaLower 0]

-- Cycle fingerprint 6c5866721fbece920ded5e0d5479ebdfb1502deda1d89717871b8377d15fa485.
def localCycle00105 : Cycle where
  length := 12
  data := {
    node := ![.distance 1 2, .distance 0 1, .theta 0, .zero, .theta 1, .distance 1 3, .distance 1 4, .distance 1 5, .distance 5 6, .distance 3 5, .distance 0 3, .distance 0 2, .distance 1 2]
    constant := ![-2, -1, 0, 0, 2, 0, 0, -1, -1, -1, 0, 2]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, false, false, false, false, true] }
  origin := ![.gapLower 1 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 1, .gapLower 1 6, .triangle 19 2, .triangle 22 2, .triangle 24 0, .triangle 33 0, .triangle 10 0, .gapLower 0 2, .gapUpper 2 1]

-- Cycle fingerprint 6dea7ea444f48258e26d9f0bb94f6101c67e9abb8d64c97011e3aa12cc307c15.
def localCycle00106 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 2, .distance 1 6, .distance 1 5, .distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 1 3, .distance 1 4, .distance 1 2]
    constant := ![0, -2, -1, -1, 0, 0, 3, 0, -2, 0]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![true, false, false, false, false, false, false, true, false, true] }
  origin := ![.triangle 18 2, .gapLower 1 2, .triangle 3 0, .corridorLower 0 1, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 15 2, .gapLower 1 5, .triangle 16 1]

-- Cycle fingerprint 71f651f5bc4408427f209611a3eff7779976199b1ad7d618dca9d99188b6dca2.
def localCycle00107 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 2 3, .distance 1 2, .distance 2 5, .distance 3 5, .distance 4 5, .distance 0 4, .theta 0, .zero]
    constant := ![0, 3, -1, -1, -1, 0, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 25 0, .triangle 15 0, .triangle 17 0, .triangle 26 1, .triangle 31 1, .triangle 12 0, .corridorLower 0 4, .thetaLower 0]

-- Cycle fingerprint 7277df3bc52ce3ba4fcf1c9e5cd17b8d6dcee7a43ddd21f19821a70bf3a265ae.
def localCycle00108 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 2, .distance 1 5, .distance 0 1, .theta 1, .zero, .theta 3, .distance 2 3, .distance 1 2]
    constant := ![-2, -1, -2, 0, 0, 3, -1]
    coefficient := ![0, 0, 0, 0, 1, 1, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 1 2, .triangle 3 0, .gapLower 1 0, .thetaLower 1, .thetaUpper 3, .corridorUpper 2 3, .triangle 15 0]

-- Cycle fingerprint 732be887b54820cd414fe70975a0b4894ce975bc003cba0bb17ec170d9b8c155.
def localCycle00109 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 2, .distance 2 5, .distance 5 6, .distance 4 5, .distance 3 4, .theta 3]
    constant := ![3, -1, -1, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 0, .triangle 17 0, .triangle 30 0, .triangle 34 0, .triangle 31 0, .corridorLower 3 4]

-- Cycle fingerprint 73b0c395d147baeccc69b351a8e5f8e1e51284c8d15b3a789a58202051852c3d.
def localCycle00110 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 3, .distance 2 3, .distance 1 2, .distance 2 6, .distance 3 6, .distance 3 5, .distance 0 3, .distance 0 1, .theta 1, .zero]
    constant := ![0, 3, -1, -1, 0, 0, 0, 0, -3, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, false, true, false, false] }
  origin := ![.thetaUpper 3, .corridorUpper 2 3, .triangle 15 0, .triangle 18 0, .triangle 27 1, .triangle 33 1, .gapLower 3 1, .triangle 1 1, .gapLower 1 0, .thetaLower 1]

-- Cycle fingerprint 74d999c561358f05f6445d9281a0047a111c8c1c208acfbd46e31c65201bcacc.
def localCycle00111 : Cycle where
  length := 8
  data := {
    node := ![.distance 4 5, .distance 0 4, .distance 0 3, .distance 0 1, .theta 1, .distance 1 3, .distance 3 6, .distance 3 4, .distance 4 5]
    constant := ![-1, 0, 0, 0, 1, -1, 0, -1]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![false, false, true, false, false, false, true, false] }
  origin := ![.triangle 12 0, .gapLower 0 3, .triangle 1 1, .gapLower 1 0, .gapLower 1 6, .triangle 21 0, .triangle 32 1, .triangle 31 0]

-- Cycle fingerprint 78cb965d5e06a03249d6f021f6e7509852226c8e04a1206432d773ddc7d83090.
def localCycle00112 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 1, .distance 1 3, .distance 3 4, .distance 4 6, .distance 4 5, .distance 0 4, .distance 0 3, .theta 0, .zero]
    constant := ![0, 2, -1, -1, 0, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, false, false] }
  origin := ![.thetaUpper 1, .gapLower 1 6, .triangle 19 0, .triangle 32 0, .triangle 34 1, .triangle 12 0, .gapLower 0 3, .corridorLower 0 3, .thetaLower 0]

-- Cycle fingerprint 79a1410eedb1a38bdb16973276c854616ae399911bb90829cadbd96dfb48e1ea.
def localCycle00113 : Cycle where
  length := 8
  data := {
    node := ![.distance 3 5, .theta 3, .distance 2 3, .distance 1 3, .distance 1 4, .distance 1 5, .distance 1 6, .distance 5 6, .distance 3 5]
    constant := ![-1, 3, 0, 0, -2, -2, 0, -1]
    coefficient := ![0, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, true, false] }
  origin := ![.corridorLower 3 5, .corridorUpper 2 3, .triangle 15 2, .triangle 19 2, .gapLower 1 4, .gapLower 1 3, .triangle 24 1, .triangle 33 0]

-- Cycle fingerprint 7e243d04fe835e8fab2662693f27a34f052d337120e445302aa900f4caa4d0d7.
def localCycle00114 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 2, .distance 1 6, .distance 1 5, .distance 0 1, .theta 1, .zero, .theta 3]
    constant := ![3, -1, 0, 0, -2, -2, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 1]
    strict := ![false, false, true, true, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 0, .triangle 18 2, .triangle 24 1, .gapLower 1 1, .gapLower 1 0, .thetaLower 1, .thetaUpper 3]

-- Cycle fingerprint 8030155a32f6a919eeca98d59cfa75ef631ef344c0e5f7c1bcf9a3321320eff3.
def localCycle00115 : Cycle where
  length := 6
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 2, .distance 2 5, .distance 4 5, .distance 3 4, .theta 3]
    constant := ![3, -1, -1, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 0, .triangle 17 0, .triangle 28 1, .triangle 31 0, .corridorLower 3 4]

-- Cycle fingerprint 837f1631132dbc9b28b8f8322a653c03ee336c0a9d4ab870ca0d94cfd30d0a1d.
def localCycle00116 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 6, .distance 1 3, .distance 3 4, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true] }
  origin := ![.corridorUpper 2 3, .triangle 27 0, .triangle 21 0, .triangle 19 0, .triangle 31 0, .corridorLower 4 5, .thetaNext 3]

-- Cycle fingerprint 83d3184bd2dff112cb402d98372e1b533ca9661d877963c4825ca62ae46823cd.
def localCycle00117 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 2, .distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 1 3, .distance 1 4, .distance 1 6, .distance 1 5, .distance 1 2]
    constant := ![-1, -1, 0, 0, 3, 0, 0, 0, -2, -2]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, true, false, false] }
  origin := ![.triangle 0 0, .corridorLower 0 1, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 15 2, .triangle 19 2, .triangle 23 2, .gapLower 1 3, .gapLower 1 2]

-- Cycle fingerprint 84cb98fceaed0995746b442e538f9e44c030bc32a41a57d217531e9f52cb6020.
def localCycle00118 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 4, .distance 1 3, .distance 1 5, .distance 5 6, .distance 3 5, .theta 3]
    constant := ![3, -1, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 25 0, .triangle 19 0, .triangle 20 2, .triangle 24 0, .triangle 33 0, .corridorLower 3 5]

-- Cycle fingerprint 84dbd38d61fc03413c7160d159f37e8710f21e5f47cdb1de76142dbd91d4d8cd.
def localCycle00119 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 3, .distance 1 4, .distance 1 6, .distance 1 2, .distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 1 3]
    constant := ![0, -2, 0, -2, -1, 0, 0, 3, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![true, false, true, false, false, false, false, false, true] }
  origin := ![.triangle 19 2, .gapLower 1 4, .triangle 18 1, .gapLower 1 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 15 2]

-- Cycle fingerprint 84f98c7c3aa06e3953c36d0e9f52257f4fce49ed88f64a0a8cfd6dc40334e314.
def localCycle00120 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 3, .distance 2 3, .distance 2 4, .distance 2 5, .distance 5 6, .distance 4 6, .distance 3 4, .distance 4 5, .distance 0 4, .theta 0, .zero]
    constant := ![0, 3, 0, 0, -1, 0, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, true, false, false, false, false, false] }
  origin := ![.thetaUpper 3, .corridorUpper 2 3, .triangle 25 2, .triangle 28 2, .triangle 30 0, .triangle 34 2, .triangle 32 0, .triangle 31 0, .triangle 12 0, .corridorLower 0 4, .thetaLower 0]

-- Cycle fingerprint 8671a6d07e97431c718efee40d5b8202b7f977b9ab9dea5bb44e424b54456331.
def localCycle00121 : Cycle where
  length := 7
  data := {
    node := ![.theta 6, .distance 5 6, .distance 2 5, .distance 1 2, .distance 0 1, .theta 0, .zero, .theta 6]
    constant := ![3, -1, -1, -2, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 1]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.corridorUpper 5 6, .triangle 30 0, .triangle 17 0, .gapLower 1 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 6]

-- Cycle fingerprint 86ec0aa2e1e6f72b37acb0eca1bb9c957bafddf26019074fcda5264395768dfe.
def localCycle00122 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 3, .distance 1 6, .distance 1 4, .distance 1 2, .distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 1 3]
    constant := ![0, -2, 0, -2, -1, 0, 0, 3, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![true, false, true, false, false, false, false, false, true] }
  origin := ![.triangle 21 2, .gapLower 1 4, .triangle 16 1, .gapLower 1 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 15 2]

-- Cycle fingerprint 872c4034a11fd3f27a385dfa500aa26e0f57b88b25e3cdc475bf6611e70f8e99.
def localCycle00123 : Cycle where
  length := 9
  data := {
    node := ![.distance 2 4, .distance 3 4, .theta 3, .distance 2 3, .distance 3 5, .distance 5 6, .distance 1 5, .distance 1 3, .distance 1 2, .distance 2 4]
    constant := ![0, -1, 3, -1, -1, -1, 0, 0, -1]
    coefficient := ![0, 0, 1, 0, 0, 0, 0, 0, 0]
    strict := ![true, false, false, false, false, false, false, true, false] }
  origin := ![.triangle 25 1, .corridorLower 3 4, .corridorUpper 2 3, .triangle 26 0, .triangle 33 0, .triangle 24 0, .gapLower 1 4, .triangle 15 1, .triangle 16 0]

-- Cycle fingerprint 877da0c1871409520fb15d361e0728e94bbbe58157ddec9da660f254efc7244e.
def localCycle00124 : Cycle where
  length := 11
  data := {
    node := ![.distance 4 5, .distance 0 4, .distance 0 3, .theta 3, .distance 2 3, .distance 1 3, .distance 1 4, .distance 1 6, .distance 1 2, .distance 2 5, .distance 3 5, .distance 4 5]
    constant := ![-1, 0, 0, 3, 0, 0, -2, -2, -1, 0, 0]
    coefficient := ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, false, false, false, true, true] }
  origin := ![.triangle 12 0, .gapLower 0 3, .gapLower 3 0, .corridorUpper 2 3, .triangle 15 2, .triangle 19 2, .gapLower 1 4, .gapLower 1 3, .triangle 17 0, .triangle 26 1, .triangle 31 1]

-- Cycle fingerprint 88e21bcfbf8eb6b6a0696bf476aec8b575ea2f09c1d91fbff6116883e0084813.
def localCycle00125 : Cycle where
  length := 9
  data := {
    node := ![.distance 4 6, .distance 1 4, .distance 1 5, .distance 1 2, .distance 0 1, .theta 1, .zero, .theta 6, .distance 5 6, .distance 4 6]
    constant := ![-1, -2, 0, -1, -2, 0, 0, 3, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![false, false, true, false, false, false, false, false, true] }
  origin := ![.triangle 23 0, .gapLower 1 3, .triangle 17 1, .triangle 0 0, .gapLower 1 0, .thetaLower 1, .thetaUpper 6, .corridorUpper 5 6, .triangle 34 2]

-- Cycle fingerprint 899c91acf03cd3ff1000f85d2d9302096b991811ef73598ffd0bc3b0087e3c25.
def localCycle00126 : Cycle where
  length := 12
  data := {
    node := ![.distance 3 4, .distance 4 5, .distance 0 4, .distance 0 3, .distance 0 1, .theta 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 1 3, .distance 3 6, .distance 3 4]
    constant := ![-1, -1, 0, 0, -3, 0, 0, 0, 3, 0, -1, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, true, false, true, false, false, false, true, false, true] }
  origin := ![.triangle 31 0, .triangle 12 0, .gapLower 0 3, .triangle 1 1, .gapLower 1 0, .thetaNext 0, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 15 2, .triangle 21 0, .triangle 32 1]

-- Cycle fingerprint 8a4654c2e8cf5a195eafe7821b0de879fbda65e15d8f2abae62f975e347606ee.
def localCycle00127 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 3, .distance 2 3, .distance 3 5, .distance 1 3, .distance 3 6, .distance 3 4, .distance 0 3, .distance 0 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, -1, -1, -1, 0, -1, 0, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, true, true, false, false] }
  origin := ![.thetaUpper 3, .corridorUpper 2 3, .triangle 26 0, .triangle 20 0, .triangle 21 0, .triangle 32 1, .triangle 9 0, .triangle 5 1, .triangle 0 1, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint 8aaa6095975f36095b3de42713356003a791a260090f966c2f5299ef17c6f22f.
def localCycle00128 : Cycle where
  length := 6
  data := {
    node := ![.theta 0, .zero, .theta 3, .distance 2 3, .distance 1 2, .distance 0 1, .theta 0]
    constant := ![0, 0, 3, -1, -3, -1]
    coefficient := ![0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 15 0, .gapLower 1 1, .corridorLower 0 1]

-- Cycle fingerprint 8b81a1f8a5ac33de67657f2a3c9b2df6e61cc9b3ca5a2bf9a771587733baf0d2.
def localCycle00129 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 2, .distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 1 3, .distance 1 4, .distance 1 6, .distance 1 5, .distance 1 2]
    constant := ![-2, -1, 0, 0, 3, 0, 0, 0, -2, 0]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, true, false, true] }
  origin := ![.gapLower 1 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 15 2, .triangle 19 2, .triangle 23 2, .gapLower 1 3, .triangle 17 1]

-- Cycle fingerprint 8c97446fbf6816699186a1a135ccddae118488799168def45401b2caa20a77bf.
def localCycle00130 : Cycle where
  length := 6
  data := {
    node := ![.distance 1 4, .distance 1 5, .distance 1 6, .distance 1 2, .theta 1, .distance 1 3, .distance 1 4]
    constant := ![0, 0, -2, -1, 2, 0]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![true, true, false, false, false, true] }
  origin := ![.triangle 22 2, .triangle 24 2, .gapLower 1 2, .corridorLower 1 2, .gapLower 1 6, .triangle 19 2]

-- Cycle fingerprint 8d1db3f8cb1e725614c432d574ab0e7cbbc13aff64d1ccc74db7ee22f09d9c3c.
def localCycle00131 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 3, .distance 3 5, .distance 4 5, .distance 1 4, .distance 4 6, .theta 4]
    constant := ![3, -1, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 0, .triangle 26 0, .triangle 31 1, .triangle 22 0, .triangle 23 0, .corridorLower 4 6]

-- Cycle fingerprint 8db15a8e06d56b462dc663d1d55d7ec904ce70d5b959f576036d7d092384330a.
def localCycle00132 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 3, .distance 1 2, .distance 1 5, .distance 5 6, .distance 4 5, .theta 4]
    constant := ![3, -1, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 0, .triangle 15 0, .triangle 17 2, .triangle 24 0, .triangle 34 0, .corridorLower 4 5]

-- Cycle fingerprint 8e530950249fd7b8c9e3296a14ff730eddda42ca653a4466decc11734e5dc794.
def localCycle00133 : Cycle where
  length := 3
  data := {
    node := ![.distance 2 5, .distance 1 2, .distance 1 5, .distance 2 5]
    constant := ![2, -3, 0]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.gapUpper 2 2, .gapLower 1 2, .triangle 17 1]

-- Cycle fingerprint 8ff0c869e7f13daa9dde43c93ba16b9a5d67308f0fdcb562f74bd0816fcb4dc4.
def localCycle00134 : Cycle where
  length := 13
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 3, .distance 1 2, .distance 2 6, .distance 4 6, .distance 3 4, .distance 0 3, .distance 0 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, -1, -1, -1, 0, -1, -1, 0, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, true, false, false, true, true, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 0, .triangle 15 0, .triangle 18 0, .triangle 29 1, .triangle 32 0, .triangle 9 0, .triangle 5 1, .triangle 0 1, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint 91665d6801168d5eb12b18a33b4949b8e471f2cafb85040071b347a796a9fd98.
def localCycle00135 : Cycle where
  length := 8
  data := {
    node := ![.theta 0, .zero, .theta 3, .distance 2 3, .distance 1 3, .distance 1 4, .distance 1 6, .distance 0 1, .theta 0]
    constant := ![0, 0, 3, 0, -2, -2, -1, -1]
    coefficient := ![0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, false] }
  origin := ![.thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 15 2, .gapLower 1 5, .gapLower 1 4, .triangle 4 0, .corridorLower 0 1]

-- Cycle fingerprint 91675553f08df58c66e78dd48e6c462a85367ef7cc2105c9712033a56667ded6.
def localCycle00136 : Cycle where
  length := 9
  data := {
    node := ![.distance 2 3, .distance 1 3, .distance 1 4, .distance 1 6, .distance 1 5, .distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3]
    constant := ![0, -2, 0, -2, -1, -1, 0, 0, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1, 1]
    strict := ![true, false, true, false, false, false, false, false, false] }
  origin := ![.triangle 15 2, .gapLower 1 5, .triangle 23 2, .gapLower 1 3, .triangle 3 0, .corridorLower 0 1, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3]

-- Cycle fingerprint 91bc19565844ade036fd4e27b8758bde9fca52ea0e67379a95afb45bc7b71ce9.
def localCycle00137 : Cycle where
  length := 8
  data := {
    node := ![.distance 5 6, .distance 4 6, .distance 1 4, .distance 1 5, .distance 0 1, .theta 0, .zero, .theta 6, .distance 5 6]
    constant := ![0, -1, -2, -1, -1, 0, 0, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 1]
    strict := ![true, false, false, false, false, false, false, false] }
  origin := ![.triangle 34 2, .triangle 23 0, .gapLower 1 3, .triangle 3 0, .corridorLower 0 1, .thetaLower 0, .thetaUpper 6, .corridorUpper 5 6]

-- Cycle fingerprint 935a4de0c9403b56f78e905e2b18be9415550046d717c6d0318374af740a9b7f.
def localCycle00138 : Cycle where
  length := 5
  data := {
    node := ![.distance 1 2, .distance 1 4, .distance 4 6, .distance 3 6, .distance 2 3, .distance 1 2]
    constant := ![0, 2, 0, -1, -1]
    coefficient := ![0, 0, 0, 0, 0]
    strict := ![true, true, true, false, false] }
  origin := ![.triangle 16 2, .gapUpper 4 4, .triangle 32 2, .triangle 27 0, .triangle 15 0]

-- Cycle fingerprint 94071fbb62ffb0fb71d1a860499e4f7c7356e266e168f1e4456312c9a07dfbae.
def localCycle00139 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 2, .distance 2 5, .distance 3 5, .distance 5 6, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, -1, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, true] }
  origin := ![.corridorUpper 2 3, .triangle 15 0, .triangle 17 0, .triangle 26 1, .triangle 33 0, .triangle 34 0, .corridorLower 4 5, .thetaNext 3]

-- Cycle fingerprint 940fececf62801a5104d061eb246fa0add861553a0abcc72f2986f8b9fddda6b.
def localCycle00140 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 4, .distance 1 5, .distance 5 6, .distance 3 5, .distance 0 3, .distance 0 2, .theta 0, .zero, .theta 1, .distance 1 3, .distance 1 4]
    constant := ![0, -1, -1, -1, 0, -1, 0, 0, 2, -2]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![true, false, false, false, false, false, false, false, false, false] }
  origin := ![.triangle 22 2, .triangle 24 0, .triangle 33 0, .triangle 10 0, .gapLower 0 2, .corridorLower 0 2, .thetaLower 0, .thetaUpper 1, .gapLower 1 6, .gapLower 1 5]

-- Cycle fingerprint 95d67239f08f5b0659a31cb606e706d941926e9537c12b18b471a55ba3d8b1bc.
def localCycle00141 : Cycle where
  length := 6
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 2, .distance 2 5, .distance 5 6, .distance 3 5, .theta 3]
    constant := ![3, -1, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 0, .triangle 17 0, .triangle 30 0, .triangle 33 0, .corridorLower 3 5]

-- Cycle fingerprint 97038eea04441670f91e88eb7f3a9ae5eb5285c159e22dc4bcaef419332937c3.
def localCycle00142 : Cycle where
  length := 10
  data := {
    node := ![.theta 0, .zero, .theta 3, .distance 2 3, .distance 2 4, .distance 2 5, .distance 5 6, .distance 1 5, .distance 1 2, .distance 0 1, .theta 0]
    constant := ![0, 0, 3, 0, 0, -1, -1, 0, -3, -1]
    coefficient := ![0, 1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false, false, false, false, false] }
  origin := ![.thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 25 2, .triangle 28 2, .triangle 30 0, .triangle 24 0, .gapLower 1 2, .gapLower 1 1, .corridorLower 0 1]

-- Cycle fingerprint 97150b42460e273a2807962a16914b6f34cc702ff361e8eaf6ef2719966a72c6.
def localCycle00143 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 4, .distance 1 5, .distance 5 6, .distance 3 5, .distance 0 3, .distance 0 2, .theta 0, .zero, .theta 1, .distance 1 3, .distance 1 4]
    constant := ![-2, -1, -1, -1, 0, -1, 0, 0, 2, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![false, false, false, false, false, false, false, false, false, true] }
  origin := ![.gapLower 1 4, .triangle 24 0, .triangle 33 0, .triangle 10 0, .gapLower 0 2, .corridorLower 0 2, .thetaLower 0, .thetaUpper 1, .gapLower 1 6, .triangle 19 2]

-- Cycle fingerprint 972cd3605e0548e1f50ee717ef8005b9d34b08925b1a4c865265d671e7172059.
def localCycle00144 : Cycle where
  length := 14
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 2 3, .distance 1 2, .distance 2 5, .distance 4 5, .distance 3 4, .distance 0 3, .distance 0 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, 0, -1, -1, -1, 0, -1, -1, 0, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, true, false, false, true, true, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 27 0, .triangle 15 0, .triangle 17 0, .triangle 28 1, .triangle 31 0, .triangle 9 0, .triangle 5 1, .triangle 0 1, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint 9776a3a6e1297caaa9d934d782bc3a7a5dd0c22a359667846fea6ab6b50c5fb2.
def localCycle00145 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 3, .distance 2 3, .distance 1 3, .distance 1 4, .distance 1 6, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, 0, -3, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, false] }
  origin := ![.thetaUpper 3, .corridorUpper 2 3, .triangle 15 2, .triangle 19 2, .gapLower 1 4, .triangle 4 0, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint 97820f4e3286331e9c2cc0ec7fba136ef82e3eafe79d070cc5832694b45dccd8.
def localCycle00146 : Cycle where
  length := 4
  data := {
    node := ![.distance 1 5, .distance 1 2, .distance 2 6, .distance 5 6, .distance 1 5]
    constant := ![-2, 2, 0, -1]
    coefficient := ![0, 0, 0, 0]
    strict := ![false, true, false, false] }
  origin := ![.gapLower 1 2, .gapUpper 2 2, .gapLower 6 5, .triangle 24 0]

-- Cycle fingerprint 97a97a494518cf00afc68ab675d0ef61978b7a75bdfea85fbdef98baba6c2f09.
def localCycle00147 : Cycle where
  length := 9
  data := {
    node := ![.distance 4 6, .distance 1 4, .distance 1 5, .distance 1 2, .distance 0 1, .theta 0, .zero, .theta 6, .distance 5 6, .distance 4 6]
    constant := ![-1, -2, -2, -1, -1, 0, 0, 3, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![false, false, false, false, false, false, false, false, true] }
  origin := ![.triangle 23 0, .gapLower 1 3, .gapLower 1 2, .triangle 0 0, .corridorLower 0 1, .thetaLower 0, .thetaUpper 6, .corridorUpper 5 6, .triangle 34 2]

-- Cycle fingerprint 98cdaeebdb6ff6b0dbfb0097769dae225af628f414869568d6de022d3c51c7cc.
def localCycle00148 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 1 3, .distance 1 4, .distance 1 5, .distance 1 6, .distance 1 2, .distance 0 1]
    constant := ![-1, 0, 0, 3, 0, 0, 0, 0, -2, -2]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, true, true, false, false] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 15 2, .triangle 19 2, .triangle 22 2, .triangle 24 2, .gapLower 1 2, .gapLower 1 1]

-- Cycle fingerprint 99600781ac5bfbaaca0de997ea3248593cdc3d5bc0054e27c4247dabbbf0ea23.
def localCycle00149 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 2, .distance 2 6, .distance 5 6, .distance 4 6, .distance 3 4, .theta 3]
    constant := ![3, -1, -1, 0, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 0, .triangle 18 0, .triangle 30 1, .triangle 34 2, .triangle 32 0, .corridorLower 3 4]

-- Cycle fingerprint 9a7ebf9198555754c79c448cf2236a3cf9461bfb1ff6234e38c6358fb53786d5.
def localCycle00150 : Cycle where
  length := 8
  data := {
    node := ![.distance 5 6, .distance 3 5, .theta 3, .distance 2 3, .distance 1 3, .distance 1 4, .distance 1 5, .distance 1 6, .distance 5 6]
    constant := ![-1, -1, 3, 0, -2, 0, -2, 0]
    coefficient := ![0, 0, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true, false, true] }
  origin := ![.triangle 33 0, .corridorLower 3 5, .corridorUpper 2 3, .triangle 15 2, .gapLower 1 5, .triangle 22 2, .gapLower 1 3, .triangle 24 1]

-- Cycle fingerprint 9abe7b7fc1b5a39596a9f7b21e6720a8f50c12b59ed1a59ae6917a05ec80b277.
def localCycle00151 : Cycle where
  length := 7
  data := {
    node := ![.theta 1, .distance 1 3, .distance 1 4, .distance 1 6, .distance 0 1, .theta 0, .zero, .theta 1]
    constant := ![2, 0, -2, -1, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, false, false, false, false, false] }
  origin := ![.gapLower 1 6, .triangle 19 2, .gapLower 1 4, .triangle 4 0, .corridorLower 0 1, .thetaLower 0, .thetaUpper 1]

-- Cycle fingerprint 9cf73b6b1ff487ef9b6c1756b14f1f3863bfcf8463087fc6bddaaf2bc7f44162.
def localCycle00152 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 2, .distance 1 5, .distance 5 6, .distance 4 5, .distance 3 4, .theta 3]
    constant := ![3, -1, 0, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 0, .triangle 17 2, .triangle 24 0, .triangle 34 0, .triangle 31 0, .corridorLower 3 4]

-- Cycle fingerprint 9db371cab4a4b5806135a8d7d9356cc82537d42cc6eda256acc85efe33bc0695.
def localCycle00153 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 3, .distance 1 6, .distance 1 4, .distance 3 4, .distance 4 5, .distance 0 4, .distance 0 3, .theta 3, .distance 2 3, .distance 1 3]
    constant := ![0, -3, 0, -1, -1, 0, 0, 3, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1, 0]
    strict := ![true, false, true, false, false, false, false, false, true] }
  origin := ![.triangle 21 2, .gapLower 1 4, .triangle 19 1, .triangle 31 0, .triangle 12 0, .gapLower 0 3, .gapLower 3 0, .corridorUpper 2 3, .triangle 15 2]

-- Cycle fingerprint 9e00f87e0c719fdcb0a4b43b2f91c930b50ab72e081ff6a74b32cbfb765257e4.
def localCycle00154 : Cycle where
  length := 14
  data := {
    node := ![.zero, .theta 3, .distance 2 3, .distance 2 4, .distance 2 5, .distance 5 6, .distance 4 6, .distance 3 4, .distance 4 5, .distance 0 4, .distance 0 3, .distance 0 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, 0, -1, 0, -1, -1, -1, 0, 0, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, true, false, false, false, true, true, true, false, false] }
  origin := ![.thetaUpper 3, .corridorUpper 2 3, .triangle 25 2, .triangle 28 2, .triangle 30 0, .triangle 34 2, .triangle 32 0, .triangle 31 0, .triangle 12 0, .triangle 9 1, .triangle 5 1, .triangle 0 1, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint 9f5af8f586b7e6b0122a506dd87a70aff5a9f77dfe5f78715eecca094fd8e3e4.
def localCycle00155 : Cycle where
  length := 12
  data := {
    node := ![.distance 5 6, .distance 3 5, .distance 0 3, .distance 0 2, .distance 0 1, .theta 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 2 4, .distance 2 5, .distance 5 6]
    constant := ![-1, -1, 0, 0, -3, 0, 0, 0, 3, 0, 0, -1]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, true, false, true, false, false, false, true, true, false] }
  origin := ![.triangle 33 0, .triangle 10 0, .gapLower 0 2, .triangle 0 1, .gapLower 1 0, .thetaNext 0, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 25 2, .triangle 28 2, .triangle 30 0]

-- Cycle fingerprint 9fe633bb1610c334355bc2d9cbd89bf49344d50f13a163ed4fedca86e04b6779.
def localCycle00156 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .theta 1, .distance 1 3, .distance 1 4, .distance 1 5, .distance 5 6, .distance 3 5, .distance 0 3, .distance 0 2, .distance 0 1]
    constant := ![-2, 2, 0, 0, -1, -1, -1, 0, 0]
    coefficient := ![0, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, false, true] }
  origin := ![.gapLower 1 0, .gapLower 1 6, .triangle 19 2, .triangle 22 2, .triangle 24 0, .triangle 33 0, .triangle 10 0, .gapLower 0 2, .triangle 0 1]

-- Cycle fingerprint a113fadaacfd80466384767c52860321ee23596486247dfc2453fea8d8365dae.
def localCycle00157 : Cycle where
  length := 10
  data := {
    node := ![.distance 4 6, .distance 4 5, .distance 0 4, .distance 0 3, .theta 3, .distance 2 3, .distance 1 2, .distance 1 6, .distance 2 6, .distance 3 6, .distance 4 6]
    constant := ![0, -1, 0, 0, 3, -1, -2, 0, 0, 0]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0]
    strict := ![true, false, false, false, false, false, false, true, true, true] }
  origin := ![.triangle 34 1, .triangle 12 0, .gapLower 0 3, .gapLower 3 0, .corridorUpper 2 3, .triangle 15 0, .gapLower 1 3, .triangle 18 1, .triangle 27 1, .triangle 32 1]

-- Cycle fingerprint a215c65b65953295e2a21b3cfd44fbaf7131982fdefab803fe7cd41e952d31d4.
def localCycle00158 : Cycle where
  length := 15
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 2 4, .distance 1 2, .distance 2 6, .distance 3 6, .distance 4 6, .distance 5 6, .distance 0 5, .distance 0 4, .distance 0 3, .distance 0 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, -1, -1, -1, 0, 0, 0, -1, 0, 0, 0, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, true, false, true, true, true, true, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 28 0, .triangle 16 0, .triangle 18 0, .triangle 27 1, .triangle 32 1, .triangle 34 1, .triangle 14 0, .triangle 12 1, .triangle 9 1, .triangle 5 1, .triangle 0 1, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint a3dfa395fef333ee966e8859e56aef1977d6ee911e5155580c45bd9aca19fe27.
def localCycle00159 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 2, .distance 1 5, .distance 5 6, .distance 4 6, .distance 3 4, .theta 3]
    constant := ![3, -1, 0, -1, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 0, .triangle 17 2, .triangle 24 0, .triangle 34 2, .triangle 32 0, .corridorLower 3 4]

-- Cycle fingerprint a6a5b71465b14eb58dec899def8494b3a655d15e78991a286706d890daaa182b.
def localCycle00160 : Cycle where
  length := 14
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 2 4, .distance 1 2, .distance 2 5, .distance 3 5, .distance 4 5, .distance 0 4, .distance 0 3, .distance 0 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, -1, -1, -1, 0, 0, -1, 0, 0, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, true, true, false, true, true, true, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 29 0, .triangle 16 0, .triangle 17 0, .triangle 26 1, .triangle 31 1, .triangle 12 0, .triangle 9 1, .triangle 5 1, .triangle 0 1, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint a7077d78a5025766d9ec3e2935c19fa33ce4e88b06e15b459297023cfb4d6007.
def localCycle00161 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 3, .distance 2 3, .distance 3 4, .distance 3 6, .distance 1 3, .distance 3 5, .distance 4 5, .distance 0 4, .theta 0, .zero]
    constant := ![0, 3, -1, 0, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, true, false, false, false] }
  origin := ![.thetaUpper 3, .corridorUpper 2 3, .triangle 25 0, .triangle 32 2, .triangle 21 0, .triangle 20 0, .triangle 31 1, .triangle 12 0, .corridorLower 0 4, .thetaLower 0]

-- Cycle fingerprint a81453e66f0252b473485775871296cf58b142d220b168cfbd0e87d982e60d52.
def localCycle00162 : Cycle where
  length := 11
  data := {
    node := ![.distance 4 5, .distance 0 4, .distance 0 3, .theta 3, .distance 2 3, .distance 1 3, .distance 1 4, .distance 1 6, .distance 1 2, .distance 2 5, .distance 3 5, .distance 4 5]
    constant := ![-1, 0, 0, 3, 0, 0, -3, 0, -1, 0, 0]
    coefficient := ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, false, true, false, true, true] }
  origin := ![.triangle 12 0, .gapLower 0 3, .gapLower 3 0, .corridorUpper 2 3, .triangle 15 2, .triangle 19 2, .gapLower 1 4, .triangle 18 1, .triangle 17 0, .triangle 26 1, .triangle 31 1]

-- Cycle fingerprint ab18c40d4cb6e2eaaaca33ecd6603fa6da4386d36ec65f465d4ec3ca945e2d37.
def localCycle00163 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 2, .distance 1 6, .distance 0 1, .theta 1, .zero, .theta 3, .distance 2 3, .distance 1 2]
    constant := ![-2, -1, -2, 0, 0, 3, -1]
    coefficient := ![0, 0, 0, 0, 1, 1, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 1 3, .triangle 4 0, .gapLower 1 0, .thetaLower 1, .thetaUpper 3, .corridorUpper 2 3, .triangle 15 0]

-- Cycle fingerprint ad2f76d02617eadb6fc5ae9b1ecc129ecee73c14b94bfa26dd0b50762b098b04.
def localCycle00164 : Cycle where
  length := 6
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 2, .distance 2 4, .distance 4 6, .distance 3 4, .theta 3]
    constant := ![3, -1, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 0, .triangle 16 0, .triangle 29 0, .triangle 32 0, .corridorLower 3 4]

-- Cycle fingerprint aff4408f9839f9c97e883716874684d6e68c0e01954c486a33254bf8e0936353.
def localCycle00165 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 6, .distance 1 4, .distance 3 4, .distance 4 5, .distance 0 4, .distance 0 3, .theta 0, .zero, .theta 1, .distance 1 3, .distance 1 6]
    constant := ![-2, 0, -1, -1, 0, -1, 0, 0, 2, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![false, true, false, false, false, false, false, false, false, true] }
  origin := ![.gapLower 1 4, .triangle 19 1, .triangle 31 0, .triangle 12 0, .gapLower 0 3, .corridorLower 0 3, .thetaLower 0, .thetaUpper 1, .gapLower 1 6, .triangle 21 2]

-- Cycle fingerprint b04f30e924796800b762ca0f6ef99f8445917e0b8da037e22c23345cc52cdc3b.
def localCycle00166 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 6, .distance 5 6, .distance 1 5, .distance 1 2, .distance 0 1]
    constant := ![-1, 0, 0, 3, -1, -2, -1]
    coefficient := ![0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 6, .corridorUpper 5 6, .triangle 24 0, .gapLower 1 2, .triangle 0 0]

-- Cycle fingerprint b1339a3a1adb22c9abeb5ea0834367f6b612a662fb638271ddb2597ef490db88.
def localCycle00167 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 3, .distance 2 3, .distance 1 3, .distance 1 4, .distance 1 5, .distance 5 6, .distance 4 6, .distance 3 4, .distance 4 5, .distance 0 4, .theta 0, .zero]
    constant := ![0, 3, 0, 0, 0, -1, 0, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, true, false, true, false, false, false, false, false] }
  origin := ![.thetaUpper 3, .corridorUpper 2 3, .triangle 15 2, .triangle 19 2, .triangle 22 2, .triangle 24 0, .triangle 34 2, .triangle 32 0, .triangle 31 0, .triangle 12 0, .corridorLower 0 4, .thetaLower 0]

-- Cycle fingerprint b180d9b9fcc0b656e536a37daf2c314726a6d60d59d238a6b13f49eb8b60c5cc.
def localCycle00168 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 3, .distance 2 3, .distance 2 4, .distance 4 6, .distance 3 4, .distance 4 5, .distance 0 4, .distance 0 3, .distance 0 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, -1, -1, -1, -1, 0, 0, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, true, true, true, false, false] }
  origin := ![.thetaUpper 3, .corridorUpper 2 3, .triangle 25 2, .triangle 29 0, .triangle 32 0, .triangle 31 0, .triangle 12 0, .triangle 9 1, .triangle 5 1, .triangle 0 1, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint b1c4361e68280412accf5dd1c73fbdf435a2af5f8a74fbfb9aff34450c12c8f5.
def localCycle00169 : Cycle where
  length := 12
  data := {
    node := ![.theta 1, .zero, .theta 3, .distance 2 3, .distance 1 3, .distance 1 4, .distance 3 4, .distance 4 6, .distance 4 5, .distance 0 4, .distance 0 3, .distance 0 1, .theta 1]
    constant := ![0, 0, 3, 0, -2, 0, -1, 0, -1, 0, 0, -2]
    coefficient := ![0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true, false, true, false, false, true, false] }
  origin := ![.thetaLower 1, .thetaUpper 3, .corridorUpper 2 3, .triangle 15 2, .gapLower 1 5, .triangle 19 1, .triangle 32 0, .triangle 34 1, .triangle 12 0, .gapLower 0 3, .triangle 1 1, .gapLower 1 0]

-- Cycle fingerprint b23e7fa290e3e7db60a02fe417a9f0f15b7c402c7531de2113cc8926365e9239.
def localCycle00170 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 4, .distance 1 3, .distance 3 5, .distance 5 6, .distance 4 5, .distance 0 4, .distance 0 3, .theta 3]
    constant := ![3, -1, -1, -1, -1, -1, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 25 0, .triangle 19 0, .triangle 20 0, .triangle 33 0, .triangle 34 0, .triangle 12 0, .triangle 9 1, .gapLower 3 0]

-- Cycle fingerprint b296906f5e4273d2835b3d50f5c47a35782bfdd1b7c0ace9f8a0de6c1684a1da.
def localCycle00171 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 2 5, .distance 1 2, .distance 0 1, .theta 1, .theta 0, .zero]
    constant := ![0, 3, -1, -1, -2, -2, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 30 0, .triangle 17 0, .gapLower 1 1, .gapLower 1 0, .thetaNext 0, .thetaLower 0]

-- Cycle fingerprint b3d41b171d64f688404ec3728ddc23f8ae2aaeee215eca1d0b73ad1be07eaafc.
def localCycle00172 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 2 4, .distance 4 5, .distance 3 5, .distance 1 3, .distance 3 4, .distance 4 6, .theta 4]
    constant := ![3, -1, 0, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false] }
  origin := ![.corridorUpper 2 4, .triangle 28 0, .triangle 31 2, .triangle 20 0, .triangle 19 0, .triangle 32 0, .corridorLower 4 6]

-- Cycle fingerprint b464592f2c9f6688abde1e561f15edac777317bcd9f37e3dbcc6f457e615a1a9.
def localCycle00173 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 2, .distance 0 1, .theta 0, .zero, .theta 6, .distance 5 6, .distance 4 6, .distance 1 4, .distance 1 5, .distance 1 2]
    constant := ![-1, -1, 0, 0, 3, 0, -1, 0, -2]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, true, false] }
  origin := ![.triangle 0 0, .corridorLower 0 1, .thetaLower 0, .thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 23 0, .triangle 22 2, .gapLower 1 2]

-- Cycle fingerprint b5d0a64c07e084aea9880e039b347d1428256ab36fc09d25e99479c274219526.
def localCycle00174 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 3, .distance 1 2, .distance 2 5, .distance 5 6, .distance 4 5, .theta 4]
    constant := ![3, -1, -1, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 0, .triangle 15 0, .triangle 17 0, .triangle 30 0, .triangle 34 0, .corridorLower 4 5]

-- Cycle fingerprint b76f84521ac68ecfe4d9e3f851ffae69e215ebf00bd805f49893fb970a55571e.
def localCycle00175 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 3, .distance 1 2, .distance 2 6, .distance 3 6, .distance 5 6, .distance 4 5, .theta 4]
    constant := ![3, -1, -1, -1, 0, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 0, .triangle 15 0, .triangle 18 0, .triangle 27 1, .triangle 33 1, .triangle 34 0, .corridorLower 4 5]

-- Cycle fingerprint b871d4843f32e54322344ba6f301343b02a1a3f93176e40d9c91d9f8253c50db.
def localCycle00176 : Cycle where
  length := 10
  data := {
    node := ![.distance 4 5, .distance 0 4, .distance 0 3, .theta 3, .distance 2 3, .distance 1 2, .distance 1 6, .distance 1 5, .distance 2 5, .distance 3 5, .distance 4 5]
    constant := ![-1, 0, 0, 3, -1, 0, -2, 0, 0, 0]
    coefficient := ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, true, true, true] }
  origin := ![.triangle 12 0, .gapLower 0 3, .gapLower 3 0, .corridorUpper 2 3, .triangle 15 0, .triangle 18 2, .gapLower 1 2, .triangle 17 1, .triangle 26 1, .triangle 31 1]

-- Cycle fingerprint b8add20e989d34c73c657c58bb3f27c3e01ac2e44fa82b739fffd54296678248.
def localCycle00177 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 3, .distance 1 4, .distance 1 6, .distance 1 5, .distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 1 3]
    constant := ![0, -2, 0, -2, -1, 0, 0, 3, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![true, false, true, false, false, false, false, false, true] }
  origin := ![.triangle 19 2, .gapLower 1 4, .triangle 24 1, .gapLower 1 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 15 2]

-- Cycle fingerprint bae473f0cf77d3643d49a656866b90150b7987d499a69e39ba9821ab8a453bd9.
def localCycle00178 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 3, .distance 2 3, .distance 3 4, .distance 4 5, .distance 5 6, .distance 0 5, .theta 0, .zero]
    constant := ![0, 3, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 3, .corridorUpper 2 3, .triangle 25 0, .triangle 31 0, .triangle 34 0, .triangle 14 0, .corridorLower 0 5, .thetaLower 0]

-- Cycle fingerprint bbf9482ed71eac3009dd4345d1df3635f530d366b10181da4243aab55327c70e.
def localCycle00179 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 4 5, .distance 2 4, .distance 2 3, .distance 1 2, .distance 2 6, .distance 3 6, .distance 4 6, .theta 4]
    constant := ![3, -1, -1, 0, -1, -1, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 31 0, .triangle 28 0, .gapLower 2 4, .triangle 15 0, .triangle 18 0, .triangle 27 1, .triangle 32 1, .corridorLower 4 6]

-- Cycle fingerprint bc4ce61628607b953dc3fc7671d80050093d89607d0809d6d4121c37a7d1a8af.
def localCycle00180 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 4, .distance 1 5, .distance 1 2, .distance 0 1, .theta 0, .zero, .theta 6, .distance 5 6, .distance 4 6, .distance 1 4]
    constant := ![0, -2, -2, -1, 0, 0, 3, 0, -1]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![true, false, false, false, false, false, false, true, false] }
  origin := ![.triangle 22 2, .gapLower 1 2, .gapLower 1 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 23 0]

-- Cycle fingerprint bd42d03c2418473165a00dca6dbc49b652899ae65e88dc87564bf3916a26e6d9.
def localCycle00181 : Cycle where
  length := 8
  data := {
    node := ![.distance 4 5, .distance 0 4, .distance 0 3, .distance 0 1, .theta 1, .distance 1 3, .distance 3 4, .distance 4 6, .distance 4 5]
    constant := ![-1, 0, 0, 0, 1, -1, -1, 0]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, true] }
  origin := ![.triangle 12 0, .gapLower 0 3, .triangle 1 1, .gapLower 1 0, .gapLower 1 6, .triangle 19 0, .triangle 32 0, .triangle 34 1]

-- Cycle fingerprint be5ad2b2125a82904a3f92da1dafa965d91fad9522e66e8dcf6a597f0705665f.
def localCycle00182 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 4, .distance 1 6, .theta 6, .theta 5, .theta 4, .theta 3, .distance 2 3, .distance 3 4, .distance 4 5, .distance 1 4]
    constant := ![0, -2, 0, 0, 0, 3, -1, -1, -1]
    coefficient := ![0, -1, 0, 0, 0, 1, 0, 0, 0]
    strict := ![true, true, true, true, true, false, false, false, false] }
  origin := ![.triangle 23 2, .gapUpper 6 6, .thetaNext 5, .thetaNext 4, .thetaNext 3, .corridorUpper 2 3, .triangle 25 0, .triangle 31 0, .triangle 22 0]

-- Cycle fingerprint c00388e76c51f92b117d46109bc7a0f260f32b291fc71343e52b826915f0b1b0.
def localCycle00183 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 2 4, .distance 4 5, .distance 3 4, .distance 1 3, .distance 3 6, .distance 4 6, .theta 4]
    constant := ![3, -1, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false] }
  origin := ![.corridorUpper 2 4, .triangle 28 0, .triangle 31 0, .triangle 19 0, .triangle 21 0, .triangle 32 1, .corridorLower 4 6]

-- Cycle fingerprint c01afb07aa35b287026f5a3945cf6a1f785165c4886127aff655c2900dc5efdb.
def localCycle00184 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 5, .distance 1 2, .distance 0 1, .theta 1, .zero, .theta 6, .distance 5 6, .distance 1 5]
    constant := ![-2, -1, -2, 0, 0, 3, -1]
    coefficient := ![0, 0, 0, 0, 1, 1, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 1 2, .triangle 0 0, .gapLower 1 0, .thetaLower 1, .thetaUpper 6, .corridorUpper 5 6, .triangle 24 0]

-- Cycle fingerprint c25a2b7318a16060a079731494cd7ed4487639d09f0f1db8332827fd1458008c.
def localCycle00185 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 3, .distance 2 3, .distance 2 4, .distance 2 5, .distance 5 6, .distance 1 6, .distance 1 5, .distance 1 2, .distance 0 1, .theta 1, .zero]
    constant := ![0, 3, 0, 0, -1, 0, -2, 0, -1, -2, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, true, false, false, false] }
  origin := ![.thetaUpper 3, .corridorUpper 2 3, .triangle 25 2, .triangle 28 2, .triangle 30 0, .gapLower 6 4, .gapLower 1 3, .triangle 17 1, .triangle 0 0, .gapLower 1 0, .thetaLower 1]

-- Cycle fingerprint c2748b3430b73d7d53eb80ed3771b107d2c986728c5427979d4df7bb509903a2.
def localCycle00186 : Cycle where
  length := 11
  data := {
    node := ![.distance 3 5, .distance 4 5, .distance 0 4, .distance 0 3, .theta 3, .distance 2 3, .distance 1 3, .distance 1 4, .distance 1 6, .distance 1 2, .distance 2 5, .distance 3 5]
    constant := ![0, -1, 0, 0, 3, 0, -2, -2, 0, -1, 0]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0]
    strict := ![true, false, false, false, false, true, false, false, true, false, true] }
  origin := ![.triangle 31 1, .triangle 12 0, .gapLower 0 3, .gapLower 3 0, .corridorUpper 2 3, .triangle 15 2, .gapLower 1 5, .gapLower 1 4, .triangle 18 1, .triangle 17 0, .triangle 26 1]

-- Cycle fingerprint c2dedc4d6c796215fc083589462166de5526900333910fb922fb557785e0093c.
def localCycle00187 : Cycle where
  length := 8
  data := {
    node := ![.theta 0, .zero, .theta 3, .distance 2 3, .distance 1 2, .distance 1 6, .distance 1 5, .distance 0 1, .theta 0]
    constant := ![0, 0, 3, -1, -2, 0, -2, -1]
    coefficient := ![0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, false] }
  origin := ![.thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 15 0, .gapLower 1 3, .triangle 24 1, .gapLower 1 1, .corridorLower 0 1]

-- Cycle fingerprint c36a6159d14b5972d4a38bfff0bf817484bf5feb6a17558c251ce38c835a5a54.
def localCycle00188 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 4, .distance 3 4, .distance 4 6, .distance 4 5, .distance 0 4, .distance 0 3, .theta 0, .zero, .theta 1, .distance 1 3, .distance 1 4]
    constant := ![0, -1, 0, -1, 0, -1, 0, 0, 2, -2]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![true, false, true, false, false, false, false, false, false, false] }
  origin := ![.triangle 19 1, .triangle 32 0, .triangle 34 1, .triangle 12 0, .gapLower 0 3, .corridorLower 0 3, .thetaLower 0, .thetaUpper 1, .gapLower 1 6, .gapLower 1 5]

-- Cycle fingerprint c36b93192e175076ebcdc8560d129831c43457f715ac39e24e6a515c4826abc5.
def localCycle00189 : Cycle where
  length := 11
  data := {
    node := ![.distance 2 5, .distance 3 5, .distance 4 5, .distance 0 4, .distance 0 3, .distance 0 1, .theta 1, .distance 1 3, .distance 1 4, .distance 1 6, .distance 1 2, .distance 2 5]
    constant := ![0, 0, -1, 0, 0, 0, 2, 0, -2, 0, -1]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0]
    strict := ![true, true, false, false, true, false, false, true, false, true, false] }
  origin := ![.triangle 26 1, .triangle 31 1, .triangle 12 0, .gapLower 0 3, .triangle 1 1, .gapLower 1 0, .gapLower 1 6, .triangle 19 2, .gapLower 1 4, .triangle 18 1, .triangle 17 0]

-- Cycle fingerprint c3c44b86ec30a1f70207fb4b3ebb1648230169da54169745ca1ec93c4761a636.
def localCycle00190 : Cycle where
  length := 3
  data := {
    node := ![.distance 3 4, .distance 1 3, .distance 1 4, .distance 3 4]
    constant := ![2, -3, 0]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.gapUpper 3 4, .gapLower 1 5, .triangle 19 1]

-- Cycle fingerprint c4db3e0430c3bd7ecd52bcc5d0610f0aa21ac0930f8febc36a8ea47c42c6bdc6.
def localCycle00191 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 5, .distance 1 2, .distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 1 3, .distance 1 4, .distance 1 6, .distance 1 5]
    constant := ![-2, -1, -1, 0, 0, 3, 0, 0, -2, 0]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, true, false, true] }
  origin := ![.gapLower 1 2, .triangle 0 0, .corridorLower 0 1, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 15 2, .triangle 19 2, .gapLower 1 4, .triangle 24 1]

-- Cycle fingerprint c4f224957bc3139655aea255cef9a254976f7ea00620d066555160f9e9a07cb1.
def localCycle00192 : Cycle where
  length := 9
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 2 3, .distance 1 2, .distance 2 4, .distance 3 4, .distance 4 6, .distance 5 6, .theta 5]
    constant := ![3, 0, -1, -1, -1, 0, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, true, false, true, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 26 0, .triangle 15 0, .triangle 16 0, .triangle 25 1, .triangle 32 0, .triangle 34 1, .corridorLower 5 6]

-- Cycle fingerprint c54ddd8ff40bc848551e1ee92b9f43d21fd4c8c43d6a7751e104c52d7f919b11.
def localCycle00193 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 6, .distance 1 5, .distance 1 2, .distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 1 3, .distance 1 4, .distance 1 6]
    constant := ![0, 0, -2, -1, 0, 0, 3, 0, -2, 0]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![true, false, false, false, false, false, false, true, false, true] }
  origin := ![.triangle 24 1, .gapLower 1 2, .gapLower 1 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 15 2, .gapLower 1 5, .triangle 23 2]

-- Cycle fingerprint c5fcfee85447095ca6307e251d8936a1182e055f305628a1a4a6fdbc373cd6a9.
def localCycle00194 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 2, .distance 1 6, .distance 1 5, .distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 1 3, .distance 1 4, .distance 1 2]
    constant := ![0, 0, -2, -1, 0, 0, 3, 0, -2, 0]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![true, true, false, false, false, false, false, true, false, true] }
  origin := ![.triangle 18 2, .triangle 24 1, .gapLower 1 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 15 2, .gapLower 1 5, .triangle 16 1]

-- Cycle fingerprint c64300c403c1ab24aac4c618a8668ab3756c789f8c3652826fef8ee5cd9a282c.
def localCycle00195 : Cycle where
  length := 11
  data := {
    node := ![.distance 4 6, .distance 3 4, .theta 3, .distance 2 3, .distance 3 5, .distance 1 3, .distance 1 6, .theta 6, .theta 5, .distance 4 5, .distance 1 4, .distance 4 6]
    constant := ![-1, -1, 3, -1, -1, 0, -2, 0, 3, -1, -1]
    coefficient := ![0, 0, 1, 0, 0, 0, -1, 0, 1, 0, 0]
    strict := ![false, false, false, false, false, true, true, true, false, false, false] }
  origin := ![.triangle 32 0, .corridorLower 3 4, .corridorUpper 2 3, .triangle 26 0, .triangle 20 0, .triangle 21 2, .gapUpper 6 6, .thetaNext 5, .corridorUpper 4 5, .triangle 22 0, .triangle 23 0]

-- Cycle fingerprint c75ce807468586ad49cbc555b12db9febe3ac5342438ab0a619e6a60e4cf044a.
def localCycle00196 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 3, .distance 2 3, .distance 3 5, .distance 3 4, .distance 1 3, .distance 3 6, .distance 4 6, .distance 5 6, .distance 0 5, .theta 0, .zero]
    constant := ![0, 3, -1, 0, -1, -1, 0, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, true, true, false, false, false] }
  origin := ![.thetaUpper 3, .corridorUpper 2 3, .triangle 26 0, .triangle 31 1, .triangle 19 0, .triangle 21 0, .triangle 32 1, .triangle 34 1, .triangle 14 0, .corridorLower 0 5, .thetaLower 0]

-- Cycle fingerprint c7fc7bc78c908eb0a8dc9f46bab2fe71b645ebd148187d184452f77914292062.
def localCycle00197 : Cycle where
  length := 13
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 2 3, .distance 1 2, .distance 2 5, .distance 3 5, .distance 4 5, .distance 0 4, .distance 0 3, .distance 0 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, -1, -1, -1, 0, 0, -1, 0, 0, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, false, true, true, true, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 25 0, .triangle 15 0, .triangle 17 0, .triangle 26 1, .triangle 31 1, .triangle 12 0, .triangle 9 1, .triangle 5 1, .triangle 0 1, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint c92c46f9da8b9b7cbb0d07d92935a1ccd5a493085ca734d025eec8afc4bc739e.
def localCycle00198 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 3 5, .distance 5 6, .distance 2 5, .distance 2 3, .distance 1 2, .distance 2 4, .distance 3 4, .theta 3]
    constant := ![4, -1, -1, 0, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, true, false] }
  origin := ![.gapLower 3 6, .triangle 33 0, .triangle 30 0, .triangle 26 1, .triangle 15 0, .triangle 16 0, .triangle 25 1, .corridorLower 3 4]

-- Cycle fingerprint c972b7a0c8cac1b20eeec2f8081a2175a65623886b617c3cec0b6a6c8c0f3626.
def localCycle00199 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 3, .distance 1 2, .distance 2 4, .distance 3 4, .theta 3, .distance 3 5, .distance 2 3, .distance 3 6, .distance 5 6, .distance 1 5, .distance 1 3]
    constant := ![0, -1, 0, -1, 4, -1, -1, 0, -1, 0]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0]
    strict := ![true, false, true, false, false, false, false, true, false, true] }
  origin := ![.triangle 15 1, .triangle 16 0, .triangle 25 1, .corridorLower 3 4, .gapLower 3 6, .triangle 26 0, .triangle 27 0, .triangle 33 1, .triangle 24 0, .triangle 20 1]

-- Cycle fingerprint c9ba77943d96e650bf1db5c191355bd9dc4caefe60979de0c0e5a7f3cf599c4d.
def localCycle00200 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 3, .distance 2 3, .distance 1 2, .distance 2 5, .distance 3 5, .distance 4 5, .distance 5 6, .distance 0 5, .theta 0, .zero]
    constant := ![0, 3, -1, -1, 0, 0, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, false, false, false, false] }
  origin := ![.thetaUpper 3, .corridorUpper 2 3, .triangle 15 0, .triangle 17 0, .triangle 26 1, .triangle 31 1, .triangle 34 0, .triangle 14 0, .corridorLower 0 5, .thetaLower 0]

-- Cycle fingerprint cb3a12bf9ef078c3e889b761e5055a1ecfddb176ac7980e9683218e5fdfa4852.
def localCycle00201 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 5, .distance 1 2, .distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 1 3, .distance 1 6, .distance 1 4, .distance 1 5]
    constant := ![-2, -1, -1, 0, 0, 3, 0, 0, -2, 0]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, true, false, true] }
  origin := ![.gapLower 1 2, .triangle 0 0, .corridorLower 0 1, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 15 2, .triangle 21 2, .gapLower 1 4, .triangle 22 2]

-- Cycle fingerprint cc661757948d3264df9a0d99750e4a5bbf1a56ebd7fedd333428c92b7fd7246c.
def localCycle00202 : Cycle where
  length := 4
  data := {
    node := ![.distance 1 2, .distance 1 5, .distance 5 6, .distance 2 6, .distance 1 2]
    constant := ![-2, 2, 0, -1]
    coefficient := ![0, 0, 0, 0]
    strict := ![false, true, false, false] }
  origin := ![.gapLower 1 2, .gapUpper 5 5, .gapLower 6 5, .triangle 18 0]

-- Cycle fingerprint ce41069cdf53aed4be0305f97a2ec4e5b481de881234d83d177df13925c5c490.
def localCycle00203 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 5, .distance 3 5, .distance 2 3, .distance 1 2, .distance 2 4, .distance 3 4, .distance 0 3, .theta 0, .zero]
    constant := ![0, 3, -1, 0, -1, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, true, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 0, .triangle 31 2, .triangle 26 0, .triangle 15 0, .triangle 16 0, .triangle 25 1, .triangle 9 0, .corridorLower 0 3, .thetaLower 0]

-- Cycle fingerprint d0952198f4638f87ad17b56cf3e6c665d8620daf8f48f84cab897cde1811efcc.
def localCycle00204 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 2 3, .distance 1 2, .distance 2 6, .distance 3 6, .distance 4 6, .distance 5 6, .distance 0 5, .theta 0, .zero]
    constant := ![0, 3, -1, -1, -1, 0, 0, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, true, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 25 0, .triangle 15 0, .triangle 18 0, .triangle 27 1, .triangle 32 1, .triangle 34 1, .triangle 14 0, .corridorLower 0 5, .thetaLower 0]

-- Cycle fingerprint d1c4b01732f7ba71383d0c47619e73e98794cb6410fa019b6770622046c00d32.
def localCycle00205 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 2, .distance 0 1, .theta 0, .zero, .theta 6, .distance 5 6, .distance 4 6, .distance 2 4, .distance 1 4, .distance 1 5, .distance 1 2]
    constant := ![-2, -1, 0, 0, 3, 0, -1, 0, -2, 0]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, true, false, true] }
  origin := ![.gapLower 1 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 29 0, .triangle 16 2, .gapLower 1 3, .triangle 17 1]

-- Cycle fingerprint d2eda2961e6b837c8bc631cb2b250b485e842aec67fb191c54f05e1afb8cd421.
def localCycle00206 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 5, .distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 1 3, .distance 1 4, .distance 1 6, .distance 1 2, .distance 1 5]
    constant := ![-2, -1, 0, 0, 3, 0, 0, 0, -2, 0]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, true, false, true] }
  origin := ![.gapLower 1 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 15 2, .triangle 19 2, .triangle 23 2, .gapLower 1 3, .triangle 17 2]

-- Cycle fingerprint d4d9727772551381b138fe0483b14b7b3d72af96192bb07cebc4ed24e742d97f.
def localCycle00207 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 2, .distance 0 1, .theta 1, .zero, .theta 3, .distance 2 3, .distance 1 3, .distance 1 4, .distance 1 6, .distance 1 5, .distance 1 2]
    constant := ![-1, -2, 0, 0, 3, 0, 0, 0, -2, 0]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, true, false, true] }
  origin := ![.triangle 0 0, .gapLower 1 0, .thetaLower 1, .thetaUpper 3, .corridorUpper 2 3, .triangle 15 2, .triangle 19 2, .triangle 23 2, .gapLower 1 3, .triangle 17 1]

-- Cycle fingerprint d7a8f9f8f9cc8c4b0ed53350fe35f663e3c889519f27b0c00bbe66ae60110756.
def localCycle00208 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 2 4, .distance 2 6, .distance 1 2, .distance 2 5, .distance 4 5, .distance 3 4, .theta 3]
    constant := ![3, 0, 0, -1, -1, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, true, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 25 2, .triangle 29 2, .triangle 18 0, .triangle 17 0, .triangle 28 1, .triangle 31 0, .corridorLower 3 4]

-- Cycle fingerprint d7c3db83857e8b72a57a0be1ff911c00551c48e52203e701e026f11f5ed73dfc.
def localCycle00209 : Cycle where
  length := 13
  data := {
    node := ![.theta 5, .distance 4 5, .distance 5 6, .distance 3 6, .distance 2 3, .distance 1 2, .distance 2 4, .distance 3 4, .distance 0 3, .distance 0 2, .distance 0 1, .theta 0, .zero, .theta 5]
    constant := ![3, -1, 0, -1, -1, -1, 0, -1, 0, 0, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![false, false, false, false, false, false, true, false, true, true, false, false, false] }
  origin := ![.corridorUpper 4 5, .triangle 34 0, .gapLower 6 4, .triangle 27 0, .triangle 15 0, .triangle 16 0, .triangle 25 1, .triangle 9 0, .triangle 5 1, .triangle 0 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 5]

-- Cycle fingerprint d83de52b4bc6707d4436013cd1d66df413a6775f93e205e5b76dc67b2ee29ae5.
def localCycle00210 : Cycle where
  length := 11
  data := {
    node := ![.distance 3 5, .distance 4 5, .distance 0 4, .distance 0 3, .theta 0, .zero, .theta 1, .distance 1 3, .distance 1 4, .distance 1 2, .distance 2 5, .distance 3 5]
    constant := ![0, -1, 0, -1, 0, 0, 2, -2, 0, -1, 0]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![true, false, false, false, false, false, false, false, true, false, true] }
  origin := ![.triangle 31 1, .triangle 12 0, .gapLower 0 3, .corridorLower 0 3, .thetaLower 0, .thetaUpper 1, .gapLower 1 6, .gapLower 1 5, .triangle 16 1, .triangle 17 0, .triangle 26 1]

-- Cycle fingerprint d8493897b9ace056094350707747895c88e03954cc3b5fd38206a8dea2bcb8ae.
def localCycle00211 : Cycle where
  length := 13
  data := {
    node := ![.distance 1 3, .distance 1 4, .distance 1 5, .distance 1 6, .distance 5 6, .distance 3 5, .distance 0 3, .distance 0 2, .distance 0 1, .theta 1, .zero, .theta 3, .distance 2 3, .distance 1 3]
    constant := ![0, 0, -2, 0, -1, -1, 0, 0, -2, 0, 0, 3, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![true, true, false, true, false, false, false, true, false, false, false, false, true] }
  origin := ![.triangle 19 2, .triangle 22 2, .gapLower 1 3, .triangle 24 1, .triangle 33 0, .triangle 10 0, .gapLower 0 2, .triangle 0 1, .gapLower 1 0, .thetaLower 1, .thetaUpper 3, .corridorUpper 2 3, .triangle 15 2]

-- Cycle fingerprint daec27b8a60946e102a0469ce3ea6c443c8d7b19d86ac1249a8bc2079132f92c.
def localCycle00212 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 3, .distance 1 2, .distance 2 5, .distance 3 5, .distance 4 5, .distance 5 6, .theta 5, .theta 4]
    constant := ![3, -1, -1, -1, 0, 0, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, false, false, true] }
  origin := ![.corridorUpper 3 4, .triangle 25 0, .triangle 15 0, .triangle 17 0, .triangle 26 1, .triangle 31 1, .triangle 34 0, .corridorLower 5 6, .thetaNext 4]

-- Cycle fingerprint db50cb21964ee201ad2577272d306bc234bda0327e03b92dd9d5a5c88c22cf7a.
def localCycle00213 : Cycle where
  length := 6
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 2, .distance 1 5, .distance 5 6, .distance 3 5, .theta 3]
    constant := ![3, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 0, .triangle 17 2, .triangle 24 0, .triangle 33 0, .corridorLower 3 5]

-- Cycle fingerprint dc001319960936f631e7aa3f289e831aba25f308cedf61cbe07d4f48b5dc3112.
def localCycle00214 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 2 4, .distance 4 6, .distance 3 6, .distance 1 3, .distance 3 4, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, 0, -1, 0, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, false, false, true] }
  origin := ![.corridorUpper 2 3, .triangle 25 2, .triangle 29 0, .triangle 32 2, .triangle 21 0, .triangle 19 0, .triangle 31 0, .corridorLower 4 5, .thetaNext 3]

-- Cycle fingerprint df2ec82936ee1e3ac7c6a4b96a7870c087fc22c88fec994f5f2ae9a98c7ab2c7.
def localCycle00215 : Cycle where
  length := 9
  data := {
    node := ![.distance 2 3, .distance 1 3, .distance 1 6, .distance 1 4, .distance 3 4, .distance 4 5, .distance 0 4, .distance 0 3, .theta 3, .distance 2 3]
    constant := ![0, -2, -2, 0, -1, -1, 0, 0, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![true, false, false, true, false, false, false, false, false] }
  origin := ![.triangle 15 2, .gapLower 1 5, .gapLower 1 4, .triangle 19 1, .triangle 31 0, .triangle 12 0, .gapLower 0 3, .gapLower 3 0, .corridorUpper 2 3]

-- Cycle fingerprint e40ae0c84a705b3ea219c3432df57438f0b27f12ccfa25a999241eaa9fa78e01.
def localCycle00216 : Cycle where
  length := 3
  data := {
    node := ![.distance 2 6, .distance 1 2, .distance 1 6, .distance 2 6]
    constant := ![2, -3, 0]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.gapUpper 2 3, .gapLower 1 3, .triangle 18 1]

-- Cycle fingerprint e45284e84e6651fec95ba65fc7d9e2596564aa0ae69f2bea1bbdf9907218e1e4.
def localCycle00217 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 4, .distance 1 5, .distance 5 6, .distance 3 5, .theta 3, .distance 2 3, .distance 1 3, .distance 1 4]
    constant := ![-2, -1, -1, -1, 3, 0, 0]
    coefficient := ![0, 0, 0, 0, 1, 0, 0]
    strict := ![false, false, false, false, false, true, true] }
  origin := ![.gapLower 1 4, .triangle 24 0, .triangle 33 0, .corridorLower 3 5, .corridorUpper 2 3, .triangle 15 2, .triangle 19 2]

-- Cycle fingerprint e46c218b1a8272ef55eca8bf7a5ad33846462d5283c48ba3c57069063b5bd964.
def localCycle00218 : Cycle where
  length := 5
  data := {
    node := ![.distance 1 5, .distance 5 6, .distance 2 6, .distance 1 6, .distance 1 2, .distance 1 5]
    constant := ![2, 0, 0, -2, -2]
    coefficient := ![0, 0, 0, 0, 0]
    strict := ![true, false, true, false, false] }
  origin := ![.gapUpper 5 5, .gapLower 6 5, .triangle 18 2, .gapLower 1 3, .gapLower 1 2]

-- Cycle fingerprint e5b377f9776cb84f16b5904cc88165dfcc32d114d825a653c5ebed61189d4478.
def localCycle00219 : Cycle where
  length := 3
  data := {
    node := ![.distance 3 6, .distance 1 3, .distance 1 6, .distance 3 6]
    constant := ![2, -3, 0]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.gapUpper 3 4, .gapLower 1 5, .triangle 21 1]

-- Cycle fingerprint e8d6445f3451cde4d3b012655461076b83b8fc573ae3d92f62cd9d99094c1d0d.
def localCycle00220 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 3, .distance 2 3, .distance 3 4, .distance 1 3, .distance 3 6, .distance 3 5, .distance 0 3, .distance 0 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, -1, -1, -1, 0, -1, 0, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, true, true, false, false] }
  origin := ![.thetaUpper 3, .corridorUpper 2 3, .triangle 25 0, .triangle 19 0, .triangle 21 0, .triangle 33 1, .triangle 10 0, .triangle 5 1, .triangle 0 1, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint e96169b11ec45fd3de28e94e2eda45568908bc545187787c0857bf24947c1b9a.
def localCycle00221 : Cycle where
  length := 6
  data := {
    node := ![.distance 1 3, .distance 1 5, .distance 5 6, .distance 3 6, .distance 2 3, .distance 3 4, .distance 1 3]
    constant := ![0, 2, 0, -1, -1, -1]
    coefficient := ![0, 0, 0, 0, 0, 0]
    strict := ![true, true, true, false, false, false] }
  origin := ![.triangle 20 2, .gapUpper 5 5, .triangle 33 2, .triangle 27 0, .triangle 25 0, .triangle 19 0]

-- Cycle fingerprint e984789e413552df22791401367d2490383f124f2c6efd1053cc2089cf96e354.
def localCycle00222 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 3, .distance 1 4, .distance 1 2, .distance 1 6, .distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 1 3]
    constant := ![0, -2, -2, -1, -1, 0, 0, 3, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![true, false, false, false, false, false, false, false, true] }
  origin := ![.triangle 19 2, .gapLower 1 4, .gapLower 1 3, .triangle 4 0, .corridorLower 0 1, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 15 2]

-- Cycle fingerprint eac5669ffd40cc64d19701cd04b72bf74594bcc3d6542594131094a292c93d43.
def localCycle00223 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 3, .distance 2 5, .distance 1 2, .distance 2 6, .distance 5 6, .distance 4 5, .theta 4]
    constant := ![3, -1, 0, -1, -1, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 0, .triangle 26 2, .triangle 17 0, .triangle 18 0, .triangle 30 1, .triangle 34 0, .corridorLower 4 5]

-- Cycle fingerprint eb7391bdcd1fc4ad01c46036c14f3eef27bdbf53ca7a15db5a372e46cba5f4b5.
def localCycle00224 : Cycle where
  length := 9
  data := {
    node := ![.distance 2 4, .distance 4 6, .distance 1 4, .distance 1 2, .distance 2 5, .distance 4 5, .distance 3 4, .theta 3, .distance 2 3, .distance 2 4]
    constant := ![-1, -1, 0, -1, 0, -1, -1, 3, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1, 0]
    strict := ![false, false, false, false, true, false, false, false, true] }
  origin := ![.triangle 29 0, .triangle 23 0, .gapLower 1 3, .triangle 17 0, .triangle 28 1, .triangle 31 0, .corridorLower 3 4, .corridorUpper 2 3, .triangle 25 2]

-- Cycle fingerprint edd183f4d51f91d67ee616be57b90c7b034a602ccaecf2bc5957282dacc98a62.
def localCycle00225 : Cycle where
  length := 9
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 2 3, .distance 3 4, .distance 1 3, .distance 3 6, .distance 4 6, .distance 5 6, .theta 5]
    constant := ![3, 0, -1, -1, -1, -1, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, true, true, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 26 0, .triangle 25 0, .triangle 19 0, .triangle 21 0, .triangle 32 1, .triangle 34 1, .corridorLower 5 6]

-- Cycle fingerprint ee8b2204afd77912b49cc422559baf882ed9092fa26212e07f1f373768bb2163.
def localCycle00226 : Cycle where
  length := 6
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 2, .distance 2 6, .distance 5 6, .distance 3 5, .theta 3]
    constant := ![3, -1, -1, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 0, .triangle 18 0, .triangle 30 1, .triangle 33 0, .corridorLower 3 5]

-- Cycle fingerprint f13de0f3e2ce5517725d21e5d9134dee210fee5fe0d60c0862c77b1a93849194.
def localCycle00227 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .theta 1, .zero, .theta 3, .distance 2 3, .distance 2 4, .distance 2 5, .distance 5 6, .distance 1 5, .distance 1 2, .distance 0 1]
    constant := ![-2, 0, 0, 3, 0, 0, -1, -1, -2, -1]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, false, false, false, false] }
  origin := ![.gapLower 1 0, .thetaLower 1, .thetaUpper 3, .corridorUpper 2 3, .triangle 25 2, .triangle 28 2, .triangle 30 0, .triangle 24 0, .gapLower 1 2, .triangle 0 0]

-- Cycle fingerprint f150b1fc1433ae759aae0332701eabecfcbc83a841a621cd4b309559c2429bd6.
def localCycle00228 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 2 3, .distance 2 4, .distance 4 5, .distance 1 4, .distance 4 6, .distance 3 4, .theta 3]
    constant := ![3, 0, -1, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 25 2, .triangle 28 0, .triangle 22 0, .triangle 23 0, .triangle 32 0, .corridorLower 3 4]

-- Cycle fingerprint f415e2377affca08d00a8acf6fd3abed2e428ffa69d8129f1aabd9f73fc7ebf6.
def localCycle00229 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 6, .distance 1 5, .distance 1 2, .distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 1 3, .distance 1 4, .distance 1 6]
    constant := ![0, -2, -1, -1, 0, 0, 3, 0, -2, 0]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![true, false, false, false, false, false, false, true, false, true] }
  origin := ![.triangle 24 1, .gapLower 1 2, .triangle 0 0, .corridorLower 0 1, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 15 2, .gapLower 1 5, .triangle 23 2]

-- Cycle fingerprint f48c1890dab68c1f4ae1d9e04445893563fdfe476b8c6bb5d023a0a06f38df77.
def localCycle00230 : Cycle where
  length := 12
  data := {
    node := ![.distance 1 4, .distance 1 3, .distance 1 2, .distance 2 5, .distance 3 5, .distance 4 5, .distance 0 4, .distance 0 3, .theta 3, .distance 2 3, .distance 3 4, .distance 4 6, .distance 1 4]
    constant := ![0, 0, -1, 0, 0, -1, 0, 0, 3, -1, -1, -1]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![false, true, false, true, true, false, false, false, false, false, false, false] }
  origin := ![.gapLower 1 4, .triangle 15 1, .triangle 17 0, .triangle 26 1, .triangle 31 1, .triangle 12 0, .gapLower 0 3, .gapLower 3 0, .corridorUpper 2 3, .triangle 25 0, .triangle 32 0, .triangle 23 0]

-- Cycle fingerprint f7264cb87561645ea2db0eb2cc16a6a5189978f9145e8f38f857b2651af96659.
def localCycle00231 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 6, .distance 1 5, .distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 1 3, .distance 1 4, .distance 1 2, .distance 1 6]
    constant := ![-2, -1, -1, 0, 0, 3, 0, 0, -2, 0]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, true, false, true] }
  origin := ![.gapLower 1 2, .triangle 3 0, .corridorLower 0 1, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 15 2, .triangle 19 2, .gapLower 1 4, .triangle 18 2]

-- Cycle fingerprint f7426e7ede10dc413047f0b35f4c49ecb00695e45beddd2750ad633b13642d8b.
def localCycle00232 : Cycle where
  length := 8
  data := {
    node := ![.theta 0, .zero, .theta 3, .distance 2 3, .distance 1 3, .distance 1 6, .distance 1 2, .distance 0 1, .theta 0]
    constant := ![0, 0, 3, 0, -2, 0, -2, -1]
    coefficient := ![0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true, false, false] }
  origin := ![.thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 15 2, .gapLower 1 5, .triangle 18 1, .gapLower 1 1, .corridorLower 0 1]

-- Cycle fingerprint f7da6d28293cc001b2555acb13a055030f7651ac95a2bb5700f4ec96358925ea.
def localCycle00233 : Cycle where
  length := 5
  data := {
    node := ![.distance 1 5, .distance 5 6, .distance 2 6, .distance 1 6, .distance 1 2, .distance 1 5]
    constant := ![2, 0, 0, -3, 0]
    coefficient := ![0, 0, 0, 0, 0]
    strict := ![true, false, false, false, true] }
  origin := ![.gapUpper 5 5, .gapLower 6 5, .gapLower 6 4, .gapLower 1 3, .triangle 17 2]

-- Cycle fingerprint fab6f2b1adf7d422f8f1343cf79cd5f170c0f3e2d0e0bd5402f7c075189dfc1c.
def localCycle00234 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 5, .distance 3 6, .distance 1 3, .distance 1 2, .distance 2 4, .distance 3 4, .theta 3]
    constant := ![3, -1, 0, -1, 0, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 26 0, .triangle 33 2, .triangle 21 0, .triangle 15 1, .triangle 16 0, .triangle 25 1, .corridorLower 3 4]

-- Cycle fingerprint fb2642c7fb7ee8ad5c8965c1478fe20e8d31d226bf7d5dc44f240f5f4cd35f64.
def localCycle00235 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 2, .distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 1 3, .distance 1 4, .distance 1 5, .distance 1 6, .distance 1 2]
    constant := ![-1, -1, 0, 0, 3, 0, 0, 0, -2, -2]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, true, false, false] }
  origin := ![.triangle 0 0, .corridorLower 0 1, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 15 2, .triangle 19 2, .triangle 22 2, .gapLower 1 3, .gapLower 1 2]

-- Cycle fingerprint fc949736fc3f0c84efdcf07ce7002d0112c3b347c643482f4e8e872ebfddd453.
def localCycle00236 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 3, .distance 1 6, .distance 1 4, .distance 1 5, .distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 1 3]
    constant := ![0, -2, -2, -1, -1, 0, 0, 3, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![true, false, false, false, false, false, false, false, true] }
  origin := ![.triangle 21 2, .gapLower 1 4, .gapLower 1 3, .triangle 3 0, .corridorLower 0 1, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 15 2]

-- Cycle fingerprint fcad58957fdc0db7cffbd384ded682e44e696cb132afc5123bb11f5f7ffd2aca.
def localCycle00237 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 3, .distance 2 5, .distance 1 2, .distance 2 6, .distance 3 6, .distance 4 6, .theta 4]
    constant := ![3, -1, 0, -1, -1, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 0, .triangle 26 2, .triangle 17 0, .triangle 18 0, .triangle 27 1, .triangle 32 1, .corridorLower 4 6]

-- Cycle fingerprint fddd90d4596465193b06ee2dd1b41d281c11462154ddc1ed0f77d65a09f5ef11.
def localCycle00238 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 4, .distance 4 6, .distance 3 4, .theta 3, .distance 2 3, .distance 2 4, .distance 4 5, .distance 3 5, .distance 1 3, .distance 1 4]
    constant := ![-1, -1, -1, 3, 0, -1, 0, -1, 0]
    coefficient := ![0, 0, 0, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, true, false, false] }
  origin := ![.triangle 23 0, .triangle 32 0, .corridorLower 3 4, .corridorUpper 2 3, .triangle 25 2, .triangle 28 0, .triangle 31 2, .triangle 20 0, .gapLower 1 4]

-- Cycle fingerprint fe768191324e06bc6742d2f68c5fc06acbc3a2b2e8d38e1b83eed2c8e96ea33f.
def localCycle00239 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 3, .distance 1 2, .distance 2 4, .distance 3 4, .distance 0 3, .theta 0, .zero]
    constant := ![0, 3, 0, -1, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, true, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 0, .triangle 15 0, .triangle 16 0, .triangle 25 1, .triangle 9 0, .corridorLower 0 3, .thetaLower 0]

-- Cycle fingerprint fee3e2b4674dd2480a496b2ea23ef0466d3a9f7a5e82beaaf6c78ca7e03281e2.
def localCycle00240 : Cycle where
  length := 9
  data := {
    node := ![.distance 5 6, .distance 3 5, .distance 1 3, .distance 1 2, .distance 2 4, .distance 3 4, .theta 3, .distance 2 3, .distance 2 5, .distance 5 6]
    constant := ![-1, -1, 0, -1, 0, -1, 3, 0, -1]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 0, 0]
    strict := ![false, false, false, false, true, false, false, true, false] }
  origin := ![.triangle 33 0, .triangle 20 0, .gapLower 1 3, .triangle 16 0, .triangle 25 1, .corridorLower 3 4, .corridorUpper 2 3, .triangle 26 2, .triangle 30 0]

-- Cycle fingerprint ffe354f08d37ed3dc2855f61886f5b5678591aced62644c2a9ac6ad5d1e18ea4.
def localCycle00241 : Cycle where
  length := 13
  data := {
    node := ![.zero, .theta 3, .distance 2 3, .distance 1 3, .distance 1 4, .distance 4 6, .distance 3 4, .distance 4 5, .distance 0 4, .distance 0 3, .distance 0 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, 0, -1, -1, -1, -1, 0, 0, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, false, true, true, true, false, false] }
  origin := ![.thetaUpper 3, .corridorUpper 2 3, .triangle 15 2, .triangle 19 2, .triangle 23 0, .triangle 32 0, .triangle 31 0, .triangle 12 0, .triangle 9 1, .triangle 5 1, .triangle 0 1, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint fff793fbdca27929fdd8da9cd72ed03cb4f512a39620d71d5be81753872a1969.
def localCycle00242 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 3, .distance 2 3, .distance 1 3, .distance 1 4, .distance 1 2, .distance 0 1, .theta 1, .zero]
    constant := ![0, 3, 0, 0, -2, -1, -2, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, false] }
  origin := ![.thetaUpper 3, .corridorUpper 2 3, .triangle 15 2, .triangle 19 2, .gapLower 1 4, .triangle 0 0, .gapLower 1 0, .thetaLower 1]

def library : Library := fun id => if id < 121 then (if id < 60 then (if id < 30 then (if id < 15 then (if id < 7 then (if id < 3 then (if id < 1 then (if id = 0 then some localCycle00000 else none) else (if id < 2 then (if id = 1 then some localCycle00001 else none) else (if id = 2 then some localCycle00002 else none))) else (if id < 5 then (if id < 4 then (if id = 3 then some localCycle00003 else none) else (if id = 4 then some localCycle00004 else none)) else (if id < 6 then (if id = 5 then some localCycle00005 else none) else (if id = 6 then some localCycle00006 else none)))) else (if id < 11 then (if id < 9 then (if id < 8 then (if id = 7 then some localCycle00007 else none) else (if id = 8 then some localCycle00008 else none)) else (if id < 10 then (if id = 9 then some localCycle00009 else none) else (if id = 10 then some localCycle00010 else none))) else (if id < 13 then (if id < 12 then (if id = 11 then some localCycle00011 else none) else (if id = 12 then some localCycle00012 else none)) else (if id < 14 then (if id = 13 then some localCycle00013 else none) else (if id = 14 then some localCycle00014 else none))))) else (if id < 22 then (if id < 18 then (if id < 16 then (if id = 15 then some localCycle00015 else none) else (if id < 17 then (if id = 16 then some localCycle00016 else none) else (if id = 17 then some localCycle00017 else none))) else (if id < 20 then (if id < 19 then (if id = 18 then some localCycle00018 else none) else (if id = 19 then some localCycle00019 else none)) else (if id < 21 then (if id = 20 then some localCycle00020 else none) else (if id = 21 then some localCycle00021 else none)))) else (if id < 26 then (if id < 24 then (if id < 23 then (if id = 22 then some localCycle00022 else none) else (if id = 23 then some localCycle00023 else none)) else (if id < 25 then (if id = 24 then some localCycle00024 else none) else (if id = 25 then some localCycle00025 else none))) else (if id < 28 then (if id < 27 then (if id = 26 then some localCycle00026 else none) else (if id = 27 then some localCycle00027 else none)) else (if id < 29 then (if id = 28 then some localCycle00028 else none) else (if id = 29 then some localCycle00029 else none)))))) else (if id < 45 then (if id < 37 then (if id < 33 then (if id < 31 then (if id = 30 then some localCycle00030 else none) else (if id < 32 then (if id = 31 then some localCycle00031 else none) else (if id = 32 then some localCycle00032 else none))) else (if id < 35 then (if id < 34 then (if id = 33 then some localCycle00033 else none) else (if id = 34 then some localCycle00034 else none)) else (if id < 36 then (if id = 35 then some localCycle00035 else none) else (if id = 36 then some localCycle00036 else none)))) else (if id < 41 then (if id < 39 then (if id < 38 then (if id = 37 then some localCycle00037 else none) else (if id = 38 then some localCycle00038 else none)) else (if id < 40 then (if id = 39 then some localCycle00039 else none) else (if id = 40 then some localCycle00040 else none))) else (if id < 43 then (if id < 42 then (if id = 41 then some localCycle00041 else none) else (if id = 42 then some localCycle00042 else none)) else (if id < 44 then (if id = 43 then some localCycle00043 else none) else (if id = 44 then some localCycle00044 else none))))) else (if id < 52 then (if id < 48 then (if id < 46 then (if id = 45 then some localCycle00045 else none) else (if id < 47 then (if id = 46 then some localCycle00046 else none) else (if id = 47 then some localCycle00047 else none))) else (if id < 50 then (if id < 49 then (if id = 48 then some localCycle00048 else none) else (if id = 49 then some localCycle00049 else none)) else (if id < 51 then (if id = 50 then some localCycle00050 else none) else (if id = 51 then some localCycle00051 else none)))) else (if id < 56 then (if id < 54 then (if id < 53 then (if id = 52 then some localCycle00052 else none) else (if id = 53 then some localCycle00053 else none)) else (if id < 55 then (if id = 54 then some localCycle00054 else none) else (if id = 55 then some localCycle00055 else none))) else (if id < 58 then (if id < 57 then (if id = 56 then some localCycle00056 else none) else (if id = 57 then some localCycle00057 else none)) else (if id < 59 then (if id = 58 then some localCycle00058 else none) else (if id = 59 then some localCycle00059 else none))))))) else (if id < 90 then (if id < 75 then (if id < 67 then (if id < 63 then (if id < 61 then (if id = 60 then some localCycle00060 else none) else (if id < 62 then (if id = 61 then some localCycle00061 else none) else (if id = 62 then some localCycle00062 else none))) else (if id < 65 then (if id < 64 then (if id = 63 then some localCycle00063 else none) else (if id = 64 then some localCycle00064 else none)) else (if id < 66 then (if id = 65 then some localCycle00065 else none) else (if id = 66 then some localCycle00066 else none)))) else (if id < 71 then (if id < 69 then (if id < 68 then (if id = 67 then some localCycle00067 else none) else (if id = 68 then some localCycle00068 else none)) else (if id < 70 then (if id = 69 then some localCycle00069 else none) else (if id = 70 then some localCycle00070 else none))) else (if id < 73 then (if id < 72 then (if id = 71 then some localCycle00071 else none) else (if id = 72 then some localCycle00072 else none)) else (if id < 74 then (if id = 73 then some localCycle00073 else none) else (if id = 74 then some localCycle00074 else none))))) else (if id < 82 then (if id < 78 then (if id < 76 then (if id = 75 then some localCycle00075 else none) else (if id < 77 then (if id = 76 then some localCycle00076 else none) else (if id = 77 then some localCycle00077 else none))) else (if id < 80 then (if id < 79 then (if id = 78 then some localCycle00078 else none) else (if id = 79 then some localCycle00079 else none)) else (if id < 81 then (if id = 80 then some localCycle00080 else none) else (if id = 81 then some localCycle00081 else none)))) else (if id < 86 then (if id < 84 then (if id < 83 then (if id = 82 then some localCycle00082 else none) else (if id = 83 then some localCycle00083 else none)) else (if id < 85 then (if id = 84 then some localCycle00084 else none) else (if id = 85 then some localCycle00085 else none))) else (if id < 88 then (if id < 87 then (if id = 86 then some localCycle00086 else none) else (if id = 87 then some localCycle00087 else none)) else (if id < 89 then (if id = 88 then some localCycle00088 else none) else (if id = 89 then some localCycle00089 else none)))))) else (if id < 105 then (if id < 97 then (if id < 93 then (if id < 91 then (if id = 90 then some localCycle00090 else none) else (if id < 92 then (if id = 91 then some localCycle00091 else none) else (if id = 92 then some localCycle00092 else none))) else (if id < 95 then (if id < 94 then (if id = 93 then some localCycle00093 else none) else (if id = 94 then some localCycle00094 else none)) else (if id < 96 then (if id = 95 then some localCycle00095 else none) else (if id = 96 then some localCycle00096 else none)))) else (if id < 101 then (if id < 99 then (if id < 98 then (if id = 97 then some localCycle00097 else none) else (if id = 98 then some localCycle00098 else none)) else (if id < 100 then (if id = 99 then some localCycle00099 else none) else (if id = 100 then some localCycle00100 else none))) else (if id < 103 then (if id < 102 then (if id = 101 then some localCycle00101 else none) else (if id = 102 then some localCycle00102 else none)) else (if id < 104 then (if id = 103 then some localCycle00103 else none) else (if id = 104 then some localCycle00104 else none))))) else (if id < 113 then (if id < 109 then (if id < 107 then (if id < 106 then (if id = 105 then some localCycle00105 else none) else (if id = 106 then some localCycle00106 else none)) else (if id < 108 then (if id = 107 then some localCycle00107 else none) else (if id = 108 then some localCycle00108 else none))) else (if id < 111 then (if id < 110 then (if id = 109 then some localCycle00109 else none) else (if id = 110 then some localCycle00110 else none)) else (if id < 112 then (if id = 111 then some localCycle00111 else none) else (if id = 112 then some localCycle00112 else none)))) else (if id < 117 then (if id < 115 then (if id < 114 then (if id = 113 then some localCycle00113 else none) else (if id = 114 then some localCycle00114 else none)) else (if id < 116 then (if id = 115 then some localCycle00115 else none) else (if id = 116 then some localCycle00116 else none))) else (if id < 119 then (if id < 118 then (if id = 117 then some localCycle00117 else none) else (if id = 118 then some localCycle00118 else none)) else (if id < 120 then (if id = 119 then some localCycle00119 else none) else (if id = 120 then some localCycle00120 else none)))))))) else (if id < 182 then (if id < 151 then (if id < 136 then (if id < 128 then (if id < 124 then (if id < 122 then (if id = 121 then some localCycle00121 else none) else (if id < 123 then (if id = 122 then some localCycle00122 else none) else (if id = 123 then some localCycle00123 else none))) else (if id < 126 then (if id < 125 then (if id = 124 then some localCycle00124 else none) else (if id = 125 then some localCycle00125 else none)) else (if id < 127 then (if id = 126 then some localCycle00126 else none) else (if id = 127 then some localCycle00127 else none)))) else (if id < 132 then (if id < 130 then (if id < 129 then (if id = 128 then some localCycle00128 else none) else (if id = 129 then some localCycle00129 else none)) else (if id < 131 then (if id = 130 then some localCycle00130 else none) else (if id = 131 then some localCycle00131 else none))) else (if id < 134 then (if id < 133 then (if id = 132 then some localCycle00132 else none) else (if id = 133 then some localCycle00133 else none)) else (if id < 135 then (if id = 134 then some localCycle00134 else none) else (if id = 135 then some localCycle00135 else none))))) else (if id < 143 then (if id < 139 then (if id < 137 then (if id = 136 then some localCycle00136 else none) else (if id < 138 then (if id = 137 then some localCycle00137 else none) else (if id = 138 then some localCycle00138 else none))) else (if id < 141 then (if id < 140 then (if id = 139 then some localCycle00139 else none) else (if id = 140 then some localCycle00140 else none)) else (if id < 142 then (if id = 141 then some localCycle00141 else none) else (if id = 142 then some localCycle00142 else none)))) else (if id < 147 then (if id < 145 then (if id < 144 then (if id = 143 then some localCycle00143 else none) else (if id = 144 then some localCycle00144 else none)) else (if id < 146 then (if id = 145 then some localCycle00145 else none) else (if id = 146 then some localCycle00146 else none))) else (if id < 149 then (if id < 148 then (if id = 147 then some localCycle00147 else none) else (if id = 148 then some localCycle00148 else none)) else (if id < 150 then (if id = 149 then some localCycle00149 else none) else (if id = 150 then some localCycle00150 else none)))))) else (if id < 166 then (if id < 158 then (if id < 154 then (if id < 152 then (if id = 151 then some localCycle00151 else none) else (if id < 153 then (if id = 152 then some localCycle00152 else none) else (if id = 153 then some localCycle00153 else none))) else (if id < 156 then (if id < 155 then (if id = 154 then some localCycle00154 else none) else (if id = 155 then some localCycle00155 else none)) else (if id < 157 then (if id = 156 then some localCycle00156 else none) else (if id = 157 then some localCycle00157 else none)))) else (if id < 162 then (if id < 160 then (if id < 159 then (if id = 158 then some localCycle00158 else none) else (if id = 159 then some localCycle00159 else none)) else (if id < 161 then (if id = 160 then some localCycle00160 else none) else (if id = 161 then some localCycle00161 else none))) else (if id < 164 then (if id < 163 then (if id = 162 then some localCycle00162 else none) else (if id = 163 then some localCycle00163 else none)) else (if id < 165 then (if id = 164 then some localCycle00164 else none) else (if id = 165 then some localCycle00165 else none))))) else (if id < 174 then (if id < 170 then (if id < 168 then (if id < 167 then (if id = 166 then some localCycle00166 else none) else (if id = 167 then some localCycle00167 else none)) else (if id < 169 then (if id = 168 then some localCycle00168 else none) else (if id = 169 then some localCycle00169 else none))) else (if id < 172 then (if id < 171 then (if id = 170 then some localCycle00170 else none) else (if id = 171 then some localCycle00171 else none)) else (if id < 173 then (if id = 172 then some localCycle00172 else none) else (if id = 173 then some localCycle00173 else none)))) else (if id < 178 then (if id < 176 then (if id < 175 then (if id = 174 then some localCycle00174 else none) else (if id = 175 then some localCycle00175 else none)) else (if id < 177 then (if id = 176 then some localCycle00176 else none) else (if id = 177 then some localCycle00177 else none))) else (if id < 180 then (if id < 179 then (if id = 178 then some localCycle00178 else none) else (if id = 179 then some localCycle00179 else none)) else (if id < 181 then (if id = 180 then some localCycle00180 else none) else (if id = 181 then some localCycle00181 else none))))))) else (if id < 212 then (if id < 197 then (if id < 189 then (if id < 185 then (if id < 183 then (if id = 182 then some localCycle00182 else none) else (if id < 184 then (if id = 183 then some localCycle00183 else none) else (if id = 184 then some localCycle00184 else none))) else (if id < 187 then (if id < 186 then (if id = 185 then some localCycle00185 else none) else (if id = 186 then some localCycle00186 else none)) else (if id < 188 then (if id = 187 then some localCycle00187 else none) else (if id = 188 then some localCycle00188 else none)))) else (if id < 193 then (if id < 191 then (if id < 190 then (if id = 189 then some localCycle00189 else none) else (if id = 190 then some localCycle00190 else none)) else (if id < 192 then (if id = 191 then some localCycle00191 else none) else (if id = 192 then some localCycle00192 else none))) else (if id < 195 then (if id < 194 then (if id = 193 then some localCycle00193 else none) else (if id = 194 then some localCycle00194 else none)) else (if id < 196 then (if id = 195 then some localCycle00195 else none) else (if id = 196 then some localCycle00196 else none))))) else (if id < 204 then (if id < 200 then (if id < 198 then (if id = 197 then some localCycle00197 else none) else (if id < 199 then (if id = 198 then some localCycle00198 else none) else (if id = 199 then some localCycle00199 else none))) else (if id < 202 then (if id < 201 then (if id = 200 then some localCycle00200 else none) else (if id = 201 then some localCycle00201 else none)) else (if id < 203 then (if id = 202 then some localCycle00202 else none) else (if id = 203 then some localCycle00203 else none)))) else (if id < 208 then (if id < 206 then (if id < 205 then (if id = 204 then some localCycle00204 else none) else (if id = 205 then some localCycle00205 else none)) else (if id < 207 then (if id = 206 then some localCycle00206 else none) else (if id = 207 then some localCycle00207 else none))) else (if id < 210 then (if id < 209 then (if id = 208 then some localCycle00208 else none) else (if id = 209 then some localCycle00209 else none)) else (if id < 211 then (if id = 210 then some localCycle00210 else none) else (if id = 211 then some localCycle00211 else none)))))) else (if id < 227 then (if id < 219 then (if id < 215 then (if id < 213 then (if id = 212 then some localCycle00212 else none) else (if id < 214 then (if id = 213 then some localCycle00213 else none) else (if id = 214 then some localCycle00214 else none))) else (if id < 217 then (if id < 216 then (if id = 215 then some localCycle00215 else none) else (if id = 216 then some localCycle00216 else none)) else (if id < 218 then (if id = 217 then some localCycle00217 else none) else (if id = 218 then some localCycle00218 else none)))) else (if id < 223 then (if id < 221 then (if id < 220 then (if id = 219 then some localCycle00219 else none) else (if id = 220 then some localCycle00220 else none)) else (if id < 222 then (if id = 221 then some localCycle00221 else none) else (if id = 222 then some localCycle00222 else none))) else (if id < 225 then (if id < 224 then (if id = 223 then some localCycle00223 else none) else (if id = 224 then some localCycle00224 else none)) else (if id < 226 then (if id = 225 then some localCycle00225 else none) else (if id = 226 then some localCycle00226 else none))))) else (if id < 235 then (if id < 231 then (if id < 229 then (if id < 228 then (if id = 227 then some localCycle00227 else none) else (if id = 228 then some localCycle00228 else none)) else (if id < 230 then (if id = 229 then some localCycle00229 else none) else (if id = 230 then some localCycle00230 else none))) else (if id < 233 then (if id < 232 then (if id = 231 then some localCycle00231 else none) else (if id = 232 then some localCycle00232 else none)) else (if id < 234 then (if id = 233 then some localCycle00233 else none) else (if id = 234 then some localCycle00234 else none)))) else (if id < 239 then (if id < 237 then (if id < 236 then (if id = 235 then some localCycle00235 else none) else (if id = 236 then some localCycle00236 else none)) else (if id < 238 then (if id = 237 then some localCycle00237 else none) else (if id = 238 then some localCycle00238 else none))) else (if id < 241 then (if id < 240 then (if id = 239 then some localCycle00239 else none) else (if id = 240 then some localCycle00240 else none)) else (if id < 242 then (if id = 241 then some localCycle00241 else none) else (if id = 242 then some localCycle00242 else none))))))))

def namedLeaf000 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 2, 6, 5, 4, 3], ![0, 1, 6, 5, 4, 3], ![0, 6, 4, 5, 1, 2], ![0, 6, 3, 5, 1, 2], ![0, 6, 3, 4, 1, 2], ![0, 5, 4, 3, 1, 2]], proof := .tail 50 }

theorem namedLeaf000_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 256)) namedLeaf000 = true :=
  by decide +kernel

def namedLeaf001 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 2, 5, 4, 6, 3], ![0, 1, 5, 4, 6, 3], ![0, 5, 4, 6, 1, 2], ![0, 5, 3, 1, 2, 6], ![0, 4, 3, 1, 2, 6], ![0, 3, 1, 2, 4, 5]], proof := .low (![126, 103, 101, 13, 153, 219, 111, 57, 184, 125, 64, 46, 52, 180, 205, 122, 232, 28, 147, 201, 82, 173, 236, 17, 137, 215, 165, 90]) }

theorem namedLeaf001_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 257)) namedLeaf001 = true :=
  by decide +kernel

def namedLeaf002 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 2, 5, 4, 6, 3], ![0, 1, 5, 6, 4, 3], ![0, 5, 4, 6, 1, 2], ![0, 5, 3, 1, 6, 2], ![0, 4, 3, 1, 2, 6], ![0, 3, 1, 4, 2, 5]], proof := .tail 168 }

theorem namedLeaf002_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 258)) namedLeaf002 = true :=
  by decide +kernel

def namedLeaf003 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 2, 5, 4, 6, 3], ![0, 1, 6, 5, 4, 3], ![0, 5, 4, 6, 1, 2], ![0, 5, 3, 1, 6, 2], ![0, 4, 3, 1, 6, 2], ![0, 3, 1, 4, 5, 2]], proof := .tail 120 }

theorem namedLeaf003_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 259)) namedLeaf003 = true :=
  by decide +kernel

def namedLeaf004 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 2, 5, 6, 4, 3], ![0, 1, 5, 6, 4, 3], ![0, 5, 4, 6, 1, 2], ![0, 5, 3, 6, 1, 2], ![0, 4, 3, 1, 2, 6], ![0, 3, 4, 1, 2, 5]], proof := .tail 241 }

theorem namedLeaf004_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 260)) namedLeaf004 = true :=
  by decide +kernel

def namedLeaf005 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 2, 5, 6, 4, 3], ![0, 1, 6, 5, 4, 3], ![0, 5, 4, 6, 1, 2], ![0, 5, 3, 6, 1, 2], ![0, 4, 3, 1, 6, 2], ![0, 3, 4, 1, 5, 2]], proof := .tail 154 }

theorem namedLeaf005_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 261)) namedLeaf005 = true :=
  by decide +kernel

def namedLeaf006 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 2, 6, 5, 4, 3], ![0, 1, 6, 5, 4, 3], ![0, 5, 4, 6, 1, 2], ![0, 5, 3, 6, 1, 2], ![0, 4, 3, 6, 1, 2], ![0, 3, 4, 5, 1, 2]], proof := .tail 167 }

theorem namedLeaf006_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 262)) namedLeaf006 = true :=
  by decide +kernel

def namedLeaf007 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 2, 5, 6, 4, 3], ![0, 1, 5, 6, 4, 3], ![0, 5, 6, 4, 1, 2], ![0, 5, 6, 3, 1, 2], ![0, 4, 3, 1, 2, 6], ![0, 4, 3, 1, 2, 5]], proof := .low (![32, 85, 101, 42, 145, 190, 181, 171, 184, 207, 68, 169, 10, 76, 129, 119, 193, 121, 117, 191, 229, 166, 34, 136, 96, 135, 151, 188]) }

theorem namedLeaf007_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 263)) namedLeaf007 = true :=
  by decide +kernel

def namedLeaf008 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 2, 5, 6, 4, 3], ![0, 1, 6, 5, 4, 3], ![0, 5, 6, 4, 1, 2], ![0, 5, 6, 3, 1, 2], ![0, 4, 3, 1, 6, 2], ![0, 4, 3, 1, 5, 2]], proof := .low (![155, 142, 23, 43, 145, 190, 181, 2, 227, 185, 68, 169, 10, 54, 24, 119, 193, 87, 11, 146, 146, 146, 34, 136, 97, 135, 151, 188]) }

theorem namedLeaf008_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 264)) namedLeaf008 = true :=
  by decide +kernel

def namedLeaf009 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 2, 6, 5, 4, 3], ![0, 1, 6, 5, 4, 3], ![0, 5, 6, 4, 1, 2], ![0, 5, 6, 3, 1, 2], ![0, 4, 3, 6, 1, 2], ![0, 4, 3, 5, 1, 2]], proof := .low (![53, 128, 89, 35, 65, 190, 14, 26, 75, 211, 58, 72, 156, 148, 45, 217, 73, 105, 235, 217, 73, 130, 113, 150, 12, 79, 143, 140]) }

theorem namedLeaf009_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 265)) namedLeaf009 = true :=
  by decide +kernel

def namedLeaf010 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 2, 6, 5, 4, 3], ![0, 1, 6, 5, 4, 3], ![0, 6, 5, 4, 1, 2], ![0, 5, 6, 3, 1, 2], ![0, 4, 6, 3, 1, 2], ![0, 4, 5, 3, 1, 2]], proof := .tail 61 }

theorem namedLeaf010_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 266)) namedLeaf010 = true :=
  by decide +kernel

def namedLeaf011 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 2, 6, 5, 4, 3], ![0, 1, 6, 5, 4, 3], ![0, 6, 5, 4, 1, 2], ![0, 6, 5, 3, 1, 2], ![0, 6, 4, 3, 1, 2], ![0, 5, 4, 3, 1, 2]], proof := .tail 77 }

theorem namedLeaf011_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 267)) namedLeaf011 = true :=
  by decide +kernel

def namedLeaf012 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 6, 2, 3, 4, 5], ![0, 6, 1, 3, 4, 5], ![0, 6, 1, 2, 4, 5], ![0, 6, 1, 2, 3, 5], ![0, 6, 1, 2, 3, 4], ![0, 5, 4, 3, 2, 1]], proof := .tail 40 }

theorem namedLeaf012_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 268)) namedLeaf012 = true :=
  by decide +kernel

def namedLeaf013 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 6, 2, 3, 4, 5], ![0, 6, 1, 3, 4, 5], ![0, 6, 1, 2, 5, 4], ![0, 6, 1, 2, 5, 3], ![0, 6, 1, 2, 4, 3], ![0, 5, 4, 3, 2, 1]], proof := .tail 179 }

theorem namedLeaf013_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 269)) namedLeaf013 = true :=
  by decide +kernel

def namedLeaf014 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 6, 2, 3, 4, 5], ![0, 6, 1, 3, 5, 4], ![0, 6, 1, 2, 5, 4], ![0, 6, 1, 5, 2, 3], ![0, 6, 1, 4, 2, 3], ![0, 5, 4, 3, 2, 1]], proof := .tail 204 }

theorem namedLeaf014_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 270)) namedLeaf014 = true :=
  by decide +kernel

def namedLeaf015 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 6, 2, 3, 5, 4], ![0, 6, 1, 3, 5, 4], ![0, 6, 1, 2, 5, 4], ![0, 5, 6, 1, 2, 3], ![0, 4, 6, 1, 2, 3], ![0, 4, 5, 3, 2, 1]], proof := .tail 175 }

theorem namedLeaf015_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 271)) namedLeaf015 = true :=
  by decide +kernel

def namedLeaf016 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 6, 2, 3, 5, 4], ![0, 6, 1, 3, 5, 4], ![0, 6, 1, 2, 5, 4], ![0, 6, 5, 1, 2, 3], ![0, 6, 4, 1, 2, 3], ![0, 5, 4, 3, 2, 1]], proof := .tail 66 }

theorem namedLeaf016_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 272)) namedLeaf016 = true :=
  by decide +kernel

def namedLeaf017 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 6, 2, 3, 4, 5], ![0, 6, 1, 5, 3, 4], ![0, 6, 1, 5, 2, 4], ![0, 6, 1, 5, 2, 3], ![0, 6, 1, 4, 3, 2], ![0, 5, 4, 3, 2, 1]], proof := .tail 131 }

theorem namedLeaf017_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 273)) namedLeaf017 = true :=
  by decide +kernel

def namedLeaf018 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 6, 2, 3, 5, 4], ![0, 6, 1, 5, 3, 4], ![0, 6, 1, 5, 2, 4], ![0, 5, 6, 1, 2, 3], ![0, 4, 6, 1, 3, 2], ![0, 4, 5, 3, 2, 1]], proof := .tail 92 }

theorem namedLeaf018_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 274)) namedLeaf018 = true :=
  by decide +kernel

def namedLeaf019 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 6, 2, 3, 5, 4], ![0, 6, 1, 5, 3, 4], ![0, 6, 1, 5, 2, 4], ![0, 6, 5, 1, 2, 3], ![0, 6, 4, 1, 3, 2], ![0, 5, 4, 3, 2, 1]], proof := .tail 63 }

theorem namedLeaf019_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 275)) namedLeaf019 = true :=
  by decide +kernel

def namedLeaf020 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 6, 2, 5, 3, 4], ![0, 6, 1, 5, 3, 4], ![0, 5, 6, 1, 2, 4], ![0, 5, 6, 1, 2, 3], ![0, 4, 3, 6, 1, 2], ![0, 4, 3, 5, 2, 1]], proof := .tail 223 }

theorem namedLeaf020_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 276)) namedLeaf020 = true :=
  by decide +kernel

def namedLeaf021 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 6, 2, 5, 3, 4], ![0, 6, 1, 5, 3, 4], ![0, 6, 5, 1, 2, 4], ![0, 5, 6, 1, 2, 3], ![0, 4, 6, 3, 1, 2], ![0, 4, 5, 3, 2, 1]], proof := .tail 48 }

theorem namedLeaf021_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 277)) namedLeaf021 = true :=
  by decide +kernel

def namedLeaf022 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 6, 2, 5, 3, 4], ![0, 6, 1, 5, 3, 4], ![0, 6, 5, 1, 2, 4], ![0, 6, 5, 1, 2, 3], ![0, 6, 4, 3, 1, 2], ![0, 5, 4, 3, 2, 1]], proof := .tail 237 }

theorem namedLeaf022_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 278)) namedLeaf022 = true :=
  by decide +kernel

def namedLeaf023 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 6, 2, 3, 4, 5], ![0, 6, 1, 4, 3, 5], ![0, 6, 1, 4, 2, 5], ![0, 6, 1, 3, 2, 5], ![0, 6, 1, 2, 3, 4], ![0, 5, 4, 3, 2, 1]], proof := .tail 225 }

theorem namedLeaf023_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 279)) namedLeaf023 = true :=
  by decide +kernel

def namedLeaf024 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 6, 2, 3, 4, 5], ![0, 6, 1, 4, 5, 3], ![0, 6, 1, 4, 5, 2], ![0, 6, 1, 3, 2, 5], ![0, 6, 1, 3, 2, 4], ![0, 5, 4, 3, 2, 1]], proof := .tail 196 }

theorem namedLeaf024_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 280)) namedLeaf024 = true :=
  by decide +kernel

def namedLeaf025 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 6, 2, 3, 4, 5], ![0, 6, 1, 5, 4, 3], ![0, 6, 1, 4, 5, 2], ![0, 6, 1, 3, 5, 2], ![0, 6, 1, 3, 4, 2], ![0, 5, 4, 3, 2, 1]], proof := .tail 183 }

theorem namedLeaf025_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 281)) namedLeaf025 = true :=
  by decide +kernel

def namedLeaf026 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 6, 2, 3, 4, 5], ![0, 6, 1, 5, 4, 3], ![0, 6, 1, 5, 4, 2], ![0, 6, 1, 5, 3, 2], ![0, 6, 1, 4, 3, 2], ![0, 5, 4, 3, 2, 1]], proof := .tail 182 }

theorem namedLeaf026_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 282)) namedLeaf026 = true :=
  by decide +kernel

def namedLeaf027 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 6, 2, 3, 5, 4], ![0, 6, 1, 5, 4, 3], ![0, 6, 1, 5, 4, 2], ![0, 5, 6, 1, 3, 2], ![0, 4, 6, 1, 3, 2], ![0, 4, 5, 3, 2, 1]], proof := .tail 104 }

theorem namedLeaf027_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 283)) namedLeaf027 = true :=
  by decide +kernel

def namedLeaf028 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 6, 2, 3, 5, 4], ![0, 6, 1, 5, 4, 3], ![0, 6, 1, 5, 4, 2], ![0, 6, 5, 1, 3, 2], ![0, 6, 4, 1, 3, 2], ![0, 5, 4, 3, 2, 1]], proof := .tail 178 }

theorem namedLeaf028_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 284)) namedLeaf028 = true :=
  by decide +kernel

def namedLeaf029 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 6, 2, 5, 3, 4], ![0, 6, 1, 5, 4, 3], ![0, 5, 6, 1, 4, 2], ![0, 5, 6, 1, 3, 2], ![0, 4, 3, 6, 1, 2], ![0, 4, 3, 5, 2, 1]], proof := .tail 118 }

theorem namedLeaf029_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 285)) namedLeaf029 = true :=
  by decide +kernel

def namedLeaf030 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 6, 2, 5, 3, 4], ![0, 6, 1, 5, 4, 3], ![0, 6, 5, 1, 4, 2], ![0, 5, 6, 1, 3, 2], ![0, 4, 6, 3, 1, 2], ![0, 4, 5, 3, 2, 1]], proof := .tail 170 }

theorem namedLeaf030_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 286)) namedLeaf030 = true :=
  by decide +kernel

def namedLeaf031 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 6, 2, 5, 3, 4], ![0, 6, 1, 5, 4, 3], ![0, 6, 5, 1, 4, 2], ![0, 6, 5, 1, 3, 2], ![0, 6, 4, 3, 1, 2], ![0, 5, 4, 3, 2, 1]], proof := .tail 21 }

theorem namedLeaf031_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 287)) namedLeaf031 = true :=
  by decide +kernel

def namedLeaf032 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 6, 2, 4, 3, 5], ![0, 6, 1, 4, 3, 5], ![0, 4, 6, 1, 2, 5], ![0, 3, 6, 1, 2, 5], ![0, 6, 1, 2, 3, 4], ![0, 5, 3, 4, 2, 1]], proof := .tail 134 }

theorem namedLeaf032_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 288)) namedLeaf032 = true :=
  by decide +kernel

def namedLeaf033 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 6, 2, 4, 3, 5], ![0, 6, 1, 4, 5, 3], ![0, 4, 6, 1, 5, 2], ![0, 3, 6, 1, 2, 5], ![0, 6, 1, 3, 2, 4], ![0, 5, 3, 4, 2, 1]], proof := .tail 39 }

theorem namedLeaf033_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 289)) namedLeaf033 = true :=
  by decide +kernel

def namedLeaf034 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 6, 2, 4, 3, 5], ![0, 6, 1, 5, 4, 3], ![0, 4, 6, 1, 5, 2], ![0, 3, 6, 1, 5, 2], ![0, 6, 1, 3, 4, 2], ![0, 5, 3, 4, 2, 1]], proof := .tail 238 }

theorem namedLeaf034_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 290)) namedLeaf034 = true :=
  by decide +kernel

def namedLeaf035 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 6, 2, 4, 5, 3], ![0, 6, 1, 4, 5, 3], ![0, 4, 5, 6, 1, 2], ![0, 3, 6, 1, 2, 5], ![0, 3, 6, 1, 2, 4], ![0, 3, 5, 4, 2, 1]], proof := .tail 39 }

theorem namedLeaf035_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 291)) namedLeaf035 = true :=
  by decide +kernel

def namedLeaf036 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 6, 2, 4, 5, 3], ![0, 6, 1, 5, 4, 3], ![0, 4, 5, 6, 1, 2], ![0, 3, 6, 1, 5, 2], ![0, 3, 6, 1, 4, 2], ![0, 3, 5, 4, 2, 1]], proof := .tail 228 }

theorem namedLeaf036_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 292)) namedLeaf036 = true :=
  by decide +kernel

def namedLeaf037 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 6, 2, 5, 4, 3], ![0, 6, 1, 5, 4, 3], ![0, 4, 5, 6, 1, 2], ![0, 3, 5, 6, 1, 2], ![0, 3, 4, 6, 1, 2], ![0, 3, 4, 5, 2, 1]], proof := .tail 80 }

theorem namedLeaf037_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 293)) namedLeaf037 = true :=
  by decide +kernel

def namedLeaf038 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 6, 2, 5, 4, 3], ![0, 6, 1, 5, 4, 3], ![0, 4, 5, 6, 1, 2], ![0, 3, 6, 5, 1, 2], ![0, 3, 6, 4, 1, 2], ![0, 3, 5, 4, 2, 1]], proof := .tail 39 }

theorem namedLeaf038_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 294)) namedLeaf038 = true :=
  by decide +kernel

def namedLeaf039 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 6, 2, 5, 4, 3], ![0, 6, 1, 5, 4, 3], ![0, 5, 4, 6, 1, 2], ![0, 5, 3, 6, 1, 2], ![0, 4, 3, 6, 1, 2], ![0, 3, 4, 5, 2, 1]], proof := .tail 149 }

theorem namedLeaf039_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 295)) namedLeaf039 = true :=
  by decide +kernel

def namedLeaf040 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 6, 2, 4, 5, 3], ![0, 6, 1, 4, 5, 3], ![0, 4, 6, 5, 1, 2], ![0, 3, 6, 1, 2, 5], ![0, 6, 3, 1, 2, 4], ![0, 5, 3, 4, 2, 1]], proof := .tail 39 }

theorem namedLeaf040_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 296)) namedLeaf040 = true :=
  by decide +kernel

def namedLeaf041 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 6, 2, 4, 5, 3], ![0, 6, 1, 5, 4, 3], ![0, 4, 6, 5, 1, 2], ![0, 3, 6, 1, 5, 2], ![0, 6, 3, 1, 4, 2], ![0, 5, 3, 4, 2, 1]], proof := .tail 228 }

theorem namedLeaf041_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 297)) namedLeaf041 = true :=
  by decide +kernel

def namedLeaf042 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 6, 2, 5, 4, 3], ![0, 6, 1, 5, 4, 3], ![0, 4, 6, 5, 1, 2], ![0, 3, 6, 5, 1, 2], ![0, 6, 3, 4, 1, 2], ![0, 5, 3, 4, 2, 1]], proof := .tail 39 }

theorem namedLeaf042_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 298)) namedLeaf042 = true :=
  by decide +kernel

def namedLeaf043 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 6, 2, 4, 3, 5], ![0, 6, 1, 4, 3, 5], ![0, 6, 4, 1, 2, 5], ![0, 6, 3, 1, 2, 5], ![0, 6, 1, 2, 3, 4], ![0, 5, 4, 3, 2, 1]], proof := .tail 74 }

theorem namedLeaf043_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 299)) namedLeaf043 = true :=
  by decide +kernel

def namedLeaf044 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 6, 2, 4, 3, 5], ![0, 6, 1, 4, 5, 3], ![0, 6, 4, 1, 5, 2], ![0, 6, 3, 1, 2, 5], ![0, 6, 1, 3, 2, 4], ![0, 5, 4, 3, 2, 1]], proof := .tail 99 }

theorem namedLeaf044_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 300)) namedLeaf044 = true :=
  by decide +kernel

def namedLeaf045 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 6, 2, 4, 3, 5], ![0, 6, 1, 5, 4, 3], ![0, 6, 4, 1, 5, 2], ![0, 6, 3, 1, 5, 2], ![0, 6, 1, 3, 4, 2], ![0, 5, 4, 3, 2, 1]], proof := .tail 172 }

theorem namedLeaf045_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 301)) namedLeaf045 = true :=
  by decide +kernel

def namedLeaf046 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 6, 2, 5, 4, 3], ![0, 6, 1, 5, 4, 3], ![0, 5, 6, 4, 1, 2], ![0, 5, 6, 3, 1, 2], ![0, 4, 3, 6, 1, 2], ![0, 4, 3, 5, 2, 1]], proof := .tail 226 }

theorem namedLeaf046_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 302)) namedLeaf046 = true :=
  by decide +kernel

def namedLeaf047 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 6, 2, 4, 5, 3], ![0, 6, 1, 4, 5, 3], ![0, 6, 4, 5, 1, 2], ![0, 6, 3, 1, 2, 5], ![0, 6, 3, 1, 2, 4], ![0, 5, 4, 3, 2, 1]], proof := .tail 158 }

theorem namedLeaf047_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 303)) namedLeaf047 = true :=
  by decide +kernel

def namedLeaf048 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 6, 2, 4, 5, 3], ![0, 6, 1, 5, 4, 3], ![0, 6, 4, 5, 1, 2], ![0, 6, 3, 1, 5, 2], ![0, 6, 3, 1, 4, 2], ![0, 5, 4, 3, 2, 1]], proof := .tail 67 }

theorem namedLeaf048_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 304)) namedLeaf048 = true :=
  by decide +kernel

def namedLeaf049 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 6, 2, 5, 4, 3], ![0, 6, 1, 5, 4, 3], ![0, 6, 4, 5, 1, 2], ![0, 6, 3, 5, 1, 2], ![0, 6, 3, 4, 1, 2], ![0, 5, 4, 3, 2, 1]], proof := .tail 50 }

theorem namedLeaf049_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 305)) namedLeaf049 = true :=
  by decide +kernel

def namedLeaf050 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 6, 2, 5, 4, 3], ![0, 6, 1, 5, 4, 3], ![0, 6, 5, 4, 1, 2], ![0, 5, 6, 3, 1, 2], ![0, 4, 6, 3, 1, 2], ![0, 4, 5, 3, 2, 1]], proof := .tail 61 }

theorem namedLeaf050_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 306)) namedLeaf050 = true :=
  by decide +kernel

def namedLeaf051 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 6, 2, 5, 4, 3], ![0, 6, 1, 5, 4, 3], ![0, 6, 5, 4, 1, 2], ![0, 6, 5, 3, 1, 2], ![0, 6, 4, 3, 1, 2], ![0, 5, 4, 3, 2, 1]], proof := .tail 77 }

theorem namedLeaf051_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 307)) namedLeaf051 = true :=
  by decide +kernel

def namedLeaf052 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 5, 2, 3, 4, 6], ![0, 5, 1, 3, 4, 6], ![0, 5, 1, 2, 4, 6], ![0, 5, 1, 2, 3, 6], ![0, 4, 3, 2, 1, 6], ![0, 1, 2, 3, 4, 5]], proof := .tail 62 }

theorem namedLeaf052_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 308)) namedLeaf052 = true :=
  by decide +kernel

def namedLeaf053 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 5, 2, 3, 4, 6], ![0, 5, 1, 3, 4, 6], ![0, 5, 1, 2, 6, 4], ![0, 5, 1, 2, 6, 3], ![0, 4, 3, 2, 1, 6], ![0, 1, 2, 4, 3, 5]], proof := .tail 88 }

theorem namedLeaf053_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 309)) namedLeaf053 = true :=
  by decide +kernel

def namedLeaf054 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 5, 2, 3, 4, 6], ![0, 5, 1, 3, 6, 4], ![0, 5, 1, 2, 6, 4], ![0, 5, 1, 6, 2, 3], ![0, 4, 3, 2, 1, 6], ![0, 1, 4, 2, 3, 5]], proof := .tail 107 }

theorem namedLeaf054_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 310)) namedLeaf054 = true :=
  by decide +kernel

def namedLeaf055 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 5, 2, 3, 4, 6], ![0, 5, 1, 6, 3, 4], ![0, 5, 1, 6, 2, 4], ![0, 5, 1, 6, 2, 3], ![0, 4, 3, 2, 1, 6], ![0, 1, 4, 3, 2, 5]], proof := .tail 102 }

theorem namedLeaf055_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 311)) namedLeaf055 = true :=
  by decide +kernel

def namedLeaf056 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 5, 2, 3, 6, 4], ![0, 5, 1, 3, 6, 4], ![0, 5, 1, 2, 6, 4], ![0, 5, 6, 1, 2, 3], ![0, 4, 3, 2, 1, 6], ![0, 4, 1, 2, 3, 5]], proof := .tail 197 }

theorem namedLeaf056_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 312)) namedLeaf056 = true :=
  by decide +kernel

def namedLeaf057 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 5, 2, 3, 6, 4], ![0, 5, 1, 6, 3, 4], ![0, 5, 1, 6, 2, 4], ![0, 5, 6, 1, 2, 3], ![0, 4, 3, 2, 1, 6], ![0, 4, 1, 3, 2, 5]], proof := .tail 91 }

theorem namedLeaf057_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 313)) namedLeaf057 = true :=
  by decide +kernel

def namedLeaf058 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 5, 2, 6, 3, 4], ![0, 5, 1, 6, 3, 4], ![0, 5, 6, 1, 2, 4], ![0, 5, 6, 1, 2, 3], ![0, 4, 3, 2, 1, 6], ![0, 4, 3, 1, 2, 5]], proof := .tail 59 }

theorem namedLeaf058_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 314)) namedLeaf058 = true :=
  by decide +kernel

def namedLeaf059 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 5, 6, 2, 3, 4], ![0, 5, 6, 1, 3, 4], ![0, 5, 6, 1, 2, 4], ![0, 5, 6, 1, 2, 3], ![0, 4, 3, 2, 1, 6], ![0, 4, 3, 2, 1, 5]], proof := .tail 19 }

theorem namedLeaf059_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 315)) namedLeaf059 = true :=
  by decide +kernel

def namedLeaf060 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 6, 5, 2, 3, 4], ![0, 5, 6, 1, 3, 4], ![0, 5, 6, 1, 2, 4], ![0, 5, 6, 1, 2, 3], ![0, 4, 3, 2, 6, 1], ![0, 4, 3, 2, 5, 1]], proof := .tail 132 }

theorem namedLeaf060_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 316)) namedLeaf060 = true :=
  by decide +kernel

def namedLeaf061 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 6, 5, 2, 3, 4], ![0, 6, 5, 1, 3, 4], ![0, 5, 6, 1, 2, 4], ![0, 5, 6, 1, 2, 3], ![0, 4, 3, 6, 2, 1], ![0, 4, 3, 5, 2, 1]], proof := .tail 174 }

theorem namedLeaf061_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 317)) namedLeaf061 = true :=
  by decide +kernel

def namedLeaf062 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 6, 5, 2, 3, 4], ![0, 6, 5, 1, 3, 4], ![0, 6, 5, 1, 2, 4], ![0, 5, 6, 1, 2, 3], ![0, 4, 6, 3, 2, 1], ![0, 4, 5, 3, 2, 1]], proof := .tail 51 }

theorem namedLeaf062_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 318)) namedLeaf062 = true :=
  by decide +kernel

def namedLeaf063 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 6, 5, 2, 3, 4], ![0, 6, 5, 1, 3, 4], ![0, 6, 5, 1, 2, 4], ![0, 6, 5, 1, 2, 3], ![0, 6, 4, 3, 2, 1], ![0, 5, 4, 3, 2, 1]], proof := .tail 212 }

theorem namedLeaf063_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 319)) namedLeaf063 = true :=
  by decide +kernel

def namedLeaf064 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 5, 2, 3, 4, 6], ![0, 5, 1, 4, 3, 6], ![0, 5, 1, 4, 2, 6], ![0, 5, 1, 3, 2, 6], ![0, 4, 3, 2, 1, 6], ![0, 1, 2, 3, 4, 5]], proof := .tail 221 }

theorem namedLeaf064_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 320)) namedLeaf064 = true :=
  by decide +kernel

def namedLeaf065 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 5, 2, 3, 4, 6], ![0, 5, 1, 4, 6, 3], ![0, 5, 1, 4, 6, 2], ![0, 5, 1, 3, 2, 6], ![0, 4, 3, 2, 1, 6], ![0, 1, 3, 2, 4, 5]], proof := .tail 22 }

theorem namedLeaf065_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 321)) namedLeaf065 = true :=
  by decide +kernel

def namedLeaf066 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 5, 2, 3, 4, 6], ![0, 5, 1, 6, 4, 3], ![0, 5, 1, 4, 6, 2], ![0, 5, 1, 3, 6, 2], ![0, 4, 3, 2, 1, 6], ![0, 1, 3, 4, 2, 5]], proof := .tail 60 }

theorem namedLeaf066_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 322)) namedLeaf066 = true :=
  by decide +kernel

def namedLeaf067 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 5, 2, 3, 4, 6], ![0, 5, 1, 6, 4, 3], ![0, 5, 1, 6, 4, 2], ![0, 5, 1, 6, 3, 2], ![0, 4, 3, 2, 1, 6], ![0, 1, 4, 3, 2, 5]], proof := .tail 230 }

theorem namedLeaf067_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 323)) namedLeaf067 = true :=
  by decide +kernel

def namedLeaf068 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 5, 2, 3, 6, 4], ![0, 5, 1, 6, 4, 3], ![0, 5, 1, 6, 4, 2], ![0, 5, 6, 1, 3, 2], ![0, 4, 3, 2, 1, 6], ![0, 4, 1, 3, 2, 5]], proof := .tail 161 }

theorem namedLeaf068_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 324)) namedLeaf068 = true :=
  by decide +kernel

def namedLeaf069 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 5, 2, 6, 3, 4], ![0, 5, 1, 6, 4, 3], ![0, 5, 6, 1, 4, 2], ![0, 5, 6, 1, 3, 2], ![0, 4, 3, 2, 1, 6], ![0, 4, 3, 1, 2, 5]], proof := .tail 220 }

theorem namedLeaf069_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 325)) namedLeaf069 = true :=
  by decide +kernel

def namedLeaf070 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 5, 6, 2, 3, 4], ![0, 5, 6, 1, 4, 3], ![0, 5, 6, 1, 4, 2], ![0, 5, 6, 1, 3, 2], ![0, 4, 3, 2, 1, 6], ![0, 4, 3, 2, 1, 5]], proof := .tail 30 }

theorem namedLeaf070_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 326)) namedLeaf070 = true :=
  by decide +kernel

def namedLeaf071 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 6, 5, 2, 3, 4], ![0, 5, 6, 1, 4, 3], ![0, 5, 6, 1, 4, 2], ![0, 5, 6, 1, 3, 2], ![0, 4, 3, 2, 6, 1], ![0, 4, 3, 2, 5, 1]], proof := .tail 118 }

theorem namedLeaf071_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 327)) namedLeaf071 = true :=
  by decide +kernel

def namedLeaf072 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 6, 5, 2, 3, 4], ![0, 6, 5, 1, 4, 3], ![0, 5, 6, 1, 4, 2], ![0, 5, 6, 1, 3, 2], ![0, 4, 3, 6, 2, 1], ![0, 4, 3, 5, 2, 1]], proof := .tail 141 }

theorem namedLeaf072_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 328)) namedLeaf072 = true :=
  by decide +kernel

def namedLeaf073 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 6, 5, 2, 3, 4], ![0, 6, 5, 1, 4, 3], ![0, 6, 5, 1, 4, 2], ![0, 5, 6, 1, 3, 2], ![0, 4, 6, 3, 2, 1], ![0, 4, 5, 3, 2, 1]], proof := .tail 29 }

theorem namedLeaf073_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 329)) namedLeaf073 = true :=
  by decide +kernel

def namedLeaf074 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 6, 5, 2, 3, 4], ![0, 6, 5, 1, 4, 3], ![0, 6, 5, 1, 4, 2], ![0, 6, 5, 1, 3, 2], ![0, 6, 4, 3, 2, 1], ![0, 5, 4, 3, 2, 1]], proof := .tail 20 }

theorem namedLeaf074_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 330)) namedLeaf074 = true :=
  by decide +kernel

def namedLeaf075 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 5, 2, 4, 3, 6], ![0, 5, 1, 4, 3, 6], ![0, 4, 5, 1, 2, 6], ![0, 3, 5, 1, 2, 6], ![0, 3, 4, 2, 1, 6], ![0, 1, 2, 3, 4, 5]], proof := .tail 144 }

theorem namedLeaf075_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 331)) namedLeaf075 = true :=
  by decide +kernel

def namedLeaf076 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 5, 2, 4, 3, 6], ![0, 5, 1, 4, 6, 3], ![0, 4, 5, 1, 6, 2], ![0, 3, 5, 1, 2, 6], ![0, 3, 4, 2, 1, 6], ![0, 1, 3, 2, 4, 5]], proof := .tail 115 }

theorem namedLeaf076_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 332)) namedLeaf076 = true :=
  by decide +kernel

def namedLeaf077 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 5, 2, 4, 3, 6], ![0, 5, 1, 6, 4, 3], ![0, 4, 5, 1, 6, 2], ![0, 3, 5, 1, 6, 2], ![0, 3, 4, 2, 1, 6], ![0, 1, 3, 4, 2, 5]], proof := .tail 83 }

theorem namedLeaf077_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 333)) namedLeaf077 = true :=
  by decide +kernel

def namedLeaf078 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 5, 2, 4, 6, 3], ![0, 5, 1, 4, 6, 3], ![0, 4, 5, 6, 1, 2], ![0, 3, 5, 1, 2, 6], ![0, 3, 4, 2, 1, 6], ![0, 3, 1, 2, 4, 5]], proof := .tail 115 }

theorem namedLeaf078_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 334)) namedLeaf078 = true :=
  by decide +kernel

def namedLeaf079 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 5, 2, 4, 6, 3], ![0, 5, 1, 6, 4, 3], ![0, 4, 5, 6, 1, 2], ![0, 3, 5, 1, 6, 2], ![0, 3, 4, 2, 1, 6], ![0, 3, 1, 4, 2, 5]], proof := .tail 224 }

theorem namedLeaf079_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 335)) namedLeaf079 = true :=
  by decide +kernel

def namedLeaf080 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 5, 2, 6, 4, 3], ![0, 5, 1, 6, 4, 3], ![0, 4, 5, 6, 1, 2], ![0, 3, 5, 6, 1, 2], ![0, 3, 4, 2, 1, 6], ![0, 3, 4, 1, 2, 5]], proof := .tail 208 }

theorem namedLeaf080_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 336)) namedLeaf080 = true :=
  by decide +kernel

def namedLeaf081 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 5, 6, 2, 4, 3], ![0, 5, 6, 1, 4, 3], ![0, 4, 5, 6, 1, 2], ![0, 3, 5, 6, 1, 2], ![0, 3, 4, 2, 1, 6], ![0, 3, 4, 2, 1, 5]], proof := .tail 0 }

theorem namedLeaf081_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 337)) namedLeaf081 = true :=
  by decide +kernel

def namedLeaf082 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 6, 5, 2, 4, 3], ![0, 5, 6, 1, 4, 3], ![0, 4, 5, 6, 1, 2], ![0, 3, 5, 6, 1, 2], ![0, 3, 4, 2, 6, 1], ![0, 3, 4, 2, 5, 1]], proof := .tail 152 }

theorem namedLeaf082_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 338)) namedLeaf082 = true :=
  by decide +kernel

def namedLeaf083 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 6, 5, 2, 4, 3], ![0, 6, 5, 1, 4, 3], ![0, 4, 5, 6, 1, 2], ![0, 3, 5, 6, 1, 2], ![0, 3, 4, 6, 2, 1], ![0, 3, 4, 5, 2, 1]], proof := .tail 109 }

theorem namedLeaf083_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 339)) namedLeaf083 = true :=
  by decide +kernel

def namedLeaf084 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 6, 5, 2, 4, 3], ![0, 6, 5, 1, 4, 3], ![0, 4, 5, 6, 1, 2], ![0, 3, 6, 5, 1, 2], ![0, 3, 6, 4, 2, 1], ![0, 3, 5, 4, 2, 1]], proof := .tail 98 }

theorem namedLeaf084_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 340)) namedLeaf084 = true :=
  by decide +kernel

def namedLeaf085 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 6, 5, 2, 4, 3], ![0, 6, 5, 1, 4, 3], ![0, 4, 6, 5, 1, 2], ![0, 3, 6, 5, 1, 2], ![0, 6, 3, 4, 2, 1], ![0, 5, 3, 4, 2, 1]], proof := .tail 115 }

theorem namedLeaf085_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 341)) namedLeaf085 = true :=
  by decide +kernel

def namedLeaf086 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 6, 5, 2, 4, 3], ![0, 6, 5, 1, 4, 3], ![0, 6, 4, 5, 1, 2], ![0, 6, 3, 5, 1, 2], ![0, 6, 3, 4, 2, 1], ![0, 5, 4, 3, 2, 1]], proof := .tail 9 }

theorem namedLeaf086_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 342)) namedLeaf086 = true :=
  by decide +kernel

def namedLeaf087 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 5, 2, 4, 3, 6], ![0, 5, 1, 4, 3, 6], ![0, 5, 4, 1, 2, 6], ![0, 5, 3, 1, 2, 6], ![0, 4, 3, 2, 1, 6], ![0, 1, 2, 3, 4, 5]], proof := .tail 3 }

theorem namedLeaf087_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 343)) namedLeaf087 = true :=
  by decide +kernel

def namedLeaf088 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 5, 2, 4, 3, 6], ![0, 5, 1, 4, 6, 3], ![0, 5, 4, 1, 6, 2], ![0, 5, 3, 1, 2, 6], ![0, 4, 3, 2, 1, 6], ![0, 1, 3, 2, 4, 5]], proof := .tail 116 }

theorem namedLeaf088_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 344)) namedLeaf088 = true :=
  by decide +kernel

def namedLeaf089 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 5, 2, 4, 3, 6], ![0, 5, 1, 6, 4, 3], ![0, 5, 4, 1, 6, 2], ![0, 5, 3, 1, 6, 2], ![0, 4, 3, 2, 1, 6], ![0, 1, 3, 4, 2, 5]], proof := .tail 214 }

theorem namedLeaf089_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 345)) namedLeaf089 = true :=
  by decide +kernel

def namedLeaf090 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 5, 2, 4, 6, 3], ![0, 5, 1, 4, 6, 3], ![0, 5, 4, 6, 1, 2], ![0, 5, 3, 1, 2, 6], ![0, 4, 3, 2, 1, 6], ![0, 3, 1, 2, 4, 5]], proof := .tail 160 }

theorem namedLeaf090_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 346)) namedLeaf090 = true :=
  by decide +kernel

def namedLeaf091 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 5, 2, 4, 6, 3], ![0, 5, 1, 6, 4, 3], ![0, 5, 4, 6, 1, 2], ![0, 5, 3, 1, 6, 2], ![0, 4, 3, 2, 1, 6], ![0, 3, 1, 4, 2, 5]], proof := .tail 49 }

theorem namedLeaf091_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 347)) namedLeaf091 = true :=
  by decide +kernel

def namedLeaf092 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 5, 2, 6, 4, 3], ![0, 5, 1, 6, 4, 3], ![0, 5, 4, 6, 1, 2], ![0, 5, 3, 6, 1, 2], ![0, 4, 3, 2, 1, 6], ![0, 3, 4, 1, 2, 5]], proof := .tail 241 }

theorem namedLeaf092_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 348)) namedLeaf092 = true :=
  by decide +kernel

def namedLeaf093 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 5, 2, 6, 4, 3], ![0, 5, 1, 6, 4, 3], ![0, 5, 6, 4, 1, 2], ![0, 5, 6, 3, 1, 2], ![0, 4, 3, 2, 1, 6], ![0, 4, 3, 1, 2, 5]], proof := .low (![70, 55, 133, 233, 162, 190, 181, 4, 108, 41, 5, 36, 10, 202, 206, 177, 69, 112, 218, 202, 202, 202, 124, 15, 86, 186, 189, 210]) }

theorem namedLeaf093_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 349)) namedLeaf093 = true :=
  by decide +kernel

def namedLeaf094 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 5, 6, 2, 4, 3], ![0, 5, 6, 1, 4, 3], ![0, 5, 4, 6, 1, 2], ![0, 5, 3, 6, 1, 2], ![0, 4, 3, 2, 1, 6], ![0, 3, 4, 2, 1, 5]], proof := .tail 39 }

theorem namedLeaf094_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 350)) namedLeaf094 = true :=
  by decide +kernel

def namedLeaf095 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 6, 5, 2, 4, 3], ![0, 5, 6, 1, 4, 3], ![0, 5, 4, 6, 1, 2], ![0, 5, 3, 6, 1, 2], ![0, 4, 3, 2, 6, 1], ![0, 3, 4, 2, 5, 1]], proof := .tail 159 }

theorem namedLeaf095_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 351)) namedLeaf095 = true :=
  by decide +kernel

def namedLeaf096 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 6, 5, 2, 4, 3], ![0, 6, 5, 1, 4, 3], ![0, 5, 4, 6, 1, 2], ![0, 5, 3, 6, 1, 2], ![0, 4, 3, 6, 2, 1], ![0, 3, 4, 5, 2, 1]], proof := .tail 141 }

theorem namedLeaf096_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 352)) namedLeaf096 = true :=
  by decide +kernel

def namedLeaf097 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 5, 6, 2, 4, 3], ![0, 5, 6, 1, 4, 3], ![0, 5, 6, 4, 1, 2], ![0, 5, 6, 3, 1, 2], ![0, 4, 3, 2, 1, 6], ![0, 4, 3, 2, 1, 5]], proof := .low (![110, 18, 93, 216, 78, 190, 181, 114, 8, 163, 242, 36, 10, 6, 187, 95, 194, 112, 56, 231, 106, 176, 222, 84, 157, 100, 27, 31]) }

theorem namedLeaf097_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 353)) namedLeaf097 = true :=
  by decide +kernel

def namedLeaf098 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 6, 5, 2, 4, 3], ![0, 5, 6, 1, 4, 3], ![0, 5, 6, 4, 1, 2], ![0, 5, 6, 3, 1, 2], ![0, 4, 3, 2, 6, 1], ![0, 4, 3, 2, 5, 1]], proof := .tail 213 }

theorem namedLeaf098_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 354)) namedLeaf098 = true :=
  by decide +kernel

def namedLeaf099 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 6, 5, 2, 4, 3], ![0, 6, 5, 1, 4, 3], ![0, 5, 6, 4, 1, 2], ![0, 5, 6, 3, 1, 2], ![0, 4, 3, 6, 2, 1], ![0, 4, 3, 5, 2, 1]], proof := .tail 141 }

theorem namedLeaf099_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 355)) namedLeaf099 = true :=
  by decide +kernel

def namedLeaf100 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 6, 5, 2, 4, 3], ![0, 6, 5, 1, 4, 3], ![0, 6, 5, 4, 1, 2], ![0, 5, 6, 3, 1, 2], ![0, 4, 6, 3, 2, 1], ![0, 4, 5, 3, 2, 1]], proof := .tail 139 }

theorem namedLeaf100_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 356)) namedLeaf100 = true :=
  by decide +kernel

def namedLeaf101 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 6, 5, 2, 4, 3], ![0, 6, 5, 1, 4, 3], ![0, 6, 5, 4, 1, 2], ![0, 6, 5, 3, 1, 2], ![0, 6, 4, 3, 2, 1], ![0, 5, 4, 3, 2, 1]], proof := .tail 200 }

theorem namedLeaf101_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 357)) namedLeaf101 = true :=
  by decide +kernel

def namedLeaf102 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 4, 2, 3, 5, 6], ![0, 4, 1, 3, 5, 6], ![0, 4, 1, 2, 5, 6], ![0, 3, 2, 1, 5, 6], ![0, 1, 2, 3, 4, 6], ![0, 1, 2, 3, 4, 5]], proof := .tail 203 }

theorem namedLeaf102_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 358)) namedLeaf102 = true :=
  by decide +kernel

def namedLeaf103 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 4, 2, 3, 5, 6], ![0, 4, 1, 3, 5, 6], ![0, 4, 1, 2, 5, 6], ![0, 3, 2, 1, 6, 5], ![0, 1, 2, 3, 6, 4], ![0, 1, 2, 3, 5, 4]], proof := .tail 25 }

theorem namedLeaf103_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 359)) namedLeaf103 = true :=
  by decide +kernel

def namedLeaf104 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 4, 2, 3, 5, 6], ![0, 4, 1, 3, 5, 6], ![0, 4, 1, 2, 6, 5], ![0, 3, 2, 1, 6, 5], ![0, 1, 2, 6, 3, 4], ![0, 1, 2, 5, 3, 4]], proof := .tail 198 }

theorem namedLeaf104_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 360)) namedLeaf104 = true :=
  by decide +kernel

def namedLeaf105 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 4, 2, 3, 5, 6], ![0, 4, 1, 3, 6, 5], ![0, 4, 1, 2, 6, 5], ![0, 3, 2, 1, 6, 5], ![0, 1, 6, 2, 3, 4], ![0, 1, 5, 2, 3, 4]], proof := .tail 239 }

theorem namedLeaf105_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 361)) namedLeaf105 = true :=
  by decide +kernel

def namedLeaf106 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 4, 2, 3, 6, 5], ![0, 4, 1, 3, 6, 5], ![0, 4, 1, 2, 6, 5], ![0, 3, 2, 1, 6, 5], ![0, 6, 1, 2, 3, 4], ![0, 5, 1, 2, 3, 4]], proof := .tail 239 }

theorem namedLeaf106_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 362)) namedLeaf106 = true :=
  by decide +kernel

def namedLeaf107 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 4, 2, 3, 5, 6], ![0, 4, 1, 6, 3, 5], ![0, 4, 1, 6, 2, 5], ![0, 3, 2, 1, 6, 5], ![0, 1, 6, 2, 3, 4], ![0, 1, 5, 3, 2, 4]], proof := .tail 199 }

theorem namedLeaf107_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 363)) namedLeaf107 = true :=
  by decide +kernel

def namedLeaf108 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 4, 2, 3, 6, 5], ![0, 4, 1, 6, 3, 5], ![0, 4, 1, 6, 2, 5], ![0, 3, 2, 1, 6, 5], ![0, 6, 1, 2, 3, 4], ![0, 5, 1, 3, 2, 4]], proof := .tail 1 }

theorem namedLeaf108_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 364)) namedLeaf108 = true :=
  by decide +kernel

def namedLeaf109 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 4, 2, 6, 3, 5], ![0, 4, 1, 6, 3, 5], ![0, 4, 6, 1, 2, 5], ![0, 3, 2, 1, 6, 5], ![0, 6, 1, 2, 3, 4], ![0, 5, 3, 1, 2, 4]], proof := .tail 38 }

theorem namedLeaf109_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 365)) namedLeaf109 = true :=
  by decide +kernel

def namedLeaf110 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 4, 6, 2, 3, 5], ![0, 4, 6, 1, 3, 5], ![0, 4, 6, 1, 2, 5], ![0, 3, 2, 1, 6, 5], ![0, 6, 1, 2, 3, 4], ![0, 5, 3, 2, 1, 4]], proof := .tail 37 }

theorem namedLeaf110_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 366)) namedLeaf110 = true :=
  by decide +kernel

def namedLeaf111 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 6, 4, 2, 3, 5], ![0, 4, 6, 1, 3, 5], ![0, 4, 6, 1, 2, 5], ![0, 3, 2, 6, 1, 5], ![0, 6, 1, 2, 3, 4], ![0, 5, 3, 2, 4, 1]], proof := .tail 71 }

theorem namedLeaf111_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 367)) namedLeaf111 = true :=
  by decide +kernel

def namedLeaf112 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 6, 4, 2, 3, 5], ![0, 6, 4, 1, 3, 5], ![0, 4, 6, 1, 2, 5], ![0, 3, 6, 2, 1, 5], ![0, 6, 1, 2, 3, 4], ![0, 5, 3, 4, 2, 1]], proof := .tail 81 }

theorem namedLeaf112_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 368)) namedLeaf112 = true :=
  by decide +kernel

def namedLeaf113 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 6, 4, 2, 3, 5], ![0, 6, 4, 1, 3, 5], ![0, 6, 4, 1, 2, 5], ![0, 6, 3, 2, 1, 5], ![0, 6, 1, 2, 3, 4], ![0, 5, 4, 3, 2, 1]], proof := .tail 192 }

theorem namedLeaf113_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 369)) namedLeaf113 = true :=
  by decide +kernel

def namedLeaf114 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 4, 2, 3, 5, 6], ![0, 4, 1, 5, 3, 6], ![0, 4, 1, 5, 2, 6], ![0, 3, 2, 1, 5, 6], ![0, 1, 3, 2, 4, 6], ![0, 1, 2, 3, 4, 5]], proof := .tail 44 }

theorem namedLeaf114_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 370)) namedLeaf114 = true :=
  by decide +kernel

def namedLeaf115 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 4, 2, 3, 5, 6], ![0, 4, 1, 5, 3, 6], ![0, 4, 1, 5, 2, 6], ![0, 3, 2, 1, 6, 5], ![0, 1, 3, 2, 6, 4], ![0, 1, 2, 3, 5, 4]], proof := .tail 209 }

theorem namedLeaf115_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 371)) namedLeaf115 = true :=
  by decide +kernel

def namedLeaf116 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 4, 2, 3, 5, 6], ![0, 4, 1, 5, 6, 3], ![0, 4, 1, 5, 6, 2], ![0, 3, 2, 1, 5, 6], ![0, 1, 3, 2, 4, 6], ![0, 1, 3, 2, 4, 5]], proof := .tail 16 }

theorem namedLeaf116_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 372)) namedLeaf116 = true :=
  by decide +kernel

def namedLeaf117 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 4, 2, 3, 5, 6], ![0, 4, 1, 5, 6, 3], ![0, 4, 1, 5, 6, 2], ![0, 3, 2, 1, 6, 5], ![0, 1, 3, 2, 6, 4], ![0, 1, 3, 2, 5, 4]], proof := .tail 47 }

theorem namedLeaf117_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 373)) namedLeaf117 = true :=
  by decide +kernel

def namedLeaf118 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 4, 2, 3, 5, 6], ![0, 4, 1, 6, 5, 3], ![0, 4, 1, 5, 6, 2], ![0, 3, 2, 1, 6, 5], ![0, 1, 3, 6, 2, 4], ![0, 1, 3, 5, 2, 4]], proof := .tail 240 }

theorem namedLeaf118_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 374)) namedLeaf118 = true :=
  by decide +kernel

def namedLeaf119 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 4, 2, 3, 5, 6], ![0, 4, 1, 6, 5, 3], ![0, 4, 1, 6, 5, 2], ![0, 3, 2, 1, 6, 5], ![0, 1, 6, 3, 2, 4], ![0, 1, 5, 3, 2, 4]], proof := .tail 123 }

theorem namedLeaf119_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 375)) namedLeaf119 = true :=
  by decide +kernel

def namedLeaf120 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 4, 2, 3, 6, 5], ![0, 4, 1, 6, 5, 3], ![0, 4, 1, 6, 5, 2], ![0, 3, 2, 1, 6, 5], ![0, 6, 1, 3, 2, 4], ![0, 5, 1, 3, 2, 4]], proof := .tail 234 }

theorem namedLeaf120_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 376)) namedLeaf120 = true :=
  by decide +kernel

def namedLeaf121 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 4, 2, 6, 3, 5], ![0, 4, 1, 6, 5, 3], ![0, 4, 6, 1, 5, 2], ![0, 3, 2, 1, 6, 5], ![0, 6, 1, 3, 2, 4], ![0, 5, 3, 1, 2, 4]], proof := .tail 127 }

theorem namedLeaf121_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 377)) namedLeaf121 = true :=
  by decide +kernel

def namedLeaf122 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 4, 6, 2, 3, 5], ![0, 4, 6, 1, 5, 3], ![0, 4, 6, 1, 5, 2], ![0, 3, 2, 1, 6, 5], ![0, 6, 1, 3, 2, 4], ![0, 5, 3, 2, 1, 4]], proof := .tail 7 }

theorem namedLeaf122_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 378)) namedLeaf122 = true :=
  by decide +kernel

def namedLeaf123 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 6, 4, 2, 3, 5], ![0, 4, 6, 1, 5, 3], ![0, 4, 6, 1, 5, 2], ![0, 3, 2, 6, 1, 5], ![0, 6, 1, 3, 2, 4], ![0, 5, 3, 2, 4, 1]], proof := .tail 195 }

theorem namedLeaf123_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 379)) namedLeaf123 = true :=
  by decide +kernel

def namedLeaf124 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 6, 4, 2, 3, 5], ![0, 6, 4, 1, 5, 3], ![0, 4, 6, 1, 5, 2], ![0, 3, 6, 2, 1, 5], ![0, 6, 1, 3, 2, 4], ![0, 5, 3, 4, 2, 1]], proof := .tail 164 }

theorem namedLeaf124_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 380)) namedLeaf124 = true :=
  by decide +kernel

def namedLeaf125 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 6, 4, 2, 3, 5], ![0, 6, 4, 1, 5, 3], ![0, 6, 4, 1, 5, 2], ![0, 6, 3, 2, 1, 5], ![0, 6, 1, 3, 2, 4], ![0, 5, 4, 3, 2, 1]], proof := .tail 94 }

theorem namedLeaf125_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 381)) namedLeaf125 = true :=
  by decide +kernel

def namedLeaf126 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 4, 2, 5, 3, 6], ![0, 4, 1, 5, 3, 6], ![0, 4, 5, 1, 2, 6], ![0, 3, 2, 1, 5, 6], ![0, 3, 1, 2, 4, 6], ![0, 1, 2, 3, 4, 5]], proof := .tail 33 }

theorem namedLeaf126_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 382)) namedLeaf126 = true :=
  by decide +kernel

def namedLeaf127 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 4, 2, 5, 3, 6], ![0, 4, 1, 5, 3, 6], ![0, 4, 5, 1, 2, 6], ![0, 3, 2, 1, 6, 5], ![0, 3, 1, 2, 6, 4], ![0, 1, 2, 3, 5, 4]], proof := .tail 138 }

theorem namedLeaf127_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 383)) namedLeaf127 = true :=
  by decide +kernel

def fallback : LeafData := { rows := fun _ _ => 0, proof := .tail 0 }
def lookup (offset : ℕ) : LeafData :=
  if offset < 128 then (if offset < 64 then (if offset < 32 then (if offset < 16 then (if offset < 8 then (if offset < 4 then (if offset < 2 then (if offset < 1 then (namedLeaf000) else (namedLeaf001)) else (if offset < 3 then (namedLeaf002) else (namedLeaf003))) else (if offset < 6 then (if offset < 5 then (namedLeaf004) else (namedLeaf005)) else (if offset < 7 then (namedLeaf006) else (namedLeaf007)))) else (if offset < 12 then (if offset < 10 then (if offset < 9 then (namedLeaf008) else (namedLeaf009)) else (if offset < 11 then (namedLeaf010) else (namedLeaf011))) else (if offset < 14 then (if offset < 13 then (namedLeaf012) else (namedLeaf013)) else (if offset < 15 then (namedLeaf014) else (namedLeaf015))))) else (if offset < 24 then (if offset < 20 then (if offset < 18 then (if offset < 17 then (namedLeaf016) else (namedLeaf017)) else (if offset < 19 then (namedLeaf018) else (namedLeaf019))) else (if offset < 22 then (if offset < 21 then (namedLeaf020) else (namedLeaf021)) else (if offset < 23 then (namedLeaf022) else (namedLeaf023)))) else (if offset < 28 then (if offset < 26 then (if offset < 25 then (namedLeaf024) else (namedLeaf025)) else (if offset < 27 then (namedLeaf026) else (namedLeaf027))) else (if offset < 30 then (if offset < 29 then (namedLeaf028) else (namedLeaf029)) else (if offset < 31 then (namedLeaf030) else (namedLeaf031)))))) else (if offset < 48 then (if offset < 40 then (if offset < 36 then (if offset < 34 then (if offset < 33 then (namedLeaf032) else (namedLeaf033)) else (if offset < 35 then (namedLeaf034) else (namedLeaf035))) else (if offset < 38 then (if offset < 37 then (namedLeaf036) else (namedLeaf037)) else (if offset < 39 then (namedLeaf038) else (namedLeaf039)))) else (if offset < 44 then (if offset < 42 then (if offset < 41 then (namedLeaf040) else (namedLeaf041)) else (if offset < 43 then (namedLeaf042) else (namedLeaf043))) else (if offset < 46 then (if offset < 45 then (namedLeaf044) else (namedLeaf045)) else (if offset < 47 then (namedLeaf046) else (namedLeaf047))))) else (if offset < 56 then (if offset < 52 then (if offset < 50 then (if offset < 49 then (namedLeaf048) else (namedLeaf049)) else (if offset < 51 then (namedLeaf050) else (namedLeaf051))) else (if offset < 54 then (if offset < 53 then (namedLeaf052) else (namedLeaf053)) else (if offset < 55 then (namedLeaf054) else (namedLeaf055)))) else (if offset < 60 then (if offset < 58 then (if offset < 57 then (namedLeaf056) else (namedLeaf057)) else (if offset < 59 then (namedLeaf058) else (namedLeaf059))) else (if offset < 62 then (if offset < 61 then (namedLeaf060) else (namedLeaf061)) else (if offset < 63 then (namedLeaf062) else (namedLeaf063))))))) else (if offset < 96 then (if offset < 80 then (if offset < 72 then (if offset < 68 then (if offset < 66 then (if offset < 65 then (namedLeaf064) else (namedLeaf065)) else (if offset < 67 then (namedLeaf066) else (namedLeaf067))) else (if offset < 70 then (if offset < 69 then (namedLeaf068) else (namedLeaf069)) else (if offset < 71 then (namedLeaf070) else (namedLeaf071)))) else (if offset < 76 then (if offset < 74 then (if offset < 73 then (namedLeaf072) else (namedLeaf073)) else (if offset < 75 then (namedLeaf074) else (namedLeaf075))) else (if offset < 78 then (if offset < 77 then (namedLeaf076) else (namedLeaf077)) else (if offset < 79 then (namedLeaf078) else (namedLeaf079))))) else (if offset < 88 then (if offset < 84 then (if offset < 82 then (if offset < 81 then (namedLeaf080) else (namedLeaf081)) else (if offset < 83 then (namedLeaf082) else (namedLeaf083))) else (if offset < 86 then (if offset < 85 then (namedLeaf084) else (namedLeaf085)) else (if offset < 87 then (namedLeaf086) else (namedLeaf087)))) else (if offset < 92 then (if offset < 90 then (if offset < 89 then (namedLeaf088) else (namedLeaf089)) else (if offset < 91 then (namedLeaf090) else (namedLeaf091))) else (if offset < 94 then (if offset < 93 then (namedLeaf092) else (namedLeaf093)) else (if offset < 95 then (namedLeaf094) else (namedLeaf095)))))) else (if offset < 112 then (if offset < 104 then (if offset < 100 then (if offset < 98 then (if offset < 97 then (namedLeaf096) else (namedLeaf097)) else (if offset < 99 then (namedLeaf098) else (namedLeaf099))) else (if offset < 102 then (if offset < 101 then (namedLeaf100) else (namedLeaf101)) else (if offset < 103 then (namedLeaf102) else (namedLeaf103)))) else (if offset < 108 then (if offset < 106 then (if offset < 105 then (namedLeaf104) else (namedLeaf105)) else (if offset < 107 then (namedLeaf106) else (namedLeaf107))) else (if offset < 110 then (if offset < 109 then (namedLeaf108) else (namedLeaf109)) else (if offset < 111 then (namedLeaf110) else (namedLeaf111))))) else (if offset < 120 then (if offset < 116 then (if offset < 114 then (if offset < 113 then (namedLeaf112) else (namedLeaf113)) else (if offset < 115 then (namedLeaf114) else (namedLeaf115))) else (if offset < 118 then (if offset < 117 then (namedLeaf116) else (namedLeaf117)) else (if offset < 119 then (namedLeaf118) else (namedLeaf119)))) else (if offset < 124 then (if offset < 122 then (if offset < 121 then (namedLeaf120) else (namedLeaf121)) else (if offset < 123 then (namedLeaf122) else (namedLeaf123))) else (if offset < 126 then (if offset < 125 then (namedLeaf124) else (namedLeaf125)) else (if offset < 127 then (namedLeaf126) else (namedLeaf127)))))))) else fallback

theorem point_checked (j : Fin 128) :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 (256 + j.val))) (lookup j.val) = true := by
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

theorem correct (id : Fin 24698) (hlow : 256 ≤ id.val) (hhigh : id.val < 384) :
    leafCheck library (N4R2WordTree.catalog id) (lookup (id.val - 256)) = true := by
  let j : Fin 128 := ⟨id.val - 256, by omega⟩
  have hsum : 256 + j.val = id.val := by dsimp [j]; omega
  have hindex : Fin.ofNat 24698 (256 + j.val) = id := by
    apply Fin.ext
    simp only [Fin.ofNat, hsum, Nat.mod_eq_of_lt id.isLt]
  have hh := point_checked j
  rw [hindex] at hh
  exact hh

#print axioms point_checked
#print axioms correct
end Jsp404.N4R2OuterLeftData.LeafShard002
