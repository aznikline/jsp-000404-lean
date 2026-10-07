import Jsp000404.N4R2OuterLeftReplay
import Jsp000404.N4R2WordCatalog

set_option autoImplicit false
set_option pp.fullNames true
set_option maxRecDepth 8192
set_option maxHeartbeats 0
set_option Elab.async false

namespace Jsp404.N4R2OuterLeftData.LeafShard001
open N4R2OuterLeftReplay

-- Cycle fingerprint 00c117b99bcd0b2b580ce9c104d9e7c95879bea7efd414cb1fa1acc8489793cb.
def localCycle00000 : Cycle where
  length := 7
  data := {
    node := ![.theta 1, .distance 1 3, .distance 3 5, .distance 5 6, .distance 0 5, .distance 0 4, .distance 0 1, .theta 1]
    constant := ![1, -1, -1, -1, 0, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false] }
  origin := ![.gapLower 1 6, .triangle 20 0, .triangle 33 0, .triangle 14 0, .gapLower 0 4, .triangle 2 1, .gapLower 1 0]

-- Cycle fingerprint 00dc0ef5f71549f6d6fb3b3c7eeb25ea484acf0e8ba621ee802ce0ab3c11c5da.
def localCycle00001 : Cycle where
  length := 4
  data := {
    node := ![.distance 4 5, .distance 1 4, .distance 1 2, .distance 2 5, .distance 4 5]
    constant := ![-1, -2, 2, 0]
    coefficient := ![0, 0, 0, 0]
    strict := ![false, false, true, false] }
  origin := ![.triangle 22 0, .gapLower 1 2, .gapUpper 2 2, .gapLower 5 4]

-- Cycle fingerprint 0176baecaff74ea6807f2af8f291185f6256fcf15ccfaed8a7547b6210e28e69.
def localCycle00002 : Cycle where
  length := 5
  data := {
    node := ![.distance 1 5, .distance 1 6, .distance 1 4, .theta 1, .distance 1 3, .distance 1 5]
    constant := ![0, -2, -1, 2, 0]
    coefficient := ![0, 0, 0, 1, 0]
    strict := ![true, false, false, false, true] }
  origin := ![.triangle 24 2, .gapLower 1 3, .corridorLower 1 4, .gapLower 1 6, .triangle 20 2]

-- Cycle fingerprint 026353ddd71152ee152351de28463ce3ce66d6e24dcb5664be94057a8194bb6a.
def localCycle00003 : Cycle where
  length := 11
  data := {
    node := ![.theta 0, .zero, .theta 4, .distance 3 4, .distance 2 4, .distance 1 4, .distance 1 6, .distance 1 3, .distance 1 5, .distance 1 2, .distance 0 1, .theta 0]
    constant := ![0, 0, 3, 0, 0, 0, -2, 0, -2, -1, -1]
    coefficient := ![0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, true, false, true, false, false, false] }
  origin := ![.thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 16 2, .triangle 23 2, .gapLower 1 4, .triangle 20 2, .gapLower 1 2, .triangle 0 0, .corridorLower 0 1]

-- Cycle fingerprint 05b40dfc4813fe69b3eabd2411a34b266c1cc0a7574533c6ba952b3f152bfaf0.
def localCycle00004 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 2 4, .distance 4 5, .distance 3 5, .distance 3 6, .distance 1 3, .distance 3 4, .theta 3]
    constant := ![3, 0, -1, 0, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, true, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 25 2, .triangle 28 0, .triangle 31 2, .triangle 33 2, .triangle 21 0, .triangle 19 0, .corridorLower 3 4]

-- Cycle fingerprint 06081cbf301c44810aa99f4f89652439ee62a3aca0dfd1fdfbf3a1849631dbf6.
def localCycle00005 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 4, .distance 1 2, .distance 0 1, .theta 0, .zero, .theta 5, .distance 4 5, .distance 1 4]
    constant := ![-2, -2, -1, 0, 0, 3, -1]
    coefficient := ![0, 0, 0, 0, 1, 1, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 1 2, .gapLower 1 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 5, .corridorUpper 4 5, .triangle 22 0]

-- Cycle fingerprint 072ea027891b33e3b284698dffcd9a521a378b7f612e90e430f7761f226b0629.
def localCycle00006 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 3, .distance 1 6, .distance 0 1, .theta 1, .zero, .theta 4, .distance 3 4, .distance 1 3]
    constant := ![-2, -1, -2, 0, 0, 3, -1]
    coefficient := ![0, 0, 0, 0, 1, 1, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 1 4, .triangle 4 0, .gapLower 1 0, .thetaLower 1, .thetaUpper 4, .corridorUpper 3 4, .triangle 19 0]

-- Cycle fingerprint 075f973072869b3ce7269e95a9e51cd8a2973d0585d05eb18320f7b2c3c77be6.
def localCycle00007 : Cycle where
  length := 9
  data := {
    node := ![.distance 3 5, .distance 1 3, .distance 1 4, .distance 1 2, .distance 0 1, .theta 0, .zero, .theta 5, .distance 4 5, .distance 3 5]
    constant := ![-1, -2, -2, -1, -1, 0, 0, 3, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![false, false, false, false, false, false, false, false, true] }
  origin := ![.triangle 20 0, .gapLower 1 3, .gapLower 1 2, .triangle 0 0, .corridorLower 0 1, .thetaLower 0, .thetaUpper 5, .corridorUpper 4 5, .triangle 31 2]

-- Cycle fingerprint 07617771145ba941a66f3b65e3c3a62ee8d0f4e4c24c3462f48e03a46cf9d84f.
def localCycle00008 : Cycle where
  length := 9
  data := {
    node := ![.distance 3 5, .distance 1 3, .distance 1 4, .distance 1 2, .distance 0 1, .theta 0, .zero, .theta 5, .distance 4 5, .distance 3 5]
    constant := ![-1, -2, 0, -2, -1, 0, 0, 3, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![false, false, true, false, false, false, false, false, true] }
  origin := ![.triangle 20 0, .gapLower 1 3, .triangle 16 1, .gapLower 1 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 5, .corridorUpper 4 5, .triangle 31 2]

-- Cycle fingerprint 08aa5ff7cb9cbafdcfc8c446e6d4f7721d06293e38300f7de1015bdd5b7de669.
def localCycle00009 : Cycle where
  length := 9
  data := {
    node := ![.distance 3 4, .distance 1 3, .distance 1 6, .distance 1 5, .distance 1 2, .distance 0 1, .theta 0, .zero, .theta 4, .distance 3 4]
    constant := ![-1, -2, 0, -2, -1, -1, 0, 0, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1, 1]
    strict := ![false, false, true, false, false, false, false, false, false] }
  origin := ![.triangle 19 0, .gapLower 1 4, .triangle 24 1, .gapLower 1 2, .triangle 0 0, .corridorLower 0 1, .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4]

-- Cycle fingerprint 0ad9a5f42187ef687300cd10a156c9b308dd679bc84f5dc040eccbd7d2076dd3.
def localCycle00010 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 2 4, .distance 4 6, .distance 3 6, .distance 3 5, .distance 1 3, .distance 3 4, .theta 3]
    constant := ![3, 0, -1, 0, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, true, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 25 2, .triangle 29 0, .triangle 32 2, .triangle 33 1, .triangle 20 0, .triangle 19 0, .corridorLower 3 4]

-- Cycle fingerprint 0bcacd6823cc6f46230c2e15799eb97a7c645102118113580c2651fc176be5d6.
def localCycle00011 : Cycle where
  length := 6
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 5, .distance 3 6, .distance 1 3, .distance 3 4, .theta 3]
    constant := ![3, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 26 0, .triangle 33 2, .triangle 21 0, .triangle 19 0, .corridorLower 3 4]

-- Cycle fingerprint 0bd5a0a16ce4643270d192b27f3fd224ed035e4c4c198a22902825763b142707.
def localCycle00012 : Cycle where
  length := 4
  data := {
    node := ![.distance 1 4, .distance 1 3, .distance 3 6, .distance 4 6, .distance 1 4]
    constant := ![-3, -1, 0, 2]
    coefficient := ![0, 0, 0, 0]
    strict := ![false, false, true, true] }
  origin := ![.gapLower 1 5, .triangle 21 0, .triangle 32 1, .gapUpper 4 3]

-- Cycle fingerprint 0ca00cdc1e381b5194ad0e7c80538aff3e5323d08d3dbd3362ca9b22f05e7586.
def localCycle00013 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 6, .distance 1 2, .distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 1 3, .distance 1 4, .distance 1 5, .distance 1 6]
    constant := ![-2, -1, -1, 0, 0, 3, 0, 0, -2, 0]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, true, false, true] }
  origin := ![.gapLower 1 2, .triangle 0 0, .corridorLower 0 1, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 15 2, .triangle 19 2, .gapLower 1 4, .triangle 24 2]

-- Cycle fingerprint 0f05f2a933f5a95b2f8ef26b76d4b1294bbe1b482a11dedd219a9fa593fbfa83.
def localCycle00014 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 6, .distance 1 5, .distance 3 5, .distance 4 5, .theta 4, .distance 3 4, .distance 1 3, .distance 1 6]
    constant := ![-3, 0, 0, -1, 3, -1, 0]
    coefficient := ![0, 0, 0, 0, 1, 0, 0]
    strict := ![false, true, true, false, false, false, true] }
  origin := ![.gapLower 1 3, .triangle 20 1, .triangle 31 1, .corridorLower 4 5, .corridorUpper 3 4, .triangle 19 0, .triangle 21 2]

-- Cycle fingerprint 10be55b683ef2fae624b6cfa3e4e9f2f275cab58f883ed3d8f5561734602614a.
def localCycle00015 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 1 3, .distance 1 4, .distance 0 1, .theta 1, .zero]
    constant := ![0, 3, 0, -1, -2, -1, -2, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 20 0, .gapLower 1 3, .triangle 2 0, .gapLower 1 0, .thetaLower 1]

-- Cycle fingerprint 10f59177fb21caf0b8646d8eed0198d2e05300f7368c1893c2ba67fd6e6ad462.
def localCycle00016 : Cycle where
  length := 4
  data := {
    node := ![.distance 1 5, .distance 1 3, .distance 3 6, .distance 5 6, .distance 1 5]
    constant := ![-3, -1, 0, 2]
    coefficient := ![0, 0, 0, 0]
    strict := ![false, false, true, true] }
  origin := ![.gapLower 1 5, .triangle 21 0, .triangle 33 1, .gapUpper 5 2]

-- Cycle fingerprint 1156018f6fdcdf511eccb1b8394c3068efb646236ac57986cbd793f4b2cd48ef.
def localCycle00017 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 2, .distance 0 1, .theta 1, .zero, .theta 5, .distance 4 5, .distance 2 4, .distance 1 2]
    constant := ![-2, -2, 0, 0, 3, -1, -1]
    coefficient := ![0, 0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 1 1, .gapLower 1 0, .thetaLower 1, .thetaUpper 5, .corridorUpper 4 5, .triangle 28 0, .triangle 16 0]

-- Cycle fingerprint 1474485da1777db18e9d0593ae2e570b7b1f2d872cd0b32893f5af36a8c52c61.
def localCycle00018 : Cycle where
  length := 5
  data := {
    node := ![.distance 1 2, .distance 2 5, .distance 4 5, .distance 1 5, .distance 1 4, .distance 1 2]
    constant := ![2, 0, 0, -3, 0]
    coefficient := ![0, 0, 0, 0, 0]
    strict := ![true, false, false, false, true] }
  origin := ![.gapUpper 2 2, .gapLower 5 4, .gapLower 5 3, .gapLower 1 3, .triangle 16 1]

-- Cycle fingerprint 1527f8a89e668365dc1094bb74d1ace616fb6b3c7f8cf5cfa1fdd03c7a310578.
def localCycle00019 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .theta 1, .distance 1 4, .distance 1 3, .distance 3 6, .distance 4 6, .distance 4 5, .distance 0 4, .distance 0 3, .distance 0 1]
    constant := ![-2, 2, 0, -1, 0, 0, -1, 0, 0]
    coefficient := ![0, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, true, false, false, true] }
  origin := ![.gapLower 1 0, .gapLower 1 6, .triangle 19 1, .triangle 21 0, .triangle 32 1, .triangle 34 1, .triangle 12 0, .gapLower 0 3, .triangle 1 1]

-- Cycle fingerprint 162013ce996f1ce680754e2067b9d0f1d36bd6a1c8bd2ea1849e70640327905a.
def localCycle00020 : Cycle where
  length := 5
  data := {
    node := ![.distance 1 2, .distance 2 5, .distance 4 5, .distance 1 5, .distance 1 4, .distance 1 2]
    constant := ![2, 0, 0, -2, 0]
    coefficient := ![0, 0, 0, 0, 0]
    strict := ![true, false, true, false, true] }
  origin := ![.gapUpper 2 2, .gapLower 5 4, .triangle 22 2, .gapLower 1 3, .triangle 16 1]

-- Cycle fingerprint 17365a2cef5b5116b3757a7fa187cbabe5e1d05ac67ba7d026187f2ae2e28f31.
def localCycle00021 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 2 4, .distance 1 4, .distance 4 6, .distance 3 4, .distance 0 3, .distance 0 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, -1, 0, -1, -1, -1, 0, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, true, true, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 28 0, .triangle 16 2, .triangle 23 0, .triangle 32 0, .triangle 9 0, .triangle 5 1, .triangle 0 1, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint 175df82c3590dac8e7202648df5029824cf8b34a84ec28528ab0caa4b7af51e3.
def localCycle00022 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 4, .distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 2 5, .distance 5 6, .distance 1 5, .distance 1 4]
    constant := ![-1, -1, 0, 0, 3, 0, -1, -1, -2]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, false, false] }
  origin := ![.triangle 2 0, .corridorLower 0 1, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 26 2, .triangle 30 0, .triangle 24 0, .gapLower 1 3]

-- Cycle fingerprint 194f57d604075c1c6886f6bc3eff12c8028724402f6beef752068244a351db72.
def localCycle00023 : Cycle where
  length := 14
  data := {
    node := ![.zero, .theta 3, .distance 2 3, .distance 3 4, .distance 1 3, .distance 3 5, .distance 4 5, .distance 5 6, .distance 0 5, .distance 0 4, .distance 0 3, .distance 0 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, -1, -1, -1, 0, -1, -1, 0, 0, 0, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, false, true, true, true, true, false, false] }
  origin := ![.thetaUpper 3, .corridorUpper 2 3, .triangle 25 0, .triangle 19 0, .triangle 20 0, .triangle 31 1, .triangle 34 0, .triangle 14 0, .triangle 12 1, .triangle 9 1, .triangle 5 1, .triangle 0 1, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint 1a236a503d4be24ce1c78d20d3eea8ab14780efb919167ef3ff5466af6419703.
def localCycle00024 : Cycle where
  length := 5
  data := {
    node := ![.distance 1 2, .distance 2 6, .distance 4 6, .distance 1 6, .distance 1 4, .distance 1 2]
    constant := ![2, 0, 0, -2, 0]
    coefficient := ![0, 0, 0, 0, 0]
    strict := ![true, false, true, false, true] }
  origin := ![.gapUpper 2 2, .gapLower 6 5, .triangle 23 2, .gapLower 1 3, .triangle 16 1]

-- Cycle fingerprint 1b7c46c5c3b44417b6cbbe4fa628a19eaf9e71b3e1d3d17b512062bff941040f.
def localCycle00025 : Cycle where
  length := 6
  data := {
    node := ![.theta 1, .zero, .theta 3, .distance 2 3, .distance 1 2, .distance 0 1, .theta 1]
    constant := ![0, 0, 3, -1, -2, -2]
    coefficient := ![0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.thetaLower 1, .thetaUpper 3, .corridorUpper 2 3, .triangle 15 0, .gapLower 1 1, .gapLower 1 0]

-- Cycle fingerprint 1c4f0b855cd4b1ce0c7120c5ec85023c79cff9060b7c9f99b3003b42f05179d4.
def localCycle00026 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 4, .distance 1 6, .distance 4 6, .distance 3 4, .distance 0 3, .distance 0 2, .theta 0, .zero, .theta 1, .distance 1 3, .distance 1 4]
    constant := ![-2, 0, -1, -1, 0, -1, 0, 0, 2, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![false, true, false, false, false, false, false, false, false, true] }
  origin := ![.gapLower 1 4, .triangle 23 1, .triangle 32 0, .triangle 9 0, .gapLower 0 2, .corridorLower 0 2, .thetaLower 0, .thetaUpper 1, .gapLower 1 6, .triangle 19 2]

-- Cycle fingerprint 1cc5baa42d32a51123bef6d6be066a0ede97e36224bce823e07414b1d537056f.
def localCycle00027 : Cycle where
  length := 8
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 2 3, .distance 1 2, .distance 0 1, .theta 1, .zero, .theta 5]
    constant := ![3, 0, -1, -1, -2, -2, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, false, false, false, false, false, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 26 0, .triangle 15 0, .gapLower 1 1, .gapLower 1 0, .thetaLower 1, .thetaUpper 5]

-- Cycle fingerprint 1da241de7b26d1e1c23455e646043136bf11f98ee31cda0d51f830bfbd3322ce.
def localCycle00028 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 3, .distance 3 6, .distance 4 6, .distance 4 5, .distance 0 4, .distance 0 3, .theta 0, .zero, .theta 1, .distance 1 4, .distance 1 3]
    constant := ![-1, 0, 0, -1, 0, -1, 0, 0, 1, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![false, true, true, false, false, false, false, false, false, true] }
  origin := ![.triangle 21 0, .triangle 32 1, .triangle 34 1, .triangle 12 0, .gapLower 0 3, .corridorLower 0 3, .thetaLower 0, .thetaUpper 1, .gapLower 1 6, .triangle 19 1]

-- Cycle fingerprint 1db1e1ad103a857db2d6d6142ac00ba79a87a0de866ddf6b96a98ce54174c628.
def localCycle00029 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 2, .distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 2 5, .distance 5 6, .distance 1 5, .distance 1 4, .distance 1 2]
    constant := ![-2, -1, 0, 0, 3, 0, -1, -1, -2, 0]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, false, false, true] }
  origin := ![.gapLower 1 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 26 2, .triangle 30 0, .triangle 24 0, .gapLower 1 3, .triangle 16 1]

-- Cycle fingerprint 1de8d98f2205ca0865def05058de5ae034d77b487df811faaf494e590b7ce422.
def localCycle00030 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 2, .distance 0 1, .theta 0, .zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 1 5, .distance 1 6, .distance 1 2]
    constant := ![-2, -1, 0, 0, 3, 0, 0, 0, -2, 0]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, true, false, true] }
  origin := ![.gapLower 1 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 17 2, .gapLower 1 5, .triangle 18 1]

-- Cycle fingerprint 1e5097d7f5232c6290a2083437aa870bf4d13d048f3441e1a380beaeb730215b.
def localCycle00031 : Cycle where
  length := 9
  data := {
    node := ![.distance 2 3, .distance 1 3, .distance 1 5, .distance 1 6, .distance 1 4, .distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3]
    constant := ![0, -2, 0, -2, -1, -1, 0, 0, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1, 1]
    strict := ![true, false, true, false, false, false, false, false, false] }
  origin := ![.triangle 15 2, .gapLower 1 5, .triangle 24 2, .gapLower 1 3, .triangle 2 0, .corridorLower 0 1, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3]

-- Cycle fingerprint 1ee5c5d88ca8fcf261644710c37e94e1b4e41d455115ae77457e6e9ddf81e3ed.
def localCycle00032 : Cycle where
  length := 11
  data := {
    node := ![.theta 0, .zero, .theta 3, .distance 2 3, .distance 2 4, .distance 4 6, .distance 1 6, .distance 1 5, .distance 1 4, .distance 1 2, .distance 0 1, .theta 0]
    constant := ![0, 0, 3, 0, -1, 0, -2, 0, -2, -1, -1]
    coefficient := ![0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, true, false, false, false] }
  origin := ![.thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 25 2, .triangle 29 0, .gapLower 6 3, .gapLower 1 4, .triangle 22 1, .gapLower 1 2, .triangle 0 0, .corridorLower 0 1]

-- Cycle fingerprint 1ee8088bfb0350d8c2f9e1a3ee1175df3e1c26c7f2a8297fc07ee04db09660a2.
def localCycle00033 : Cycle where
  length := 8
  data := {
    node := ![.distance 4 5, .theta 4, .distance 3 4, .distance 2 4, .distance 1 4, .distance 1 6, .distance 1 3, .distance 3 5, .distance 4 5]
    constant := ![-1, 3, 0, 0, -2, -2, -1, 0]
    coefficient := ![0, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, true] }
  origin := ![.corridorLower 4 5, .corridorUpper 3 4, .triangle 25 2, .triangle 16 2, .gapLower 1 5, .gapLower 1 4, .triangle 20 0, .triangle 31 1]

-- Cycle fingerprint 1ef7ec56d46fd0ac53344b7d55e8470adaa931561ac1f38bd2f949e10a799b23.
def localCycle00034 : Cycle where
  length := 6
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 3, .distance 2 5, .distance 5 6, .distance 4 5, .theta 4]
    constant := ![3, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 0, .triangle 26 2, .triangle 30 0, .triangle 34 0, .corridorLower 4 5]

-- Cycle fingerprint 1f446f54db66a3407225a7326478114c9f7f5c322433800bd941dc09012dd29d.
def localCycle00035 : Cycle where
  length := 13
  data := {
    node := ![.distance 3 5, .distance 2 5, .distance 1 5, .distance 1 6, .distance 1 3, .distance 3 4, .distance 0 3, .distance 0 2, .distance 0 1, .theta 1, .zero, .theta 5, .distance 4 5, .distance 3 5]
    constant := ![0, 0, -2, 0, -1, -1, 0, 0, -2, 0, 0, 3, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![true, true, false, true, false, false, false, true, false, false, false, false, true] }
  origin := ![.triangle 26 2, .triangle 17 2, .gapLower 1 5, .triangle 21 1, .triangle 19 0, .triangle 9 0, .gapLower 0 2, .triangle 0 1, .gapLower 1 0, .thetaLower 1, .thetaUpper 5, .corridorUpper 4 5, .triangle 31 2]

-- Cycle fingerprint 1fcb8758a6300ddb6f252b2b6256c3c24b333f7a61d3a9f2482271bd90c93505.
def localCycle00036 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 3, .distance 2 3, .distance 2 4, .distance 2 5, .distance 5 6, .distance 4 5, .distance 1 4, .distance 1 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, 0, -1, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 3, .corridorUpper 2 3, .triangle 25 2, .triangle 28 2, .triangle 30 0, .triangle 34 0, .triangle 22 0, .gapLower 1 2, .triangle 0 0, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint 212707d1c4897ac7eb4fb713c4a1625a763075dae5002419feb11f9d46539bdb.
def localCycle00037 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 3, .distance 2 5, .distance 5 6, .distance 3 6, .distance 1 3, .distance 3 5, .distance 4 5, .theta 4]
    constant := ![3, -1, 0, -1, 0, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 0, .triangle 26 2, .triangle 30 0, .triangle 33 2, .triangle 21 0, .triangle 20 0, .triangle 31 1, .corridorLower 4 5]

-- Cycle fingerprint 214e4f1d69f8be100db14176088660a7a60b3385fdd9043850f6241e3181fbe1.
def localCycle00038 : Cycle where
  length := 11
  data := {
    node := ![.distance 3 5, .distance 3 4, .distance 0 3, .distance 0 2, .theta 0, .zero, .theta 1, .distance 1 3, .distance 1 5, .distance 1 6, .distance 5 6, .distance 3 5]
    constant := ![0, -1, 0, -1, 0, 0, 2, 0, -2, 0, -1]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, true, false, true, false] }
  origin := ![.gapLower 3 2, .triangle 9 0, .gapLower 0 2, .corridorLower 0 2, .thetaLower 0, .thetaUpper 1, .gapLower 1 6, .triangle 20 2, .gapLower 1 4, .triangle 24 1, .triangle 33 0]

-- Cycle fingerprint 21a7274897f48b58e1eb5bf9f4a246256079094b11e6ecb1ced8993f8d177b1f.
def localCycle00039 : Cycle where
  length := 4
  data := {
    node := ![.distance 1 3, .distance 1 4, .distance 4 5, .distance 3 5, .distance 1 3]
    constant := ![-3, -1, 0, 2]
    coefficient := ![0, 0, 0, 0]
    strict := ![false, false, true, true] }
  origin := ![.gapLower 1 5, .triangle 22 0, .triangle 31 2, .gapUpper 3 4]

-- Cycle fingerprint 22404b30b56843c0c4dfac7cfae7a9bc13ffd9bcfcd80ca1bb12d9645ac74bc9.
def localCycle00040 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 4, .distance 1 2, .distance 0 1, .theta 1, .zero, .theta 5, .distance 4 5, .distance 1 4]
    constant := ![-2, -1, -2, 0, 0, 3, -1]
    coefficient := ![0, 0, 0, 0, 1, 1, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 1 2, .triangle 0 0, .gapLower 1 0, .thetaLower 1, .thetaUpper 5, .corridorUpper 4 5, .triangle 22 0]

-- Cycle fingerprint 23b02e5016b844542a0ad032aa8425db509b8d09570fd8dd93ae1f48745e9896.
def localCycle00041 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 2 4, .distance 4 5, .distance 3 5, .distance 1 3, .distance 1 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, -1, -1, 0, -1, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, false, true, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 29 0, .triangle 28 0, .triangle 31 2, .triangle 20 0, .triangle 15 1, .triangle 0 0, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint 2509510b47594f32300bdfbb0becc20d44d4b8f2c215da8a149ade92f9b51591.
def localCycle00042 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .theta 1, .distance 1 3, .distance 1 4, .distance 4 6, .distance 4 5, .distance 3 4, .distance 0 3, .distance 0 2, .distance 0 1]
    constant := ![-2, 2, 0, -1, 0, -1, -1, 0, 0]
    coefficient := ![0, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false, false, true] }
  origin := ![.gapLower 1 0, .gapLower 1 6, .triangle 19 2, .triangle 23 0, .triangle 34 1, .triangle 31 0, .triangle 9 0, .gapLower 0 2, .triangle 0 1]

-- Cycle fingerprint 25d4afcbeb49879dac900fbdf937010bdb580d4a4af4c7a8e14b7d195cffcf09.
def localCycle00043 : Cycle where
  length := 4
  data := {
    node := ![.distance 1 3, .distance 1 5, .distance 5 6, .distance 3 6, .distance 1 3]
    constant := ![-2, -1, 0, 2]
    coefficient := ![0, 0, 0, 0]
    strict := ![false, false, true, true] }
  origin := ![.gapLower 1 5, .triangle 24 0, .triangle 33 2, .gapUpper 3 4]

-- Cycle fingerprint 27e350ab4c831ebe9070c4afbc59924ee0f2723e6d450b48d647e0ebb0766207.
def localCycle00044 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .theta 1, .distance 1 3, .distance 1 5, .distance 5 6, .distance 3 5, .distance 3 4, .distance 0 3, .distance 0 2, .distance 0 1]
    constant := ![-2, 2, 0, -1, -1, 0, -1, 0, 0]
    coefficient := ![0, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false, true] }
  origin := ![.gapLower 1 0, .gapLower 1 6, .triangle 20 2, .triangle 24 0, .triangle 33 0, .gapLower 3 2, .triangle 9 0, .gapLower 0 2, .triangle 0 1]

-- Cycle fingerprint 28fea3a39d9a11240b7bd8c40ce2d155f891e87e795567db5dafb2fe4c203453.
def localCycle00045 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 2 3, .distance 2 6, .distance 2 5, .distance 1 5, .distance 1 2, .distance 0 1]
    constant := ![-1, 0, 0, 3, -1, 0, 0, 0, -2, -2]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, true, false, false] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 25 0, .triangle 27 2, .triangle 30 1, .triangle 17 2, .gapLower 1 2, .gapLower 1 1]

-- Cycle fingerprint 29117a0ef66f2b0b6e6ddbd8712148df6d53031280e3107e54b9743b00bb42de.
def localCycle00046 : Cycle where
  length := 9
  data := {
    node := ![.distance 5 6, .distance 1 5, .distance 1 4, .distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 2 5, .distance 5 6]
    constant := ![-1, -3, -1, -1, 0, 0, 3, 0, -1]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, false, false, false, false, true, false] }
  origin := ![.triangle 24 0, .gapLower 1 3, .triangle 2 0, .corridorLower 0 1, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 26 2, .triangle 30 0]

-- Cycle fingerprint 2a96ff14d0628a353621a2ea2b1baca5178cbd246db8a6ddd6c9d5686f8dfb4e.
def localCycle00047 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 6, .distance 1 3, .distance 3 5, .distance 4 5, .distance 0 4, .distance 0 3, .theta 0, .zero, .theta 1, .distance 1 4, .distance 1 6]
    constant := ![-2, -1, 0, -1, 0, -1, 0, 0, 2, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![false, false, true, false, false, false, false, false, false, true] }
  origin := ![.gapLower 1 4, .triangle 20 0, .triangle 31 1, .triangle 12 0, .gapLower 0 3, .corridorLower 0 3, .thetaLower 0, .thetaUpper 1, .gapLower 1 6, .triangle 23 2]

-- Cycle fingerprint 2af71584599cd2c1e4b83ae593a98fde5023d76521d423b9691ffa541464f7f1.
def localCycle00048 : Cycle where
  length := 6
  data := {
    node := ![.theta 4, .distance 3 4, .distance 1 3, .distance 1 5, .distance 5 6, .distance 4 5, .theta 4]
    constant := ![3, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 19 0, .triangle 20 2, .triangle 24 0, .triangle 34 0, .corridorLower 4 5]

-- Cycle fingerprint 2af823b9eee0f9ded70739b2378307df7b29d24739b37e54f6ef2fd42932830b.
def localCycle00049 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 2, .distance 0 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 2 4, .distance 2 6, .distance 1 6, .distance 1 3, .distance 1 2]
    constant := ![-2, -1, 0, 0, 3, 0, 0, 0, -2, 0]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, true, false, true] }
  origin := ![.gapLower 1 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 29 2, .triangle 18 2, .gapLower 1 4, .triangle 15 1]

-- Cycle fingerprint 2b7c73f7548f1a1a902a93800a6bd8552e5e32142e64198b426646177da882dd.
def localCycle00050 : Cycle where
  length := 4
  data := {
    node := ![.distance 1 6, .distance 1 4, .distance 1 2, .distance 2 6, .distance 1 6]
    constant := ![-2, -2, 2, 0]
    coefficient := ![0, 0, 0, 0]
    strict := ![false, false, true, true] }
  origin := ![.gapLower 1 3, .gapLower 1 2, .gapUpper 2 2, .triangle 18 2]

-- Cycle fingerprint 2bce6387ae51baf26d1f4395ceddca69b39c9c3b254dfbcc3855bc4161b2933d.
def localCycle00051 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 2, .distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 1 3, .distance 1 4, .distance 1 5, .distance 1 6, .distance 1 2]
    constant := ![-2, -1, 0, 0, 3, 0, 0, 0, -2, 0]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, true, false, true] }
  origin := ![.gapLower 1 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 15 2, .triangle 19 2, .triangle 22 2, .gapLower 1 3, .triangle 18 1]

-- Cycle fingerprint 2d5c6cc2f52f45cf6d760b951c805cf2b0eea37d449e6bf9e85e3e1c12dcbcb4.
def localCycle00052 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 2 4, .distance 4 5, .distance 3 5, .distance 1 3, .distance 3 4, .distance 0 3, .theta 0, .zero]
    constant := ![0, 3, 0, -1, -1, 0, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, false, false, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 29 0, .triangle 28 0, .triangle 31 2, .triangle 20 0, .triangle 19 0, .triangle 9 0, .corridorLower 0 3, .thetaLower 0]

-- Cycle fingerprint 2e0e8c8d38814d1a0d11fd33863a0b53a9edbc0a76868f3e02fd56fcfb87587a.
def localCycle00053 : Cycle where
  length := 3
  data := {
    node := ![.distance 5 6, .distance 1 6, .distance 1 5, .distance 5 6]
    constant := ![0, -3, 2]
    coefficient := ![0, 0, 0]
    strict := ![false, false, true] }
  origin := ![.gapLower 6 3, .gapLower 1 4, .gapUpper 5 3]

-- Cycle fingerprint 2e7fa84d669415052948468da02c695fa2e5da65452c8dc1594fb8b12a6271d5.
def localCycle00054 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 1, .distance 1 3, .distance 3 6, .distance 3 5, .distance 3 4, .distance 0 3, .distance 0 2, .theta 0, .zero]
    constant := ![0, 1, -1, 0, 0, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false, false, false, false] }
  origin := ![.thetaUpper 1, .gapLower 1 6, .triangle 21 0, .triangle 33 1, .triangle 31 1, .triangle 9 0, .gapLower 0 2, .corridorLower 0 2, .thetaLower 0]

-- Cycle fingerprint 2e8cb6e7c4909a519af75e81f5f9defb3e0a074ecdf09af0719c8ddfbb3f965d.
def localCycle00055 : Cycle where
  length := 13
  data := {
    node := ![.distance 3 4, .distance 2 4, .distance 1 4, .distance 1 6, .distance 1 3, .distance 3 5, .distance 4 5, .distance 0 4, .distance 0 3, .distance 0 1, .theta 1, .zero, .theta 4, .distance 3 4]
    constant := ![0, 0, -2, 0, -1, 0, -1, 0, 0, -2, 0, 0, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1]
    strict := ![true, true, false, true, false, true, false, false, true, false, false, false, false] }
  origin := ![.triangle 25 2, .triangle 16 2, .gapLower 1 5, .triangle 21 1, .triangle 20 0, .triangle 31 1, .triangle 12 0, .gapLower 0 3, .triangle 1 1, .gapLower 1 0, .thetaLower 1, .thetaUpper 4, .corridorUpper 3 4]

-- Cycle fingerprint 306083743dfa6967acdf8336328e2035744a23c4ff240f4c4a66b7b380be6dda.
def localCycle00056 : Cycle where
  length := 3
  data := {
    node := ![.distance 3 4, .distance 1 3, .distance 1 4, .distance 3 4]
    constant := ![2, -3, 0]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.gapUpper 3 2, .gapLower 1 3, .triangle 19 1]

-- Cycle fingerprint 317c0d6fd70879b3aac3881c967a6aa2667d292c0f76d758e96b0a4d6ccdaf66.
def localCycle00057 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 3, .distance 2 3, .distance 2 5, .distance 5 6, .distance 1 5, .distance 1 4, .distance 1 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, -1, -1, 0, -2, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 3, .corridorUpper 2 3, .triangle 26 2, .triangle 30 0, .triangle 24 0, .gapLower 1 3, .gapLower 1 2, .triangle 0 0, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint 31c2206412be8aafa78cbeead9f69e0a25752ac8f89e8fe08edf9d5aa5eaecd2.
def localCycle00058 : Cycle where
  length := 6
  data := {
    node := ![.theta 4, .distance 3 4, .distance 1 3, .distance 3 5, .distance 5 6, .distance 4 5, .theta 4]
    constant := ![3, -1, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 19 0, .triangle 20 0, .triangle 33 0, .triangle 34 0, .corridorLower 4 5]

-- Cycle fingerprint 31e58d2e7987c4d6bc8a2b928af8df5b3773821a2477be107221321ef9592b2a.
def localCycle00059 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 3, .distance 1 6, .distance 1 5, .distance 1 2, .distance 0 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 1 3]
    constant := ![0, -2, -2, -1, -1, 0, 0, 3, -1]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![true, false, false, false, false, false, false, false, false] }
  origin := ![.triangle 21 2, .gapLower 1 3, .gapLower 1 2, .triangle 0 0, .corridorLower 0 1, .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 19 0]

-- Cycle fingerprint 3326e809d105197b10d2daac9c101c5c781baaf6c6d12619995b59fd73bf7f62.
def localCycle00060 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 2 4, .distance 4 5, .distance 5 6, .distance 3 6, .distance 1 3, .distance 3 5, .distance 3 4, .theta 3]
    constant := ![3, 0, -1, -1, 0, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, false, false, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 25 2, .triangle 28 0, .triangle 34 0, .triangle 33 2, .triangle 21 0, .triangle 20 0, .triangle 31 1, .corridorLower 3 4]

-- Cycle fingerprint 3344b7ccf28d9ea7a99c0ce15ee50a63d5bf8f5acdbe3b37315dd43902793d4e.
def localCycle00061 : Cycle where
  length := 8
  data := {
    node := ![.distance 4 5, .distance 3 5, .distance 1 3, .distance 1 4, .distance 0 1, .theta 0, .zero, .theta 5, .distance 4 5]
    constant := ![0, -1, -2, -1, -1, 0, 0, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 1]
    strict := ![true, false, false, false, false, false, false, false] }
  origin := ![.triangle 31 2, .triangle 20 0, .gapLower 1 3, .triangle 2 0, .corridorLower 0 1, .thetaLower 0, .thetaUpper 5, .corridorUpper 4 5]

-- Cycle fingerprint 33660f2e2f9ddde407bf4b22f83363d861149299d498457717cfe85572ca02f9.
def localCycle00062 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 4, .distance 0 1, .theta 0, .zero, .theta 5, .distance 4 5, .distance 3 5, .distance 1 3, .distance 1 6, .distance 1 4]
    constant := ![-1, -1, 0, 0, 3, 0, -1, 0, -2]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, true, false] }
  origin := ![.triangle 2 0, .corridorLower 0 1, .thetaLower 0, .thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 20 0, .triangle 21 2, .gapLower 1 3]

-- Cycle fingerprint 339746bfda5bde4406e182ae33e2b3d102df12a81e8721cf1b59867623dfe82b.
def localCycle00063 : Cycle where
  length := 13
  data := {
    node := ![.distance 1 3, .distance 1 4, .distance 1 6, .distance 1 5, .distance 4 5, .distance 3 4, .distance 0 3, .distance 0 2, .distance 0 1, .theta 1, .zero, .theta 3, .distance 2 3, .distance 1 3]
    constant := ![0, 0, -2, 0, -1, -1, 0, 0, -2, 0, 0, 3, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![true, true, false, true, false, false, false, true, false, false, false, false, true] }
  origin := ![.triangle 19 2, .triangle 23 2, .gapLower 1 3, .triangle 22 1, .triangle 31 0, .triangle 9 0, .gapLower 0 2, .triangle 0 1, .gapLower 1 0, .thetaLower 1, .thetaUpper 3, .corridorUpper 2 3, .triangle 15 2]

-- Cycle fingerprint 3479ba49f7595cb19a78d3f49470c11cd615d471c27682e441b333e0fb93ecf6.
def localCycle00064 : Cycle where
  length := 11
  data := {
    node := ![.distance 4 6, .distance 3 4, .distance 0 3, .distance 0 2, .theta 0, .zero, .theta 1, .distance 1 3, .distance 1 4, .distance 1 5, .distance 1 6, .distance 4 6]
    constant := ![-1, -1, 0, -1, 0, 0, 2, 0, 0, -2, 0]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, true, true, false, true] }
  origin := ![.triangle 32 0, .triangle 9 0, .gapLower 0 2, .corridorLower 0 2, .thetaLower 0, .thetaUpper 1, .gapLower 1 6, .triangle 19 2, .triangle 22 2, .gapLower 1 3, .triangle 23 1]

-- Cycle fingerprint 3678b1864356315f827eb246c2c6ad571f156f862dcb9e262e92e7b42146a802.
def localCycle00065 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 3, .distance 1 5, .distance 1 6, .distance 1 4, .distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 1 3]
    constant := ![0, -2, -2, -1, -1, 0, 0, 3, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![true, false, false, false, false, false, false, false, true] }
  origin := ![.triangle 20 2, .gapLower 1 4, .gapLower 1 3, .triangle 2 0, .corridorLower 0 1, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 15 2]

-- Cycle fingerprint 372c5413230ca32c6af204af554536b694664290f60901021543561f8d3352ef.
def localCycle00066 : Cycle where
  length := 13
  data := {
    node := ![.zero, .theta 3, .distance 2 3, .distance 3 4, .distance 3 6, .distance 1 3, .distance 3 5, .distance 4 5, .distance 0 4, .distance 0 3, .distance 0 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, -1, 0, -1, -1, 0, -1, 0, 0, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, true, false, true, true, true, false, false] }
  origin := ![.thetaUpper 3, .corridorUpper 2 3, .triangle 25 0, .triangle 32 2, .triangle 21 0, .triangle 20 0, .triangle 31 1, .triangle 12 0, .triangle 9 1, .triangle 5 1, .triangle 0 1, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint 375ea4c2c7514e5d8c8336103f287623329b36af107ecf83787fe2c31825d88f.
def localCycle00067 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 3, .distance 2 3, .distance 3 6, .distance 3 4, .distance 1 3, .distance 3 5, .distance 0 3, .distance 0 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, -1, 0, -1, -1, -1, 0, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, true, true, false, false] }
  origin := ![.thetaUpper 3, .corridorUpper 2 3, .triangle 27 0, .triangle 32 1, .triangle 19 0, .triangle 20 0, .triangle 10 0, .triangle 5 1, .triangle 0 1, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint 38be005bd12af9214098044d092aa215fcaff419ceb200eae6f099268467133f.
def localCycle00068 : Cycle where
  length := 4
  data := {
    node := ![.distance 1 3, .distance 1 4, .distance 4 5, .distance 3 5, .distance 1 3]
    constant := ![-2, -1, 0, 2]
    coefficient := ![0, 0, 0, 0]
    strict := ![false, false, true, true] }
  origin := ![.gapLower 1 5, .triangle 22 0, .triangle 31 2, .gapUpper 3 4]

-- Cycle fingerprint 3a02e6f00d0e0ac495527c8b1f6872d3815dfa97b04dba497e5cb7ec47824e53.
def localCycle00069 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 2, .distance 0 1, .theta 0, .zero, .theta 5, .distance 4 5, .distance 3 5, .distance 1 3, .distance 1 4, .distance 1 2]
    constant := ![-1, -1, 0, 0, 3, 0, -1, 0, -2]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, true, false] }
  origin := ![.triangle 0 0, .corridorLower 0 1, .thetaLower 0, .thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 20 0, .triangle 19 2, .gapLower 1 2]

-- Cycle fingerprint 3a8a31010e19b998ecb8a37d7126cdace79c39845458376a155c3239d5071160.
def localCycle00070 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 1 4, .distance 4 5, .distance 3 4, .distance 0 3, .distance 0 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, -1, -1, -1, -1, 0, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, true, true, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 23 0, .triangle 22 0, .triangle 31 0, .triangle 9 0, .triangle 5 1, .triangle 0 1, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint 3bf947260aaf9824c7d05b05f145d36762503e880225ceb262d4c8ed3b3887e7.
def localCycle00071 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 3, .distance 2 3, .distance 2 4, .distance 2 5, .distance 5 6, .distance 4 5, .distance 3 4, .distance 0 3, .distance 0 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, 0, -1, -1, -1, -1, 0, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, false, true, true, false, false] }
  origin := ![.thetaUpper 3, .corridorUpper 2 3, .triangle 25 2, .triangle 28 2, .triangle 30 0, .triangle 34 0, .triangle 31 0, .triangle 9 0, .triangle 5 1, .triangle 0 1, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint 3cc3cedd136dd1463c3fd62b4835c7716a852e97df6c4c8dad1d0c947fea52e1.
def localCycle00072 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 3, .distance 2 3, .distance 2 4, .distance 2 5, .distance 5 6, .distance 3 5, .distance 1 3, .distance 1 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, 0, -1, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, true, false, false, false] }
  origin := ![.thetaUpper 3, .corridorUpper 2 3, .triangle 25 2, .triangle 28 2, .triangle 30 0, .triangle 33 0, .triangle 20 0, .triangle 15 1, .triangle 0 0, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint 3eb2fab31d88b18ef7c5ad75aaa11e7c1ac147236603bf5834fabba9e1dd7b2c.
def localCycle00073 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 3, .distance 1 5, .distance 0 1, .theta 1, .zero, .theta 4, .distance 3 4, .distance 1 3]
    constant := ![-2, -1, -2, 0, 0, 3, -1]
    coefficient := ![0, 0, 0, 0, 1, 1, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 1 3, .triangle 3 0, .gapLower 1 0, .thetaLower 1, .thetaUpper 4, .corridorUpper 3 4, .triangle 19 0]

-- Cycle fingerprint 40545932fa7aa145e1e42b7fa600c16b40f51c3eb25a2bbddf8361857b0b1fbe.
def localCycle00074 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 2 3, .distance 2 4, .distance 4 6, .distance 3 4, .distance 1 3, .distance 3 5, .theta 3]
    constant := ![3, 0, -1, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 25 2, .triangle 29 0, .triangle 32 0, .triangle 19 0, .triangle 20 0, .corridorLower 3 5]

-- Cycle fingerprint 411bb848c1571330bbc646902b448a1104ce9740c0f10f6f800b41893d7e5309.
def localCycle00075 : Cycle where
  length := 11
  data := {
    node := ![.distance 2 3, .distance 2 4, .distance 4 6, .distance 4 5, .distance 1 4, .distance 1 2, .distance 0 1, .theta 1, .theta 0, .zero, .theta 3, .distance 2 3]
    constant := ![0, -1, 0, -1, 0, -1, -3, 0, 0, 0, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1]
    strict := ![true, false, true, false, false, false, false, true, false, false, false] }
  origin := ![.triangle 25 2, .triangle 29 0, .triangle 34 1, .triangle 22 0, .gapLower 1 2, .triangle 0 0, .gapLower 1 0, .thetaNext 0, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3]

-- Cycle fingerprint 4228fcd88f822e4f5c1d63d34ebc45b126d5f3756f82df4eb39af6553beebe43.
def localCycle00076 : Cycle where
  length := 13
  data := {
    node := ![.distance 2 3, .distance 1 3, .distance 1 4, .distance 1 5, .distance 4 5, .distance 3 5, .distance 5 6, .distance 0 5, .distance 0 4, .distance 0 1, .theta 1, .zero, .theta 3, .distance 2 3]
    constant := ![0, 0, -2, 0, 0, -1, -1, 0, 0, -2, 0, 0, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1]
    strict := ![true, true, false, true, true, false, false, false, true, false, false, false, false] }
  origin := ![.triangle 15 2, .triangle 19 2, .gapLower 1 4, .triangle 22 1, .triangle 31 2, .triangle 33 0, .triangle 14 0, .gapLower 0 4, .triangle 2 1, .gapLower 1 0, .thetaLower 1, .thetaUpper 3, .corridorUpper 2 3]

-- Cycle fingerprint 4242f0c32e621a8022bf520efd336dcb0063ebfbecd3283f09a05db97c956177.
def localCycle00077 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 2, .distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 1 3, .distance 1 5, .distance 1 6, .distance 1 4, .distance 1 2]
    constant := ![-1, -1, 0, 0, 3, 0, 0, 0, -2, -2]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, true, false, false] }
  origin := ![.triangle 0 0, .corridorLower 0 1, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 15 2, .triangle 20 2, .triangle 24 2, .gapLower 1 3, .gapLower 1 2]

-- Cycle fingerprint 427b807400e9d29cf4b2c83d3d0ea7c3b487ecd3539522a196e86eba83b6f769.
def localCycle00078 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 4, .distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 2 4, .distance 4 5, .distance 5 6, .distance 1 5, .distance 1 4]
    constant := ![-1, -1, 0, 0, 3, 0, -1, -1, -1, 0]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, false, false, false] }
  origin := ![.triangle 2 0, .corridorLower 0 1, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 25 2, .triangle 28 0, .triangle 34 0, .triangle 24 0, .gapLower 1 3]

-- Cycle fingerprint 43ea03350251aa6ed34fe0aadba2df70daeb06de652353eb4b222563a45fef78.
def localCycle00079 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 3, .distance 3 5, .distance 1 3, .distance 3 6, .distance 4 6, .theta 4]
    constant := ![3, -1, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 0, .triangle 26 0, .triangle 20 0, .triangle 21 0, .triangle 32 1, .corridorLower 4 6]

-- Cycle fingerprint 43f41b60f071f25d4e66ab50d22544c3aeeeb989f02e5e2acec438f1edd59c1b.
def localCycle00080 : Cycle where
  length := 10
  data := {
    node := ![.theta 0, .zero, .theta 3, .distance 2 3, .distance 2 4, .distance 4 6, .distance 4 5, .distance 1 4, .distance 1 2, .distance 0 1, .theta 0]
    constant := ![0, 0, 3, 0, -1, 0, -1, 0, -3, -1]
    coefficient := ![0, 1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true, false, false, false, false] }
  origin := ![.thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 25 2, .triangle 29 0, .triangle 34 1, .triangle 22 0, .gapLower 1 2, .gapLower 1 1, .corridorLower 0 1]

-- Cycle fingerprint 453d5aed5743d0482e7647396fd5303c410975b1f5aa57a3f6011d91b33ca4ab.
def localCycle00081 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 2 4, .distance 4 5, .distance 3 4, .distance 0 3, .distance 0 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, -1, -1, -1, -1, 0, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, true, true, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 29 0, .triangle 28 0, .triangle 31 0, .triangle 9 0, .triangle 5 1, .triangle 0 1, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint 463200040bd54650e4b399dfece2397dbe8ae999f30c35b2dcd443fe9cc7f846.
def localCycle00082 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 2 4, .distance 4 6, .distance 4 5, .distance 1 4, .distance 1 2, .distance 0 1]
    constant := ![-1, 0, 0, 3, 0, -1, 0, -1, -2, -2]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, true, false, false, false] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 25 2, .triangle 29 0, .triangle 34 1, .triangle 22 0, .gapLower 1 2, .gapLower 1 1]

-- Cycle fingerprint 4650bf0d1da9187d0f24bd0202ece0a94a48f9c1de41aac9ddb37c510c6898bc.
def localCycle00083 : Cycle where
  length := 13
  data := {
    node := ![.distance 2 5, .distance 1 5, .distance 1 6, .distance 1 3, .distance 3 4, .distance 0 3, .distance 0 2, .distance 0 1, .theta 1, .zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 5]
    constant := ![0, 0, -2, -1, -1, 0, 0, -2, 0, 0, 3, 0, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![true, true, false, false, false, false, true, false, false, false, false, true, true] }
  origin := ![.triangle 17 2, .triangle 24 2, .gapLower 1 4, .triangle 19 0, .triangle 9 0, .gapLower 0 2, .triangle 0 1, .gapLower 1 0, .thetaLower 1, .thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 2]

-- Cycle fingerprint 46d1309cfe7c3446e8586c1bc8c745eb516923d056c17cd3068605d2346b518c.
def localCycle00084 : Cycle where
  length := 5
  data := {
    node := ![.theta 4, .distance 2 4, .distance 4 5, .distance 3 4, .distance 4 6, .theta 4]
    constant := ![3, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false] }
  origin := ![.corridorUpper 2 4, .triangle 28 0, .triangle 31 0, .triangle 32 0, .corridorLower 4 6]

-- Cycle fingerprint 47b674e5a2e2e2319efedcb29e35e95873e456f0561c41bef095c2045cf60bd8.
def localCycle00085 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 2 3, .distance 3 5, .distance 1 3, .distance 1 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, 0, -1, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, true, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 27 0, .triangle 26 0, .triangle 20 0, .triangle 15 1, .triangle 0 0, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint 48492397819d227504c8ea9d26f1032e94ccc74bc43d5a16994f1f8bc5f07689.
def localCycle00086 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 5, .distance 1 2, .distance 0 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 2 4, .distance 1 4, .distance 1 6, .distance 1 5]
    constant := ![-2, -1, -1, 0, 0, 3, 0, 0, -2, 0]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, true, false, true] }
  origin := ![.gapLower 1 2, .triangle 0 0, .corridorLower 0 1, .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 16 2, .gapLower 1 5, .triangle 24 1]

-- Cycle fingerprint 48c974551d9d456077d192d7d059d1294123de917fc7f7239acfda45b1dd319c.
def localCycle00087 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 2 5, .distance 5 6, .distance 3 6, .distance 1 3, .distance 3 5, .distance 3 4, .theta 3]
    constant := ![3, 0, -1, 0, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 26 2, .triangle 30 0, .triangle 33 2, .triangle 21 0, .triangle 20 0, .triangle 31 1, .corridorLower 3 4]

-- Cycle fingerprint 48cb26c1e574bdacc6618f9fbeef48cf9523825f9a45966c74e78bd252554d01.
def localCycle00088 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 2 4, .distance 1 2, .distance 0 1, .theta 1, .theta 0, .zero]
    constant := ![0, 3, -1, -1, -2, -2, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 28 0, .triangle 16 0, .gapLower 1 1, .gapLower 1 0, .thetaNext 0, .thetaLower 0]

-- Cycle fingerprint 4b9a3f191ce618cb30a6a7870e3dcb2f9f57576a3c1902a3c0bd43fe919a3cc0.
def localCycle00089 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 5, .distance 2 4, .distance 1 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 0, .triangle 28 0, .triangle 16 0, .triangle 0 0, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint 4cd99188853bb199a3007464187a44cf514c7b3f5a21d4465fb664df1a2cf58d.
def localCycle00090 : Cycle where
  length := 6
  data := {
    node := ![.distance 1 6, .distance 0 1, .theta 0, .zero, .theta 1, .distance 1 3, .distance 1 6]
    constant := ![-1, -1, 0, 0, 2, -2]
    coefficient := ![0, 0, 0, 1, 1, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.triangle 4 0, .corridorLower 0 1, .thetaLower 0, .thetaUpper 1, .gapLower 1 6, .gapLower 1 5]

-- Cycle fingerprint 4d9747cce40cccce6dd1cdb6847951c6a1daef8f5c7ca1e55c7157a3b6d5b786.
def localCycle00091 : Cycle where
  length := 9
  data := {
    node := ![.distance 2 5, .distance 1 5, .distance 1 2, .distance 0 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 2 3, .distance 2 5]
    constant := ![0, -2, -2, -1, 0, 0, 3, -1, 0]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![true, false, false, false, false, false, false, false, true] }
  origin := ![.triangle 17 2, .gapLower 1 2, .gapLower 1 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 25 0, .triangle 26 2]

-- Cycle fingerprint 4df2797ff84aec05c06b454fa7bd96c60c9426444acc3215b7d339ad10d320b7.
def localCycle00092 : Cycle where
  length := 13
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 1 3, .distance 3 4, .distance 4 5, .distance 0 4, .distance 0 3, .distance 0 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, 0, -1, -1, -1, -1, 0, 0, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, false, true, true, true, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 21 0, .triangle 19 0, .triangle 31 0, .triangle 12 0, .triangle 9 1, .triangle 5 1, .triangle 0 1, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint 4e679e024dd0e7538470f3c83508bf294bf46e168054041fa8b1fa2a8ab67a3e.
def localCycle00093 : Cycle where
  length := 13
  data := {
    node := ![.zero, .theta 3, .distance 2 3, .distance 1 3, .distance 1 4, .distance 4 5, .distance 5 6, .distance 3 5, .distance 3 4, .distance 0 3, .distance 0 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, 0, -1, -1, -1, 0, -1, 0, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, false, false, true, true, false, false] }
  origin := ![.thetaUpper 3, .corridorUpper 2 3, .triangle 15 2, .triangle 19 2, .triangle 22 0, .triangle 34 0, .triangle 33 0, .gapLower 3 2, .triangle 9 0, .triangle 5 1, .triangle 0 1, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint 4ebfe5a9031dbed163e4f2f81d89c74a8282910dc3462faa806ddb9b41c96f33.
def localCycle00094 : Cycle where
  length := 5
  data := {
    node := ![.distance 4 5, .distance 3 5, .distance 1 3, .distance 1 4, .distance 1 5, .distance 4 5]
    constant := ![0, 2, 0, -2, 0]
    coefficient := ![0, 0, 0, 0, 0]
    strict := ![true, true, true, false, true] }
  origin := ![.triangle 31 2, .gapUpper 3 4, .triangle 19 2, .gapLower 1 4, .triangle 22 1]

-- Cycle fingerprint 4f72f2d32f31e6df6ace9d48f866e33c3688a070cdfcfe9fe205173db1811f5a.
def localCycle00095 : Cycle where
  length := 12
  data := {
    node := ![.distance 3 5, .distance 4 5, .distance 0 4, .distance 0 3, .distance 0 1, .theta 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 2 3, .distance 1 3, .distance 3 5]
    constant := ![0, -1, 0, 0, -3, 0, 0, 0, 3, -1, 0, -1]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![true, false, false, true, false, true, false, false, false, false, true, false] }
  origin := ![.triangle 31 1, .triangle 12 0, .gapLower 0 3, .triangle 1 1, .gapLower 1 0, .thetaNext 0, .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 25 0, .triangle 15 2, .triangle 20 0]

-- Cycle fingerprint 4f8cf8ab17969fbf0cde9cdb1804bfc21b9e20a8d8b6516f6c3de0e3b9f81659.
def localCycle00096 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .theta 1, .zero, .theta 3, .distance 2 3, .distance 1 3, .distance 1 4, .distance 1 5, .distance 1 6, .distance 1 2, .distance 0 1]
    constant := ![-2, 0, 0, 3, 0, 0, 0, 0, -2, -1]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, true, true, false, false] }
  origin := ![.gapLower 1 0, .thetaLower 1, .thetaUpper 3, .corridorUpper 2 3, .triangle 15 2, .triangle 19 2, .triangle 22 2, .triangle 24 2, .gapLower 1 2, .triangle 0 0]

-- Cycle fingerprint 4f8df5caaaad985b76250c6fcc75fca3dfd4c31bf768d0eca3e58d34b35a60f1.
def localCycle00097 : Cycle where
  length := 12
  data := {
    node := ![.distance 3 5, .distance 5 6, .distance 0 5, .distance 0 4, .distance 0 1, .theta 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 2 4, .distance 4 5, .distance 3 5]
    constant := ![-1, -1, 0, 0, -3, 0, 0, 0, 3, 0, -1, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, true, false, true, false, false, false, true, false, true] }
  origin := ![.triangle 33 0, .triangle 14 0, .gapLower 0 4, .triangle 2 1, .gapLower 1 0, .thetaNext 0, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 25 2, .triangle 28 0, .triangle 31 2]

-- Cycle fingerprint 4ffd6e37edb57aa0eec9e961fe9241d68657d4fe083af9c9f5b128cfabb45033.
def localCycle00098 : Cycle where
  length := 11
  data := {
    node := ![.theta 1, .zero, .theta 3, .distance 2 3, .distance 2 4, .distance 4 5, .distance 1 5, .distance 1 6, .distance 1 4, .distance 1 2, .distance 0 1, .theta 1]
    constant := ![0, 0, 3, 0, -1, 0, -2, 0, 0, -1, -2]
    coefficient := ![0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, true, true, false, false] }
  origin := ![.thetaLower 1, .thetaUpper 3, .corridorUpper 2 3, .triangle 25 2, .triangle 28 0, .gapLower 5 4, .gapLower 1 4, .triangle 23 1, .triangle 16 1, .triangle 0 0, .gapLower 1 0]

-- Cycle fingerprint 50049a39a11dc73249b0d67c763ee42fbdd4a4059b5b4943143ea16e0550609d.
def localCycle00099 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 2 5, .distance 1 5, .distance 1 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, -1, 0, -2, -2, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 30 0, .triangle 17 2, .gapLower 1 2, .gapLower 1 1, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint 50603a69905c1f19356fff811094eafae584ae55792af04f5931a30342ee19b1.
def localCycle00100 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 2 4, .distance 2 5, .distance 5 6, .distance 4 6, .distance 1 4, .distance 4 5, .distance 3 4, .theta 3]
    constant := ![3, 0, 0, -1, 0, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 25 2, .triangle 28 2, .triangle 30 0, .triangle 34 2, .triangle 23 0, .triangle 22 0, .triangle 31 0, .corridorLower 3 4]

-- Cycle fingerprint 51b23d8ce6360557c742de7c617fb12623565499f12c326a636224fe373edda2.
def localCycle00101 : Cycle where
  length := 4
  data := {
    node := ![.distance 1 3, .distance 1 5, .distance 5 6, .distance 3 6, .distance 1 3]
    constant := ![-3, -1, 0, 2]
    coefficient := ![0, 0, 0, 0]
    strict := ![false, false, true, true] }
  origin := ![.gapLower 1 5, .triangle 24 0, .triangle 33 2, .gapUpper 3 4]

-- Cycle fingerprint 5251ae0bbcd13b908d20bd5bba97db2c20bdaf8e6d4e523b9006f75d6994fd7b.
def localCycle00102 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 2, .distance 0 1, .theta 0, .zero, .theta 5, .distance 4 5, .distance 3 5, .distance 1 3, .distance 1 6, .distance 1 4, .distance 1 2]
    constant := ![-1, -1, 0, 0, 3, 0, -1, 0, -2, -2]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, true, false, false] }
  origin := ![.triangle 0 0, .corridorLower 0 1, .thetaLower 0, .thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 20 0, .triangle 21 2, .gapLower 1 3, .gapLower 1 2]

-- Cycle fingerprint 53025ec84d13af688cacc24536731a8140acd17911f12c724efecadaa8b79a1c.
def localCycle00103 : Cycle where
  length := 3
  data := {
    node := ![.distance 2 4, .distance 1 4, .distance 1 2, .distance 2 4]
    constant := ![0, -3, 2]
    coefficient := ![0, 0, 0]
    strict := ![false, false, true] }
  origin := ![.gapLower 4 3, .gapLower 1 2, .gapUpper 2 2]

-- Cycle fingerprint 5457d76b4753d4b06029748f0eceb36b32636173378c529f9937563fba270f6f.
def localCycle00104 : Cycle where
  length := 13
  data := {
    node := ![.distance 2 4, .distance 4 6, .distance 3 6, .distance 5 6, .distance 1 5, .distance 1 3, .distance 3 4, .distance 0 3, .distance 0 2, .theta 0, .zero, .theta 5, .distance 4 5, .distance 2 4]
    constant := ![-1, 0, 0, -1, 0, -1, -1, 0, -1, 0, 0, 3, -1]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![false, true, true, false, false, false, false, false, false, false, false, false, false] }
  origin := ![.triangle 29 0, .triangle 32 2, .triangle 33 1, .triangle 24 0, .gapLower 1 4, .triangle 19 0, .triangle 9 0, .gapLower 0 2, .corridorLower 0 2, .thetaLower 0, .thetaUpper 5, .corridorUpper 4 5, .triangle 28 0]

-- Cycle fingerprint 5477fcd0ede81eaecca337a0d8b12ba355f6104c3f549c27eef0e1c81536c626.
def localCycle00105 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 2, .distance 0 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 2 3, .distance 2 6, .distance 1 6, .distance 1 5, .distance 1 2]
    constant := ![-2, -1, 0, 0, 3, -1, 0, 0, -2, 0]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, true, false, true] }
  origin := ![.gapLower 1 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 25 0, .triangle 27 2, .triangle 18 2, .gapLower 1 3, .triangle 17 1]

-- Cycle fingerprint 549c5eb3bbd385ecbe7be11f721cdd2e60da07b68f0bea7190b56d4ccd986314.
def localCycle00106 : Cycle where
  length := 8
  data := {
    node := ![.distance 2 4, .distance 4 5, .distance 1 5, .distance 1 6, .distance 3 6, .distance 3 4, .theta 3, .distance 2 3, .distance 2 4]
    constant := ![-1, 0, -2, 0, 0, -1, 3, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 0]
    strict := ![false, false, false, true, true, false, false, true] }
  origin := ![.triangle 28 0, .gapLower 5 4, .gapLower 1 4, .triangle 21 1, .triangle 32 1, .corridorLower 3 4, .corridorUpper 2 3, .triangle 25 2]

-- Cycle fingerprint 54a66e493e3473bde7d002f5ffc7e58e1ffe4133b09ec0113748ba7750338c70.
def localCycle00107 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 3, .distance 1 6, .distance 0 1, .theta 1, .zero, .theta 3, .distance 2 3, .distance 1 3]
    constant := ![-2, -1, -2, 0, 0, 3, 0]
    coefficient := ![0, 0, 0, 0, 1, 1, 0]
    strict := ![false, false, false, false, false, false, true] }
  origin := ![.gapLower 1 5, .triangle 4 0, .gapLower 1 0, .thetaLower 1, .thetaUpper 3, .corridorUpper 2 3, .triangle 15 2]

-- Cycle fingerprint 54de389f5520ed7a272ca17c60a3c7daee10d3ee4c5366ebc3425a573aa018c9.
def localCycle00108 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 3, .distance 0 1, .theta 0, .zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 1 5, .distance 1 6, .distance 1 3]
    constant := ![-1, -1, 0, 0, 3, 0, 0, 0, -2, -2]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, true, false, false] }
  origin := ![.triangle 1 0, .corridorLower 0 1, .thetaLower 0, .thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 17 2, .gapLower 1 5, .gapLower 1 4]

-- Cycle fingerprint 5665f0680b4c18da8e8e80fb05905da9c237343259a8371ef17c7db361a6e497.
def localCycle00109 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 2, .distance 0 1, .theta 0, .zero, .theta 6, .distance 5 6, .distance 2 5, .distance 1 2]
    constant := ![-3, -1, 0, 0, 3, -1, -1]
    coefficient := ![0, 0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 1 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 6, .corridorUpper 5 6, .triangle 30 0, .triangle 17 0]

-- Cycle fingerprint 58565b6605d7a2edf6b7652bb49688c8fdbe23bc60a336b9e70c5ee9c09598e2.
def localCycle00110 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .theta 1, .distance 1 3, .distance 1 5, .distance 5 6, .distance 3 5, .distance 3 4, .distance 0 3, .distance 0 2, .theta 2]
    constant := ![0, 1, 0, -1, -1, 0, -1, 0, 0]
    coefficient := ![0, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![true, false, true, false, false, false, false, false, false] }
  origin := ![.thetaNext 1, .gapLower 1 6, .triangle 20 2, .triangle 24 0, .triangle 33 0, .gapLower 3 2, .triangle 9 0, .gapLower 0 2, .gapLower 2 0]

-- Cycle fingerprint 58ea167ee6847aa7a2642a869da038cf44afe11882bf03c25f498f780ac81964.
def localCycle00111 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 3, .distance 2 6, .distance 1 6, .distance 1 4, .distance 1 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, -1, 0, 0, -2, 0, -2, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, true, false, true, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 0, .triangle 27 2, .triangle 18 2, .gapLower 1 3, .triangle 16 1, .gapLower 1 1, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint 5984d6fa43d19e033670444fa0564bf849ca4806eec6a880766877f1afc8465d.
def localCycle00112 : Cycle where
  length := 3
  data := {
    node := ![.distance 2 6, .distance 1 6, .distance 1 2, .distance 2 6]
    constant := ![0, -3, 2]
    coefficient := ![0, 0, 0]
    strict := ![false, false, true] }
  origin := ![.gapLower 6 5, .gapLower 1 2, .gapUpper 2 2]

-- Cycle fingerprint 5b628ac9fbdb5c5ad14bfc6d8de2e50ae381072ef29b66c9a90ad7f96780ceee.
def localCycle00113 : Cycle where
  length := 9
  data := {
    node := ![.distance 5 6, .distance 1 5, .distance 1 4, .distance 0 1, .theta 1, .zero, .theta 3, .distance 2 3, .distance 2 5, .distance 5 6]
    constant := ![-1, -2, -1, -2, 0, 0, 3, 0, -1]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, false, false, false, false, true, false] }
  origin := ![.triangle 24 0, .gapLower 1 3, .triangle 2 0, .gapLower 1 0, .thetaLower 1, .thetaUpper 3, .corridorUpper 2 3, .triangle 26 2, .triangle 30 0]

-- Cycle fingerprint 5c5367aaaf1419471bec796187428314b600a8a384eb125ae1de49b97e815142.
def localCycle00114 : Cycle where
  length := 9
  data := {
    node := ![.distance 2 3, .distance 1 3, .distance 1 6, .distance 1 5, .distance 1 4, .distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3]
    constant := ![0, -2, 0, -2, -1, -1, 0, 0, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1, 1]
    strict := ![true, false, true, false, false, false, false, false, false] }
  origin := ![.triangle 15 2, .gapLower 1 5, .triangle 24 1, .gapLower 1 3, .triangle 2 0, .corridorLower 0 1, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3]

-- Cycle fingerprint 5c5f31992d733c23ca381660d973decc6636788c5b155f75b6a4271c15453da7.
def localCycle00115 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 3, .distance 3 5, .distance 1 3, .distance 3 6, .distance 5 6, .distance 4 5, .theta 4]
    constant := ![3, -1, -1, -1, -1, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 0, .triangle 26 0, .triangle 20 0, .triangle 21 0, .triangle 33 1, .triangle 34 0, .corridorLower 4 5]

-- Cycle fingerprint 5d7f4e756e9fd7859a54bd06455bef218d84c94aabfa0718092ece6c4ae36417.
def localCycle00116 : Cycle where
  length := 5
  data := {
    node := ![.distance 1 6, .distance 1 5, .distance 1 4, .theta 1, .distance 1 3, .distance 1 6]
    constant := ![0, -2, -1, 2, 0]
    coefficient := ![0, 0, 0, 1, 0]
    strict := ![true, false, false, false, true] }
  origin := ![.triangle 24 1, .gapLower 1 3, .corridorLower 1 4, .gapLower 1 6, .triangle 21 2]

-- Cycle fingerprint 5e48951d5b535ee4878fa9d880a023ed82e94a47f5bbecfb9a90b7b339ab3240.
def localCycle00117 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 1 4, .distance 1 6, .distance 1 3, .distance 3 5, .distance 4 5, .theta 4]
    constant := ![3, 0, 0, 0, -3, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 16 2, .triangle 23 2, .gapLower 1 4, .triangle 20 0, .triangle 31 1, .corridorLower 4 5]

-- Cycle fingerprint 6014ca5488db26008ee8f5ec41c104068cbf5324923d7e9f81466ae032a24954.
def localCycle00118 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 3, .distance 2 3, .distance 2 4, .distance 4 5, .distance 5 6, .distance 3 5, .distance 3 4, .distance 0 3, .distance 0 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, -1, -1, -1, 0, -1, 0, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false, true, true, false, false] }
  origin := ![.thetaUpper 3, .corridorUpper 2 3, .triangle 25 2, .triangle 28 0, .triangle 34 0, .triangle 33 0, .gapLower 3 2, .triangle 9 0, .triangle 5 1, .triangle 0 1, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint 60171e38f13fa758a7244d9562a23afc62d2d11d7b20b97bc169161a8f1aa609.
def localCycle00119 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 4, .distance 1 2, .distance 0 1, .theta 0, .zero, .theta 5, .distance 4 5, .distance 3 5, .distance 1 3, .distance 1 6, .distance 1 4]
    constant := ![-2, -1, -1, 0, 0, 3, 0, -1, -2, 0]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, false, false, true] }
  origin := ![.gapLower 1 2, .triangle 0 0, .corridorLower 0 1, .thetaLower 0, .thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 20 0, .gapLower 1 4, .triangle 23 1]

-- Cycle fingerprint 6094f8fe029613e367e61206372f3d5afd207f912556146ecc155e9fc2701946.
def localCycle00120 : Cycle where
  length := 10
  data := {
    node := ![.distance 2 4, .distance 4 6, .distance 4 5, .distance 1 4, .distance 1 2, .distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 2 4]
    constant := ![-1, 0, -1, 0, -2, -1, 0, 0, 3, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![false, true, false, false, false, false, false, false, false, true] }
  origin := ![.triangle 29 0, .triangle 34 1, .triangle 22 0, .gapLower 1 2, .gapLower 1 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 25 2]

-- Cycle fingerprint 619f5c922636350aff19be26fd258ab111c9266c6cf903609165ecca8218f95f.
def localCycle00121 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 2 4, .distance 4 6, .distance 3 4, .distance 0 3, .distance 0 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, -1, -1, -1, -1, 0, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, true, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 28 0, .triangle 29 0, .triangle 32 0, .triangle 9 0, .triangle 5 1, .triangle 0 1, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint 61c1e576151f8d8683082148f5bcb6ba2efdec6a35633d5b9d317099a5215a88.
def localCycle00122 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 2 3, .distance 3 4, .distance 1 3, .distance 3 5, .distance 4 5, .distance 0 4, .theta 0, .zero]
    constant := ![0, 3, 0, 0, -1, -1, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, false, true, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 27 0, .triangle 25 0, .triangle 19 0, .triangle 20 0, .triangle 31 1, .triangle 12 0, .corridorLower 0 4, .thetaLower 0]

-- Cycle fingerprint 61c85fba578da37f371886f318bb87800286060c3edeaeb47871cdef18ac9ce7.
def localCycle00123 : Cycle where
  length := 8
  data := {
    node := ![.theta 0, .zero, .theta 3, .distance 2 3, .distance 1 3, .distance 1 6, .distance 1 5, .distance 0 1, .theta 0]
    constant := ![0, 0, 3, 0, -2, -2, -1, -1]
    coefficient := ![0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, false] }
  origin := ![.thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 15 2, .gapLower 1 5, .gapLower 1 4, .triangle 3 0, .corridorLower 0 1]

-- Cycle fingerprint 62af5fdc79a8950fb2f8ad8faa59cda5ac33ab9343b0c132ca81836ff73645a8.
def localCycle00124 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 3, .distance 2 3, .distance 1 3, .distance 1 4, .distance 1 6, .distance 4 6, .distance 3 4, .distance 0 3, .distance 0 2, .distance 0 1, .theta 1, .zero]
    constant := ![0, 3, 0, 0, -2, 0, -1, -1, 0, 0, -2, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, true, false, false, false, true, false, false] }
  origin := ![.thetaUpper 3, .corridorUpper 2 3, .triangle 15 2, .triangle 19 2, .gapLower 1 4, .triangle 23 1, .triangle 32 0, .triangle 9 0, .gapLower 0 2, .triangle 0 1, .gapLower 1 0, .thetaLower 1]

-- Cycle fingerprint 631f50b45c814eb6f865325842106f2a257e6867206d74dcaf9ce29d143f72ab.
def localCycle00125 : Cycle where
  length := 13
  data := {
    node := ![.distance 2 5, .distance 1 5, .distance 1 6, .distance 1 3, .distance 3 4, .distance 0 3, .distance 0 2, .distance 0 1, .theta 0, .zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 5]
    constant := ![0, 0, -3, -1, -1, 0, 0, -1, 0, 0, 3, 0, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![true, true, false, false, false, true, true, false, false, false, false, true, true] }
  origin := ![.triangle 17 2, .triangle 24 2, .gapLower 1 4, .triangle 19 0, .triangle 9 0, .triangle 5 1, .triangle 0 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 2]

-- Cycle fingerprint 63446f4bcb0cbdd3ad0f65dc9bcd0be360895cded03dbf1cbeb30ac875a898bc.
def localCycle00126 : Cycle where
  length := 6
  data := {
    node := ![.theta 3, .distance 3 5, .distance 2 3, .distance 3 6, .distance 1 3, .distance 3 4, .theta 3]
    constant := ![4, -1, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 3 6, .triangle 26 0, .triangle 27 0, .triangle 21 0, .triangle 19 0, .corridorLower 3 4]

-- Cycle fingerprint 63fad65c36bbbe445c6e17c8b1d6b01f64f647d7055aa75354ff50bdc1ca4f44.
def localCycle00127 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 4, .distance 1 2, .distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 1 3, .distance 1 5, .distance 1 6, .distance 1 4]
    constant := ![0, -1, -1, 0, 0, 3, 0, 0, -2, -2]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![true, false, false, false, false, false, true, true, false, false] }
  origin := ![.triangle 16 1, .triangle 0 0, .corridorLower 0 1, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 15 2, .triangle 20 2, .gapLower 1 4, .gapLower 1 3]

-- Cycle fingerprint 6416c2807649de051063811dd4db7970c47a0958ec8c0ec287db9fa89dc0510f.
def localCycle00128 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 1, .distance 1 4, .distance 1 3, .distance 3 5, .distance 4 5, .distance 0 4, .distance 0 3, .theta 0, .zero]
    constant := ![0, 1, 0, -1, 0, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false, false, false] }
  origin := ![.thetaUpper 1, .gapLower 1 6, .triangle 19 1, .triangle 20 0, .triangle 31 1, .triangle 12 0, .gapLower 0 3, .corridorLower 0 3, .thetaLower 0]

-- Cycle fingerprint 6442cccb1047c7f2c884c0373b1602767aacb56cd5c991c35956f9f78c56a9af.
def localCycle00129 : Cycle where
  length := 13
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 5 6, .distance 1 5, .distance 1 3, .distance 3 4, .distance 0 3, .distance 0 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, 0, -1, -1, 0, -1, -1, 0, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, true, false, false, true, true, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 30 0, .triangle 24 0, .triangle 20 1, .triangle 19 0, .triangle 9 0, .triangle 5 1, .triangle 0 1, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint 6480b45257efea2366d4a8c28e5859871beeaa96f9bbfdb3f2e68aa9a94330b6.
def localCycle00130 : Cycle where
  length := 14
  data := {
    node := ![.distance 1 6, .distance 1 3, .distance 3 5, .distance 4 5, .distance 0 4, .distance 0 3, .distance 0 2, .distance 0 1, .theta 1, .zero, .theta 4, .distance 3 4, .distance 2 4, .distance 1 4, .distance 1 6]
    constant := ![-2, -1, 0, -1, 0, 0, 0, -2, 0, 0, 3, 0, 0, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, true, false, false, false, true, false, false, false, false, true, true, true] }
  origin := ![.gapLower 1 4, .triangle 20 0, .triangle 31 1, .triangle 12 0, .gapLower 0 3, .gapLower 0 2, .triangle 0 1, .gapLower 1 0, .thetaLower 1, .thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 16 2, .triangle 23 2]

-- Cycle fingerprint 649ff1b1af4735113c14c0f678b90b1efc9b6f068665f72f8a93f0e4ea088360.
def localCycle00131 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 5, .distance 1 3, .distance 3 4, .distance 4 6, .distance 5 6, .distance 0 5, .distance 0 3, .theta 3]
    constant := ![3, -1, -1, -1, -1, 0, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 26 0, .triangle 20 0, .triangle 19 0, .triangle 32 0, .triangle 34 1, .triangle 14 0, .triangle 10 1, .gapLower 3 0]

-- Cycle fingerprint 64aecff618643262854e0b2df45183f4d9679d498e64639757924150fa00be49.
def localCycle00132 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 6, .distance 1 3, .distance 3 5, .distance 4 5, .distance 0 4, .distance 0 3, .theta 0, .zero, .theta 1, .distance 1 4, .distance 1 6]
    constant := ![0, -1, 0, -1, 0, -1, 0, 0, 2, -2]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![true, false, true, false, false, false, false, false, false, false] }
  origin := ![.triangle 21 1, .triangle 20 0, .triangle 31 1, .triangle 12 0, .gapLower 0 3, .corridorLower 0 3, .thetaLower 0, .thetaUpper 1, .gapLower 1 6, .gapLower 1 5]

-- Cycle fingerprint 65ef31df02abcba2a1957c64fb7ca0f44d5ea6f0e4489a0a35d3d8abb5c6beaf.
def localCycle00133 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 2 3, .distance 2 4, .distance 4 6, .distance 1 4, .distance 4 5, .distance 3 4, .theta 3]
    constant := ![3, 0, -1, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 25 2, .triangle 29 0, .triangle 23 0, .triangle 22 0, .triangle 31 0, .corridorLower 3 4]

-- Cycle fingerprint 676ac0892a795940cd49ff2aa66fe5778a1a64826bc60ee5ceb908e513ad69c0.
def localCycle00134 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 1, .distance 1 3, .distance 1 5, .distance 1 6, .distance 1 4, .distance 1 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 2, 0, -2, 0, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, true, false, false, false] }
  origin := ![.thetaUpper 1, .gapLower 1 6, .triangle 20 2, .gapLower 1 4, .triangle 23 1, .triangle 16 1, .triangle 0 0, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint 680c2751dd2fe91a73b09949334e398a1671f14aa2fb33d069de1e363d106990.
def localCycle00135 : Cycle where
  length := 3
  data := {
    node := ![.distance 2 5, .distance 1 5, .distance 1 2, .distance 2 5]
    constant := ![0, -3, 2]
    coefficient := ![0, 0, 0]
    strict := ![false, false, true] }
  origin := ![.gapLower 5 4, .gapLower 1 2, .gapUpper 2 2]

-- Cycle fingerprint 6828f328a0752ef80dc56c5fb15dc3ce4e2ab8572075f0611e3c5b227fe47508.
def localCycle00136 : Cycle where
  length := 4
  data := {
    node := ![.distance 1 3, .distance 1 4, .distance 4 6, .distance 3 6, .distance 1 3]
    constant := ![-2, -1, 0, 2]
    coefficient := ![0, 0, 0, 0]
    strict := ![false, false, true, true] }
  origin := ![.gapLower 1 5, .triangle 23 0, .triangle 32 2, .gapUpper 3 4]

-- Cycle fingerprint 685fcdd70faa84e83c1f1e187b55ec9f06bc61a27ae598f7d16f197f7cf71f15.
def localCycle00137 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 1 3, .distance 1 5, .distance 1 2, .distance 0 1, .theta 1, .zero]
    constant := ![0, 3, -1, 0, -2, -1, -2, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 19 0, .triangle 20 2, .gapLower 1 2, .triangle 0 0, .gapLower 1 0, .thetaLower 1]

-- Cycle fingerprint 68de44c4ca644f5e0d6d950180ff8b7a276b530cc0594e59617b5e5e278ac1df.
def localCycle00138 : Cycle where
  length := 9
  data := {
    node := ![.distance 3 5, .distance 1 3, .distance 1 6, .distance 1 2, .distance 0 1, .theta 0, .zero, .theta 5, .distance 4 5, .distance 3 5]
    constant := ![-1, -2, 0, -2, -1, 0, 0, 3, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![false, false, true, false, false, false, false, false, true] }
  origin := ![.triangle 20 0, .gapLower 1 4, .triangle 18 1, .gapLower 1 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 5, .corridorUpper 4 5, .triangle 31 2]

-- Cycle fingerprint 6b406c3377ac91bed2f0ebdc72fc3ee89b6d8c6e826fc2dfa2dbe00af4d80bf2.
def localCycle00139 : Cycle where
  length := 8
  data := {
    node := ![.distance 5 6, .distance 1 5, .distance 1 3, .distance 3 4, .theta 3, .distance 3 5, .distance 2 3, .distance 3 6, .distance 5 6]
    constant := ![-1, 0, -1, -1, 4, -1, -1, 0]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false, true] }
  origin := ![.triangle 24 0, .triangle 20 1, .triangle 19 0, .corridorLower 3 4, .gapLower 3 6, .triangle 26 0, .triangle 27 0, .triangle 33 1]

-- Cycle fingerprint 6b5d3998cf5b0c6f5a3719daa42448e17af3e178fa8d75453046a61dff82d450.
def localCycle00140 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 3, .distance 2 3, .distance 3 4, .distance 3 5, .distance 1 3, .distance 3 6, .distance 5 6, .distance 4 5, .distance 0 4, .theta 0, .zero]
    constant := ![0, 3, -1, 0, -1, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, true, false, false, false, false] }
  origin := ![.thetaUpper 3, .corridorUpper 2 3, .triangle 25 0, .triangle 31 2, .triangle 20 0, .triangle 21 0, .triangle 33 1, .triangle 34 0, .triangle 12 0, .corridorLower 0 4, .thetaLower 0]

-- Cycle fingerprint 6bfbee10f28bc8c86e12073ea2dede7d37ee933e8d01bab07150767f7f834b40.
def localCycle00141 : Cycle where
  length := 4
  data := {
    node := ![.distance 1 5, .distance 1 3, .distance 3 6, .distance 5 6, .distance 1 5]
    constant := ![-2, -1, 0, 2]
    coefficient := ![0, 0, 0, 0]
    strict := ![false, false, true, true] }
  origin := ![.gapLower 1 5, .triangle 21 0, .triangle 33 1, .gapUpper 5 2]

-- Cycle fingerprint 6d64c9942f3455139f3cea6cd8a0bffd3f45d01e0757ddc4d313b9a218380c81.
def localCycle00142 : Cycle where
  length := 8
  data := {
    node := ![.distance 1 2, .distance 0 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 2 3, .distance 2 5, .distance 1 2]
    constant := ![-2, -1, 0, 0, 3, -1, 0, -1]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, false] }
  origin := ![.gapLower 1 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 25 0, .triangle 26 2, .triangle 17 0]

-- Cycle fingerprint 6d83ccabe2fc2b444e831be17fa95ef31ce72a091c580abf41e0232afff12732.
def localCycle00143 : Cycle where
  length := 3
  data := {
    node := ![.distance 4 6, .distance 1 4, .distance 1 6, .distance 4 6]
    constant := ![2, -3, 0]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.gapUpper 4 4, .gapLower 1 4, .triangle 23 1]

-- Cycle fingerprint 6e7f248e373a0d7d7b1a831223b03625b80c651650e32b7b5ab33a943bc9635e.
def localCycle00144 : Cycle where
  length := 11
  data := {
    node := ![.distance 4 5, .distance 3 4, .distance 0 3, .distance 0 2, .theta 0, .zero, .theta 1, .distance 1 3, .distance 1 4, .distance 1 6, .distance 1 5, .distance 4 5]
    constant := ![-1, -1, 0, -1, 0, 0, 2, 0, 0, -2, 0]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, true, true, false, true] }
  origin := ![.triangle 31 0, .triangle 9 0, .gapLower 0 2, .corridorLower 0 2, .thetaLower 0, .thetaUpper 1, .gapLower 1 6, .triangle 19 2, .triangle 23 2, .gapLower 1 3, .triangle 22 1]

-- Cycle fingerprint 6f1ff3ab3820f98f5da077b891507513aa60d209548acc38a6f92d039031eb4f.
def localCycle00145 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 4 6, .distance 2 4, .distance 1 4, .distance 1 3, .distance 3 5, .distance 4 5, .theta 4]
    constant := ![3, -1, -1, 0, 0, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 32 0, .triangle 29 0, .triangle 16 2, .triangle 19 1, .triangle 20 0, .triangle 31 1, .corridorLower 4 5]

-- Cycle fingerprint 72e1577392d2ab5740dc68cfc981a39cbcbee235919f771184c1a5c8ce8b52c0.
def localCycle00146 : Cycle where
  length := 8
  data := {
    node := ![.distance 2 5, .distance 5 6, .distance 1 6, .distance 1 5, .distance 3 5, .distance 3 4, .theta 3, .distance 2 3, .distance 2 5]
    constant := ![-1, 0, -2, 0, 0, -1, 3, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 0]
    strict := ![false, false, false, true, true, false, false, true] }
  origin := ![.triangle 30 0, .gapLower 6 3, .gapLower 1 4, .triangle 20 1, .triangle 31 1, .corridorLower 3 4, .corridorUpper 2 3, .triangle 26 2]

-- Cycle fingerprint 73f028b8165c84340ef330b85e66187ec19edfd7340563a62df9b3951c0b8fb5.
def localCycle00147 : Cycle where
  length := 5
  data := {
    node := ![.theta 5, .distance 3 5, .distance 2 3, .distance 2 6, .theta 6, .theta 5]
    constant := ![3, -1, 0, -2, 0]
    coefficient := ![1, 0, 0, -1, 0]
    strict := ![false, false, true, true, true] }
  origin := ![.corridorUpper 3 5, .triangle 26 0, .triangle 27 2, .gapUpper 6 6, .thetaNext 5]

-- Cycle fingerprint 774c55349f81aec08ea5de3e4defb74a7236b7b253b6616fe412fb6299305c1f.
def localCycle00148 : Cycle where
  length := 3
  data := {
    node := ![.distance 5 6, .distance 1 5, .distance 1 6, .distance 5 6]
    constant := ![2, -3, 0]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.gapUpper 5 2, .gapLower 1 5, .triangle 24 1]

-- Cycle fingerprint 77f62b8c45e539414f35543cdc11ef579cebfb20b149e3971c10af27e0990065.
def localCycle00149 : Cycle where
  length := 8
  data := {
    node := ![.theta 0, .zero, .theta 4, .distance 3 4, .distance 1 3, .distance 1 6, .distance 1 2, .distance 0 1, .theta 0]
    constant := ![0, 0, 3, -1, -2, 0, -2, -1]
    coefficient := ![0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, false] }
  origin := ![.thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 19 0, .gapLower 1 4, .triangle 18 1, .gapLower 1 1, .corridorLower 0 1]

-- Cycle fingerprint 78602a9deeb7032317240f917a59b818370aaa1eafa286bcc8ea0e6f7fd215a4.
def localCycle00150 : Cycle where
  length := 13
  data := {
    node := ![.distance 1 3, .distance 1 4, .distance 1 5, .distance 1 6, .distance 4 6, .distance 3 4, .distance 0 3, .distance 0 2, .distance 0 1, .theta 1, .zero, .theta 3, .distance 2 3, .distance 1 3]
    constant := ![0, 0, -2, 0, -1, -1, 0, 0, -2, 0, 0, 3, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![true, true, false, true, false, false, false, true, false, false, false, false, true] }
  origin := ![.triangle 19 2, .triangle 22 2, .gapLower 1 3, .triangle 23 1, .triangle 32 0, .triangle 9 0, .gapLower 0 2, .triangle 0 1, .gapLower 1 0, .thetaLower 1, .thetaUpper 3, .corridorUpper 2 3, .triangle 15 2]

-- Cycle fingerprint 78a22de08a9d92baaab88d3e5ed0e9f1da0ef7cc76f7cc234f00c2a5e6dcaa10.
def localCycle00151 : Cycle where
  length := 11
  data := {
    node := ![.theta 0, .zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 1 5, .distance 1 6, .distance 1 4, .distance 1 2, .distance 0 1, .theta 0]
    constant := ![0, 0, 3, 0, 0, 0, -2, 0, -2, -1, -1]
    coefficient := ![0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, true, false, true, false, false, false] }
  origin := ![.thetaLower 0, .thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 17 2, .gapLower 1 5, .triangle 23 1, .gapLower 1 2, .triangle 0 0, .corridorLower 0 1]

-- Cycle fingerprint 7a4aee3c1865bb4249b7973deeb9ba54af9e3d8f552fa400f6a3d846b91c32d5.
def localCycle00152 : Cycle where
  length := 9
  data := {
    node := ![.distance 2 5, .distance 1 2, .distance 0 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 2 3, .distance 2 6, .distance 2 5]
    constant := ![-1, -3, -1, 0, 0, 3, -1, 0, 0]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, true, true] }
  origin := ![.triangle 17 0, .gapLower 1 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 25 0, .triangle 27 2, .triangle 30 1]

-- Cycle fingerprint 7b329e99e755d51319f40a40d9d0822f60fd095afdbc9afc35cbfb861f1d4bb0.
def localCycle00153 : Cycle where
  length := 9
  data := {
    node := ![.distance 3 5, .distance 5 6, .distance 1 5, .distance 1 3, .distance 3 4, .theta 3, .distance 2 3, .distance 2 4, .distance 4 5, .distance 3 5]
    constant := ![-1, -1, 0, -1, -1, 3, 0, -1, 0]
    coefficient := ![0, 0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, false, true] }
  origin := ![.triangle 33 0, .triangle 24 0, .gapLower 1 4, .triangle 19 0, .corridorLower 3 4, .corridorUpper 2 3, .triangle 25 2, .triangle 28 0, .triangle 31 2]

-- Cycle fingerprint 7bcc8e31d45f0d2345ca483a32032c17bfd25c6f017c1a247331a53114a6fba5.
def localCycle00154 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .theta 1, .distance 1 3, .distance 1 4, .distance 4 5, .distance 3 5, .distance 5 6, .distance 0 5, .distance 0 4, .distance 0 1]
    constant := ![0, 1, 0, -1, 0, -1, -1, 0, 0]
    coefficient := ![0, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false, false, true] }
  origin := ![.gapLower 1 0, .gapLower 1 6, .triangle 19 2, .triangle 22 0, .triangle 31 2, .triangle 33 0, .triangle 14 0, .gapLower 0 4, .triangle 2 1]

-- Cycle fingerprint 7c809b178a96e6558457d75a4e650a0bfedce7b0e5827433670f336db9d96a40.
def localCycle00155 : Cycle where
  length := 3
  data := {
    node := ![.distance 3 5, .distance 1 3, .distance 1 5, .distance 3 5]
    constant := ![2, -3, 0]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.gapUpper 3 2, .gapLower 1 3, .triangle 20 1]

-- Cycle fingerprint 7d2e41231421f840d9e4f10c140f13605ad72aaae54c16965ace81912fa4362a.
def localCycle00156 : Cycle where
  length := 8
  data := {
    node := ![.theta 0, .zero, .theta 3, .distance 2 3, .distance 1 3, .distance 1 5, .distance 1 6, .distance 0 1, .theta 0]
    constant := ![0, 0, 3, 0, -2, -2, -1, -1]
    coefficient := ![0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, false] }
  origin := ![.thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 15 2, .gapLower 1 5, .gapLower 1 4, .triangle 4 0, .corridorLower 0 1]

-- Cycle fingerprint 7e2076cad34f2079c89af3fefbc6f194fbb349628e40483cb6f47517cd9dff76.
def localCycle00157 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 5, .distance 0 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 2 4, .distance 1 4, .distance 1 6, .distance 1 3, .distance 1 5]
    constant := ![-1, -1, 0, 0, 3, 0, 0, 0, -2, -2]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, true, false, false] }
  origin := ![.triangle 3 0, .corridorLower 0 1, .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 16 2, .triangle 23 2, .gapLower 1 4, .gapLower 1 3]

-- Cycle fingerprint 80888152f3b6be393c6fe20129525f4d754608fa6b24533692cde1d2ab61a50e.
def localCycle00158 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 3, .distance 1 4, .distance 1 5, .distance 1 6, .distance 4 6, .distance 3 4, .theta 3]
    constant := ![3, 0, 0, 0, -3, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, true, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 2, .triangle 19 2, .triangle 22 2, .gapLower 1 3, .triangle 23 1, .triangle 32 0, .corridorLower 3 4]

-- Cycle fingerprint 82b9ba9495b268d85010da11849e219c29532b90c6ff4a6fd80d857e34911334.
def localCycle00159 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 6, .distance 1 5, .distance 1 2, .distance 0 1, .theta 1, .zero, .theta 4, .distance 3 4, .distance 1 3, .distance 1 6]
    constant := ![0, -2, -1, -2, 0, 0, 3, -1, 0]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![true, false, false, false, false, false, false, false, true] }
  origin := ![.triangle 24 1, .gapLower 1 2, .triangle 0 0, .gapLower 1 0, .thetaLower 1, .thetaUpper 4, .corridorUpper 3 4, .triangle 19 0, .triangle 21 2]

-- Cycle fingerprint 82be5e13e5a977f4d67abef83066370c2e7f1a10733a3916755b6ea8dea421af.
def localCycle00160 : Cycle where
  length := 11
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 2 3, .distance 2 6, .distance 2 4, .distance 1 2, .distance 0 1, .theta 1, .theta 0, .zero, .theta 5]
    constant := ![3, 0, -1, 0, 0, -1, -2, -2, 0, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, false, true, true, false, false, false, true, false, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 26 0, .triangle 27 2, .triangle 29 1, .triangle 16 0, .gapLower 1 1, .gapLower 1 0, .thetaNext 0, .thetaLower 0, .thetaUpper 5]

-- Cycle fingerprint 82c356938f38be75652a4625c1c373b80efafcacd6ea871422597613875e5ae4.
def localCycle00161 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 5, .distance 4 5, .distance 1 4, .distance 1 2, .distance 0 1]
    constant := ![-1, 0, 0, 3, -1, -2, -1]
    coefficient := ![0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 5, .corridorUpper 4 5, .triangle 22 0, .gapLower 1 2, .triangle 0 0]

-- Cycle fingerprint 82defdc70a19f7c8ac0bd498b9421858911c79de443412852bc94b3cbe7ee983.
def localCycle00162 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 2 4, .distance 4 6, .distance 3 6, .distance 1 3, .distance 1 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, -1, -1, 0, -1, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, true, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 28 0, .triangle 29 0, .triangle 32 2, .triangle 21 0, .triangle 15 1, .triangle 0 0, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint 837f1631132dbc9b28b8f8322a653c03ee336c0a9d4ab870ca0d94cfd30d0a1d.
def localCycle00163 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 6, .distance 1 3, .distance 3 4, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true] }
  origin := ![.corridorUpper 2 3, .triangle 27 0, .triangle 21 0, .triangle 19 0, .triangle 31 0, .corridorLower 4 5, .thetaNext 3]

-- Cycle fingerprint 83cea9d12a9a21e0749fc01bad7566e55a0365c4cf4be7e8cec6b76ef133fb8c.
def localCycle00164 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 2 4, .distance 4 6, .distance 1 6, .distance 1 5, .distance 3 5, .distance 3 4, .theta 3]
    constant := ![3, 0, -1, 0, -3, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, true, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 25 2, .triangle 29 0, .gapLower 6 3, .gapLower 1 4, .triangle 20 1, .triangle 31 1, .corridorLower 3 4]

-- Cycle fingerprint 83d3184bd2dff112cb402d98372e1b533ca9661d877963c4825ca62ae46823cd.
def localCycle00165 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 2, .distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 1 3, .distance 1 4, .distance 1 6, .distance 1 5, .distance 1 2]
    constant := ![-1, -1, 0, 0, 3, 0, 0, 0, -2, -2]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, true, false, false] }
  origin := ![.triangle 0 0, .corridorLower 0 1, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 15 2, .triangle 19 2, .triangle 23 2, .gapLower 1 3, .gapLower 1 2]

-- Cycle fingerprint 8479db6d307a9a165be2b16aa3b15802d38cb3ccb2177f3c264a6f3749d47d2b.
def localCycle00166 : Cycle where
  length := 5
  data := {
    node := ![.distance 5 6, .distance 3 6, .distance 1 3, .distance 1 5, .distance 1 6, .distance 5 6]
    constant := ![0, 2, 0, -2, 0]
    coefficient := ![0, 0, 0, 0, 0]
    strict := ![true, true, true, false, true] }
  origin := ![.triangle 33 2, .gapUpper 3 4, .triangle 20 2, .gapLower 1 4, .triangle 24 1]

-- Cycle fingerprint 84cb98fceaed0995746b442e538f9e44c030bc32a41a57d217531e9f52cb6020.
def localCycle00167 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 4, .distance 1 3, .distance 1 5, .distance 5 6, .distance 3 5, .theta 3]
    constant := ![3, -1, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 25 0, .triangle 19 0, .triangle 20 2, .triangle 24 0, .triangle 33 0, .corridorLower 3 5]

-- Cycle fingerprint 84e3a278fe473a451a048f786862b3eda8951361e07ae219377ecef029baa9f3.
def localCycle00168 : Cycle where
  length := 7
  data := {
    node := ![.distance 5 6, .distance 1 5, .distance 1 3, .distance 3 4, .theta 3, .distance 2 3, .distance 3 5, .distance 5 6]
    constant := ![-1, 0, -1, -1, 3, -1, -1]
    coefficient := ![0, 0, 0, 0, 1, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.triangle 24 0, .gapLower 1 4, .triangle 19 0, .corridorLower 3 4, .corridorUpper 2 3, .triangle 26 0, .triangle 33 0]

-- Cycle fingerprint 852514eb1257b255a3ad0254c3315234e05645632b33b10a6fed1c8a12fbe4bb.
def localCycle00169 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 2 4, .distance 4 5, .distance 5 6, .distance 3 5, .distance 1 3, .distance 3 4, .theta 3]
    constant := ![3, 0, -1, -1, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 25 2, .triangle 28 0, .triangle 34 0, .triangle 33 0, .triangle 20 0, .triangle 19 0, .corridorLower 3 4]

-- Cycle fingerprint 85486d0474bd8c9160f8d62cd08dd5c5dfd02b62f661862560eb6f34d5a76f72.
def localCycle00170 : Cycle where
  length := 9
  data := {
    node := ![.distance 2 3, .distance 1 3, .distance 1 5, .distance 1 4, .distance 1 2, .distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3]
    constant := ![0, -2, 0, -2, -1, -1, 0, 0, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1, 1]
    strict := ![true, false, true, false, false, false, false, false, false] }
  origin := ![.triangle 15 2, .gapLower 1 5, .triangle 22 1, .gapLower 1 2, .triangle 0 0, .corridorLower 0 1, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3]

-- Cycle fingerprint 8671a6d07e97431c718efee40d5b8202b7f977b9ab9dea5bb44e424b54456331.
def localCycle00171 : Cycle where
  length := 7
  data := {
    node := ![.theta 6, .distance 5 6, .distance 2 5, .distance 1 2, .distance 0 1, .theta 0, .zero, .theta 6]
    constant := ![3, -1, -1, -2, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 1]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.corridorUpper 5 6, .triangle 30 0, .triangle 17 0, .gapLower 1 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 6]

-- Cycle fingerprint 8826069bc41f788bffc10f25ee2bbac7a002fdf2028fea2fabf7d4885c64dbf8.
def localCycle00172 : Cycle where
  length := 3
  data := {
    node := ![.distance 3 6, .distance 1 3, .distance 1 6, .distance 3 6]
    constant := ![2, -3, 0]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.gapUpper 3 3, .gapLower 1 4, .triangle 21 1]

-- Cycle fingerprint 887a48e65db2e281349c6b209cc4c6078692857d4a92ea80775004063c940a4c.
def localCycle00173 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 2 4, .distance 1 4, .distance 1 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, -1, 0, -2, -2, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 28 0, .triangle 16 2, .gapLower 1 2, .gapLower 1 1, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint 88871acb6cc7e7a331edce28d4c10dc1e71a16f9f7694c6e5cb8dc5f0e63f15a.
def localCycle00174 : Cycle where
  length := 4
  data := {
    node := ![.distance 1 4, .distance 1 2, .distance 2 5, .distance 4 5, .distance 1 4]
    constant := ![-3, 2, 0, -1]
    coefficient := ![0, 0, 0, 0]
    strict := ![false, true, false, false] }
  origin := ![.gapLower 1 2, .gapUpper 2 2, .gapLower 5 4, .triangle 22 0]

-- Cycle fingerprint 8a4654c2e8cf5a195eafe7821b0de879fbda65e15d8f2abae62f975e347606ee.
def localCycle00175 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 3, .distance 2 3, .distance 3 5, .distance 1 3, .distance 3 6, .distance 3 4, .distance 0 3, .distance 0 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, -1, -1, -1, 0, -1, 0, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, true, true, false, false] }
  origin := ![.thetaUpper 3, .corridorUpper 2 3, .triangle 26 0, .triangle 20 0, .triangle 21 0, .triangle 32 1, .triangle 9 0, .triangle 5 1, .triangle 0 1, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint 8aaa6095975f36095b3de42713356003a791a260090f966c2f5299ef17c6f22f.
def localCycle00176 : Cycle where
  length := 6
  data := {
    node := ![.theta 0, .zero, .theta 3, .distance 2 3, .distance 1 2, .distance 0 1, .theta 0]
    constant := ![0, 0, 3, -1, -3, -1]
    coefficient := ![0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 15 0, .gapLower 1 1, .corridorLower 0 1]

-- Cycle fingerprint 8ac878d008cdfa0e5058ec4cc84283995da2edd92b8f8d5d77a4a518873eaa93.
def localCycle00177 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 1, .distance 1 5, .distance 1 6, .distance 1 3, .distance 3 4, .distance 0 3, .distance 0 2, .theta 0, .zero]
    constant := ![0, 2, 0, -2, -1, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false, false] }
  origin := ![.thetaUpper 1, .gapLower 1 6, .triangle 24 2, .gapLower 1 4, .triangle 19 0, .triangle 9 0, .gapLower 0 2, .corridorLower 0 2, .thetaLower 0]

-- Cycle fingerprint 8b81a1f8a5ac33de67657f2a3c9b2df6e61cc9b3ca5a2bf9a771587733baf0d2.
def localCycle00178 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 2, .distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 1 3, .distance 1 4, .distance 1 6, .distance 1 5, .distance 1 2]
    constant := ![-2, -1, 0, 0, 3, 0, 0, 0, -2, 0]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, true, false, true] }
  origin := ![.gapLower 1 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 15 2, .triangle 19 2, .triangle 23 2, .gapLower 1 3, .triangle 17 1]

-- Cycle fingerprint 8c97446fbf6816699186a1a135ccddae118488799168def45401b2caa20a77bf.
def localCycle00179 : Cycle where
  length := 6
  data := {
    node := ![.distance 1 4, .distance 1 5, .distance 1 6, .distance 1 2, .theta 1, .distance 1 3, .distance 1 4]
    constant := ![0, 0, -2, -1, 2, 0]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![true, true, false, false, false, true] }
  origin := ![.triangle 22 2, .triangle 24 2, .gapLower 1 2, .corridorLower 1 2, .gapLower 1 6, .triangle 19 2]

-- Cycle fingerprint 8d1db3f8cb1e725614c432d574ab0e7cbbc13aff64d1ccc74db7ee22f09d9c3c.
def localCycle00180 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 3, .distance 3 5, .distance 4 5, .distance 1 4, .distance 4 6, .theta 4]
    constant := ![3, -1, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 0, .triangle 26 0, .triangle 31 1, .triangle 22 0, .triangle 23 0, .corridorLower 4 6]

-- Cycle fingerprint 8e02727d877794cfaa64edb46a0df35c087bbfef8a1046459c222e37ac314138.
def localCycle00181 : Cycle where
  length := 13
  data := {
    node := ![.zero, .theta 3, .distance 2 3, .distance 3 4, .distance 1 4, .distance 4 5, .distance 5 6, .distance 0 5, .distance 0 4, .distance 0 3, .distance 0 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, -1, 0, -1, -1, -1, 0, 0, 0, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, true, true, true, true, false, false] }
  origin := ![.thetaUpper 3, .corridorUpper 2 3, .triangle 25 0, .triangle 19 2, .triangle 22 0, .triangle 34 0, .triangle 14 0, .triangle 12 1, .triangle 9 1, .triangle 5 1, .triangle 0 1, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint 8f52677f4b61ba22cb9e5633c9a0a331301fbb8b2647a99d5eb4125bfb1435d5.
def localCycle00182 : Cycle where
  length := 9
  data := {
    node := ![.distance 3 6, .distance 4 6, .distance 1 4, .distance 1 3, .distance 3 5, .distance 4 5, .theta 4, .distance 3 4, .distance 2 3, .distance 3 6]
    constant := ![0, -1, 0, -1, 0, -1, 3, -1, -1]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 0, 0]
    strict := ![true, false, false, false, true, false, false, false, false] }
  origin := ![.triangle 32 1, .triangle 23 0, .gapLower 1 4, .triangle 20 0, .triangle 31 1, .corridorLower 4 5, .corridorUpper 3 4, .triangle 25 0, .triangle 27 0]

-- Cycle fingerprint 8f9783c7c2c89e013df3b5e1fbc3ce3871267f7a661b9a9298dde2a677aa62fe.
def localCycle00183 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 1, .distance 1 5, .distance 1 6, .distance 1 3, .distance 3 4, .distance 0 3, .distance 0 2, .theta 0, .zero]
    constant := ![0, 2, -2, 0, -1, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, false, false] }
  origin := ![.thetaUpper 1, .gapLower 1 6, .gapLower 1 5, .triangle 21 1, .triangle 19 0, .triangle 9 0, .gapLower 0 2, .corridorLower 0 2, .thetaLower 0]

-- Cycle fingerprint 9168961527df126c219b37eb540464e4c243a958cf00dae3df67d6c16f27b334.
def localCycle00184 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 2, .distance 0 1, .theta 0, .zero, .theta 5, .distance 4 5, .distance 2 4, .distance 1 2]
    constant := ![-3, -1, 0, 0, 3, -1, -1]
    coefficient := ![0, 0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 1 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 5, .corridorUpper 4 5, .triangle 28 0, .triangle 16 0]

-- Cycle fingerprint 92786cee48952e27505bc00708990096ea1a1905ca403c93106db575842c9a60.
def localCycle00185 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 2 4, .distance 4 6, .distance 3 6, .distance 1 3, .distance 3 5, .distance 3 4, .distance 0 3, .theta 0, .zero]
    constant := ![0, 3, -1, -1, 0, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, true, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 28 0, .triangle 29 0, .triangle 32 2, .triangle 21 0, .triangle 20 0, .triangle 31 1, .triangle 9 0, .corridorLower 0 3, .thetaLower 0]

-- Cycle fingerprint 93afe1df27f763bd780b8b6c5580f2b6abb2fbfa9b3d08b162856047a924fccd.
def localCycle00186 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 2, .distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 1 3, .distance 1 5, .distance 1 6, .distance 1 4, .distance 1 2]
    constant := ![-2, -1, 0, 0, 3, 0, 0, 0, -2, 0]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, true, false, true] }
  origin := ![.gapLower 1 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 15 2, .triangle 20 2, .triangle 24 2, .gapLower 1 3, .triangle 16 1]

-- Cycle fingerprint 96e58ccf38ee68974f674384b74670c14e4a4eedd12f0ff333b397744a290189.
def localCycle00187 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 2 4, .distance 2 5, .distance 5 6, .distance 4 6, .distance 3 4, .distance 1 3, .distance 3 5, .theta 3]
    constant := ![3, 0, 0, -1, 0, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 25 2, .triangle 28 2, .triangle 30 0, .triangle 34 2, .triangle 32 0, .triangle 19 0, .triangle 20 0, .corridorLower 3 5]

-- Cycle fingerprint 9885b76f52d05f0b9f21c1b169e9a30c665cb520fa2e5157f96b8984a05f54a3.
def localCycle00188 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 4 6, .distance 1 4, .distance 1 3, .distance 3 5, .distance 4 5, .theta 4]
    constant := ![3, 0, -1, -1, 0, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 29 0, .triangle 23 0, .triangle 19 1, .triangle 20 0, .triangle 31 1, .corridorLower 4 5]

-- Cycle fingerprint 9885c7d177f1c905965b89dcdd4f8dc0d82e8c1dd73bcc4476b39ac30e5d97c1.
def localCycle00189 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 1 3, .distance 1 6, .distance 0 1, .theta 1, .zero]
    constant := ![0, 3, 0, -1, -2, -1, -2, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 20 0, .gapLower 1 4, .triangle 4 0, .gapLower 1 0, .thetaLower 1]

-- Cycle fingerprint 98cdaeebdb6ff6b0dbfb0097769dae225af628f414869568d6de022d3c51c7cc.
def localCycle00190 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 1 3, .distance 1 4, .distance 1 5, .distance 1 6, .distance 1 2, .distance 0 1]
    constant := ![-1, 0, 0, 3, 0, 0, 0, 0, -2, -2]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, true, true, false, false] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 15 2, .triangle 19 2, .triangle 22 2, .triangle 24 2, .gapLower 1 2, .gapLower 1 1]

-- Cycle fingerprint 99a3b7b1651ca30dcac4476ad24c2617060fd97e53d5b32931ee18f4ea0368ab.
def localCycle00191 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 5, .distance 3 5, .distance 2 3, .distance 1 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, -1, 0, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 0, .triangle 31 2, .triangle 26 0, .triangle 15 0, .triangle 0 0, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint 99ad453d6e27f33cb1316f73d871b307dc573e79a3fad75d581fc3dc8de305be.
def localCycle00192 : Cycle where
  length := 11
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 2 3, .distance 2 6, .distance 2 4, .distance 1 4, .distance 1 2, .distance 0 1, .theta 0, .zero, .theta 5]
    constant := ![3, 0, -1, 0, 0, 0, -2, -2, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, false, true, true, true, false, false, false, false, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 26 0, .triangle 27 2, .triangle 29 1, .triangle 16 2, .gapLower 1 2, .gapLower 1 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 5]

-- Cycle fingerprint 99bb15ef2ecaaff7f11e0b452a2905c69964907899e6de06ad602041e152bcd5.
def localCycle00193 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 4, .distance 1 2, .distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 1 3, .distance 1 5, .distance 1 6, .distance 1 4]
    constant := ![-2, -1, -1, 0, 0, 3, 0, 0, -2, 0]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, true, false, true] }
  origin := ![.gapLower 1 2, .triangle 0 0, .corridorLower 0 1, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 15 2, .triangle 20 2, .gapLower 1 4, .triangle 23 1]

-- Cycle fingerprint 9ab97debb8933da9eee8498c85e61b46c7fc1fc2632c5cc7dc8b6ded9377c73d.
def localCycle00194 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 2, .distance 0 1, .theta 1, .zero, .theta 3, .distance 2 3, .distance 1 3, .distance 1 5, .distance 1 6, .distance 1 4, .distance 1 2]
    constant := ![-1, -2, 0, 0, 3, 0, 0, 0, -2, 0]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, true, false, true] }
  origin := ![.triangle 0 0, .gapLower 1 0, .thetaLower 1, .thetaUpper 3, .corridorUpper 2 3, .triangle 15 2, .triangle 20 2, .triangle 24 2, .gapLower 1 3, .triangle 16 1]

-- Cycle fingerprint 9b0e4df5326e2e94ae2f45271c626ec9097655c30ef0906249abea3f4c954131.
def localCycle00195 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 1, .distance 1 5, .distance 1 3, .distance 3 6, .distance 3 4, .distance 0 3, .distance 0 2, .theta 0, .zero]
    constant := ![0, 1, 0, -1, 0, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false, false, false] }
  origin := ![.thetaUpper 1, .gapLower 1 6, .triangle 20 1, .triangle 21 0, .triangle 32 1, .triangle 9 0, .gapLower 0 2, .corridorLower 0 2, .thetaLower 0]

-- Cycle fingerprint 9b51b0f72917a264bdf2908ccdc2a877c2369ebb9e4a68ce8ac4582ebf2e6437.
def localCycle00196 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 3, .distance 2 3, .distance 2 4, .distance 2 5, .distance 5 6, .distance 3 6, .distance 1 3, .distance 3 5, .distance 4 5, .distance 0 4, .theta 0, .zero]
    constant := ![0, 3, 0, 0, -1, 0, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, true, false, false, true, false, false, false] }
  origin := ![.thetaUpper 3, .corridorUpper 2 3, .triangle 25 2, .triangle 28 2, .triangle 30 0, .triangle 33 2, .triangle 21 0, .triangle 20 0, .triangle 31 1, .triangle 12 0, .corridorLower 0 4, .thetaLower 0]

-- Cycle fingerprint 9d11b4696abd46efaafee72891dae1eb31b1de57af9394a10e2c055281f784a3.
def localCycle00197 : Cycle where
  length := 12
  data := {
    node := ![.distance 3 5, .distance 3 4, .distance 0 3, .distance 0 2, .distance 0 1, .theta 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 2 5, .distance 5 6, .distance 3 5]
    constant := ![0, -1, 0, 0, -3, 0, 0, 0, 3, 0, -1, -1]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![true, false, false, true, false, true, false, false, false, true, false, false] }
  origin := ![.triangle 31 1, .triangle 9 0, .gapLower 0 2, .triangle 0 1, .gapLower 1 0, .thetaNext 0, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 26 2, .triangle 30 0, .triangle 33 0]

-- Cycle fingerprint 9d5b60e6de2f6ec6ff9a65606d20ab200dea8d3ced480d8d0e679c004d39dccc.
def localCycle00198 : Cycle where
  length := 7
  data := {
    node := ![.distance 3 6, .distance 1 3, .distance 1 4, .distance 4 5, .distance 3 4, .theta 3, .distance 2 3, .distance 3 6]
    constant := ![-1, 0, -1, -1, -1, 3, -1]
    coefficient := ![0, 0, 0, 0, 0, 1, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.triangle 21 0, .gapLower 1 4, .triangle 22 0, .triangle 31 0, .corridorLower 3 4, .corridorUpper 2 3, .triangle 27 0]

-- Cycle fingerprint 9de49c41d9a4fd16242a2e6699a36b8dd77f00504b4e067ac1a80b49217f1165.
def localCycle00199 : Cycle where
  length := 4
  data := {
    node := ![.distance 1 5, .distance 1 4, .distance 1 2, .distance 2 5, .distance 1 5]
    constant := ![-2, -2, 2, 0]
    coefficient := ![0, 0, 0, 0]
    strict := ![false, false, true, true] }
  origin := ![.gapLower 1 3, .gapLower 1 2, .gapUpper 2 2, .triangle 17 2]

-- Cycle fingerprint 9efa29a6441b8ed2bfc2f9a9b2d91184d6ceb76106edb23b630485beb4c0085b.
def localCycle00200 : Cycle where
  length := 14
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 4, .distance 2 3, .distance 1 3, .distance 3 5, .distance 4 5, .distance 0 4, .distance 0 3, .distance 0 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, -1, -1, 0, -1, 0, -1, 0, 0, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, false, true, false, true, true, true, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 0, .triangle 25 0, .triangle 15 2, .triangle 20 0, .triangle 31 1, .triangle 12 0, .triangle 9 1, .triangle 5 1, .triangle 0 1, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint 9fa6b3aa385135d43cd22bdb3bb120c54802f95e16a4d9d01016d68b33abf941.
def localCycle00201 : Cycle where
  length := 6
  data := {
    node := ![.distance 5 6, .distance 0 5, .distance 0 4, .distance 0 1, .theta 1, .distance 1 5, .distance 5 6]
    constant := ![-1, 0, 0, -2, 2, -1]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![false, false, true, false, false, false] }
  origin := ![.triangle 14 0, .gapLower 0 4, .triangle 2 1, .gapLower 1 0, .gapLower 1 6, .triangle 24 0]

-- Cycle fingerprint a0f65ed1bd4fa92ac25e8963c6bb40861e28c44b8bf22c22844906932ab10330.
def localCycle00202 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 2, .distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 2 5, .distance 5 6, .distance 1 5, .distance 1 4, .distance 1 2]
    constant := ![-1, -1, 0, 0, 3, 0, -1, -1, -2, -2]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, false, false, false] }
  origin := ![.triangle 0 0, .corridorLower 0 1, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 26 2, .triangle 30 0, .triangle 24 0, .gapLower 1 3, .gapLower 1 2]

-- Cycle fingerprint a3ae5da2cf3666138dd047034e238addf15353aaab9be4be4cd3b9af6e9222de.
def localCycle00203 : Cycle where
  length := 9
  data := {
    node := ![.distance 2 3, .distance 1 3, .distance 1 6, .distance 1 4, .distance 1 2, .distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3]
    constant := ![0, -2, 0, -2, -1, -1, 0, 0, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1, 1]
    strict := ![true, false, true, false, false, false, false, false, false] }
  origin := ![.triangle 15 2, .gapLower 1 5, .triangle 23 1, .gapLower 1 2, .triangle 0 0, .corridorLower 0 1, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3]

-- Cycle fingerprint a3bf77dea82d8e2ca4b8a04950bd65e5470e10c1d5dbebc41bf3f24fef89f1f4.
def localCycle00204 : Cycle where
  length := 8
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 2 3, .distance 1 2, .distance 0 1, .theta 0, .zero, .theta 5]
    constant := ![3, 0, -1, -1, -3, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, false, false, false, false, false, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 26 0, .triangle 15 0, .gapLower 1 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 5]

-- Cycle fingerprint a5e56bbbad1f20f16506ec73d4492d2568582c5faa3543360c955653e2e6b16e.
def localCycle00205 : Cycle where
  length := 11
  data := {
    node := ![.theta 3, .distance 2 3, .distance 2 4, .distance 4 6, .distance 4 5, .distance 1 4, .distance 1 2, .distance 0 1, .theta 1, .theta 0, .zero, .theta 3]
    constant := ![3, 0, -1, 0, -1, 0, -2, -2, 0, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, false, true, false, false, false, false, true, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 25 2, .triangle 29 0, .triangle 34 1, .triangle 22 0, .gapLower 1 2, .gapLower 1 1, .gapLower 1 0, .thetaNext 0, .thetaLower 0, .thetaUpper 3]

-- Cycle fingerprint a5f7fd127afa6c3b5239ffdc471d9888c81aa6eaed86cf928b8062361aa3d729.
def localCycle00206 : Cycle where
  length := 8
  data := {
    node := ![.distance 3 4, .distance 0 3, .distance 0 2, .distance 0 1, .theta 1, .distance 1 5, .distance 1 3, .distance 3 6, .distance 3 4]
    constant := ![-1, 0, 0, -2, 2, 0, -1, 0]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![false, false, true, false, false, true, false, true] }
  origin := ![.triangle 9 0, .gapLower 0 2, .triangle 0 1, .gapLower 1 0, .gapLower 1 6, .triangle 20 1, .triangle 21 0, .triangle 32 1]

-- Cycle fingerprint a5fabc9f2ac2200fd8d6ec2363f4f6920324fc9773c06ada24d850d257e2e47b.
def localCycle00207 : Cycle where
  length := 4
  data := {
    node := ![.distance 1 4, .distance 1 3, .distance 3 6, .distance 4 6, .distance 1 4]
    constant := ![-2, -1, 0, 2]
    coefficient := ![0, 0, 0, 0]
    strict := ![false, false, true, true] }
  origin := ![.gapLower 1 5, .triangle 21 0, .triangle 32 1, .gapUpper 4 3]

-- Cycle fingerprint a7123ad537bcef942895c957642286f45c404b8bab3509c72537dbb913ecdf6c.
def localCycle00208 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 5 6, .distance 2 5, .distance 3 5, .distance 1 3, .distance 3 4, .distance 0 3, .theta 0, .zero]
    constant := ![0, 3, -1, -1, 0, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 34 0, .triangle 30 0, .triangle 26 1, .triangle 20 0, .triangle 19 0, .triangle 9 0, .corridorLower 0 3, .thetaLower 0]

-- Cycle fingerprint a74fbb609bb4fdab47f44b1a369af62a9bf97d9e8f48224b0a9190ccb22fb352.
def localCycle00209 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 3, .distance 2 6, .distance 1 6, .distance 1 4, .distance 0 1]
    constant := ![-1, 0, 0, 3, 0, -1, 0, 0, -3, -1]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, true, true, false, false] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 0, .triangle 27 2, .triangle 18 2, .gapLower 1 3, .triangle 2 0]

-- Cycle fingerprint a7927311efcd0e95fa826ba09d48ec0c7ff06f2d497d31cc224ce55002931d87.
def localCycle00210 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .theta 1, .zero, .theta 3, .distance 2 3, .distance 2 4, .distance 4 5, .distance 4 6, .distance 1 4, .distance 1 2, .distance 0 1]
    constant := ![-2, 0, 0, 3, 0, -1, 0, -1, -2, -1]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, true, false, false, false] }
  origin := ![.gapLower 1 0, .thetaLower 1, .thetaUpper 3, .corridorUpper 2 3, .triangle 25 2, .triangle 28 0, .triangle 34 2, .triangle 23 0, .gapLower 1 2, .triangle 0 0]

-- Cycle fingerprint a7d8a4eeeaf1c2220c6dd3817115fb986df0876d4e5dc2a50450c8f1ca13e72e.
def localCycle00211 : Cycle where
  length := 3
  data := {
    node := ![.distance 4 6, .distance 1 4, .distance 1 6, .distance 4 6]
    constant := ![2, -3, 0]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.gapUpper 4 3, .gapLower 1 5, .triangle 23 1]

-- Cycle fingerprint a7e99da87b55d68e61c031fa9ecdaeda1eb58f5b22fdeb99d91d867daef3a54b.
def localCycle00212 : Cycle where
  length := 7
  data := {
    node := ![.distance 3 6, .distance 4 6, .distance 4 5, .theta 4, .distance 3 4, .distance 1 3, .distance 1 6, .distance 3 6]
    constant := ![0, 0, -1, 3, -1, -2, 0]
    coefficient := ![0, 0, 0, 1, 0, 0, 0]
    strict := ![true, true, false, false, false, false, true] }
  origin := ![.triangle 32 1, .triangle 34 1, .corridorLower 4 5, .corridorUpper 3 4, .triangle 19 0, .gapLower 1 4, .triangle 21 1]

-- Cycle fingerprint a7f4f28410cf490886afb4d24b25af50509e5f8500bf6c48df37dbc59a2cebbc.
def localCycle00213 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 3, .distance 1 3, .distance 3 6, .distance 5 6, .distance 4 5, .theta 4]
    constant := ![3, -1, 0, -1, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 0, .triangle 15 2, .triangle 21 0, .triangle 33 1, .triangle 34 0, .corridorLower 4 5]

-- Cycle fingerprint a7f7c494eced14b7ebecb81f78eadfde53f47a84677f8b0116d63a1ecd2566c2.
def localCycle00214 : Cycle where
  length := 7
  data := {
    node := ![.distance 3 5, .distance 4 5, .theta 4, .distance 3 4, .distance 1 3, .distance 1 6, .distance 1 5, .distance 3 5]
    constant := ![0, -1, 3, -1, 0, -2, 0]
    coefficient := ![0, 0, 1, 0, 0, 0, 0]
    strict := ![true, false, false, false, true, false, true] }
  origin := ![.triangle 31 1, .corridorLower 4 5, .corridorUpper 3 4, .triangle 19 0, .triangle 21 2, .gapLower 1 3, .triangle 20 1]

-- Cycle fingerprint a80a3de1882061dd788011eefa85d0b06f8385eb3a6d5923a8c191884d25e653.
def localCycle00215 : Cycle where
  length := 8
  data := {
    node := ![.theta 0, .zero, .theta 4, .distance 3 4, .distance 1 3, .distance 1 5, .distance 1 2, .distance 0 1, .theta 0]
    constant := ![0, 0, 3, -1, -2, 0, -2, -1]
    coefficient := ![0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, false] }
  origin := ![.thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 19 0, .gapLower 1 3, .triangle 17 1, .gapLower 1 1, .corridorLower 0 1]

-- Cycle fingerprint a8463b2d29969a70e14573da7f83075cdc921c1f391b1207023456aa7a3e086e.
def localCycle00216 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 1 3, .distance 1 4, .distance 4 6, .distance 3 4, .distance 0 3, .theta 0, .zero]
    constant := ![0, 3, 0, -1, 0, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 20 0, .triangle 19 2, .triangle 23 0, .triangle 32 0, .triangle 9 0, .corridorLower 0 3, .thetaLower 0]

-- Cycle fingerprint a973d1ce0891db1eb992ecd717d0dea7cad8a2bb6a3fc4678aa09f2bb1afe715.
def localCycle00217 : Cycle where
  length := 11
  data := {
    node := ![.theta 0, .zero, .theta 3, .distance 2 3, .distance 2 4, .distance 4 5, .distance 1 5, .distance 1 6, .distance 1 4, .distance 1 2, .distance 0 1, .theta 0]
    constant := ![0, 0, 3, 0, -1, 0, -2, 0, -2, -1, -1]
    coefficient := ![0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, true, false, false, false] }
  origin := ![.thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 25 2, .triangle 28 0, .gapLower 5 4, .gapLower 1 4, .triangle 23 1, .gapLower 1 2, .triangle 0 0, .corridorLower 0 1]

-- Cycle fingerprint aa3c93efab8c7a785401775c53e9d271441ab1c196347f3be43e570f5c8565f3.
def localCycle00218 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 1 3, .distance 1 6, .distance 1 4, .distance 1 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, -1, 0, 0, -2, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, true, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 20 0, .triangle 21 2, .triangle 23 1, .gapLower 1 2, .triangle 0 0, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint aa5d8fc73799c4f6f43937a126a31f7ed78df362071661fecbbc35838eb60c34.
def localCycle00219 : Cycle where
  length := 3
  data := {
    node := ![.distance 5 6, .distance 1 5, .distance 1 6, .distance 5 6]
    constant := ![2, -3, 0]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.gapUpper 5 3, .gapLower 1 4, .triangle 24 1]

-- Cycle fingerprint aaa066eb6d5d830b33f5844988bd0735e5f639a755e69f70d6fd4d4d5b923466.
def localCycle00220 : Cycle where
  length := 8
  data := {
    node := ![.theta 0, .zero, .theta 4, .distance 3 4, .distance 1 3, .distance 1 5, .distance 1 2, .distance 0 1, .theta 0]
    constant := ![0, 0, 3, -1, -2, -2, -1, -1]
    coefficient := ![0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 19 0, .gapLower 1 3, .gapLower 1 2, .triangle 0 0, .corridorLower 0 1]

-- Cycle fingerprint add0069579fd2bf18970a186a84b856219c6795f92ea2428f9694c346fd051b9.
def localCycle00221 : Cycle where
  length := 10
  data := {
    node := ![.distance 3 5, .distance 2 3, .distance 2 6, .distance 2 4, .distance 1 2, .distance 0 1, .theta 0, .zero, .theta 5, .distance 4 5, .distance 3 5]
    constant := ![-1, 0, 0, -1, -2, -1, 0, 0, 3, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![false, true, true, false, false, false, false, false, false, true] }
  origin := ![.triangle 26 0, .triangle 27 2, .triangle 29 1, .triangle 16 0, .gapLower 1 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 5, .corridorUpper 4 5, .triangle 31 2]

-- Cycle fingerprint ae03400d038ce89283af157eb40fa04ebc752c87cebd83d249b2355ed2a06c1c.
def localCycle00222 : Cycle where
  length := 5
  data := {
    node := ![.distance 1 2, .distance 2 6, .distance 4 6, .distance 1 6, .distance 1 4, .distance 1 2]
    constant := ![2, 0, 0, -3, 0]
    coefficient := ![0, 0, 0, 0, 0]
    strict := ![true, false, false, false, true] }
  origin := ![.gapUpper 2 2, .gapLower 6 5, .gapLower 6 4, .gapLower 1 3, .triangle 16 1]

-- Cycle fingerprint ae2d9a52d96f13d3414877440874384eb621030bd184d3437c25e972f0c1ce5b.
def localCycle00223 : Cycle where
  length := 8
  data := {
    node := ![.distance 3 4, .theta 3, .distance 2 3, .distance 1 3, .distance 1 4, .distance 1 6, .distance 1 5, .distance 4 5, .distance 3 4]
    constant := ![-1, 3, 0, 0, -2, -2, 0, -1]
    coefficient := ![0, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, true, false] }
  origin := ![.corridorLower 3 4, .corridorUpper 2 3, .triangle 15 2, .triangle 19 2, .gapLower 1 4, .gapLower 1 3, .triangle 22 1, .triangle 31 0]

-- Cycle fingerprint ae53cb9f79619331cd095c6dd4253d08b56dddd1934b1767922a0dcbea54725e.
def localCycle00224 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 2 4, .distance 4 6, .distance 3 6, .distance 1 3, .distance 3 5, .distance 3 4, .theta 3]
    constant := ![3, 0, -1, 0, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 25 2, .triangle 29 0, .triangle 32 2, .triangle 21 0, .triangle 20 0, .triangle 31 1, .corridorLower 3 4]

-- Cycle fingerprint afe87a1d8509390804242e36c4c8b17b9e479244edb5672ae4edfcfb50564823.
def localCycle00225 : Cycle where
  length := 13
  data := {
    node := ![.distance 0 4, .distance 0 3, .distance 0 1, .theta 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 2 3, .distance 1 3, .distance 3 6, .distance 4 6, .distance 4 5, .distance 0 4]
    constant := ![0, 0, -3, 0, 0, 0, 3, -1, 0, -1, 0, 0, -1]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, false, false, true, false, true, true, false] }
  origin := ![.gapLower 0 3, .triangle 1 1, .gapLower 1 0, .thetaNext 0, .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 25 0, .triangle 15 2, .triangle 21 0, .triangle 32 1, .triangle 34 1, .triangle 12 0]

-- Cycle fingerprint b04f30e924796800b762ca0f6ef99f8445917e0b8da037e22c23345cc52cdc3b.
def localCycle00226 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 6, .distance 5 6, .distance 1 5, .distance 1 2, .distance 0 1]
    constant := ![-1, 0, 0, 3, -1, -2, -1]
    coefficient := ![0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 6, .corridorUpper 5 6, .triangle 24 0, .gapLower 1 2, .triangle 0 0]

-- Cycle fingerprint b2128e5d9c01329560fc0e02a5e9a2654f36e6c1770b307ac65a7fccd6dcb3e2.
def localCycle00227 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .theta 1, .zero, .theta 3, .distance 2 3, .distance 2 4, .distance 4 6, .distance 4 5, .distance 1 4, .distance 1 2, .distance 0 1]
    constant := ![-2, 0, 0, 3, 0, -1, 0, -1, -2, -1]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, true, false, false, false] }
  origin := ![.gapLower 1 0, .thetaLower 1, .thetaUpper 3, .corridorUpper 2 3, .triangle 25 2, .triangle 29 0, .triangle 34 1, .triangle 22 0, .gapLower 1 2, .triangle 0 0]

-- Cycle fingerprint b23e7fa290e3e7db60a02fe417a9f0f15b7c402c7531de2113cc8926365e9239.
def localCycle00228 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 4, .distance 1 3, .distance 3 5, .distance 5 6, .distance 4 5, .distance 0 4, .distance 0 3, .theta 3]
    constant := ![3, -1, -1, -1, -1, -1, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 25 0, .triangle 19 0, .triangle 20 0, .triangle 33 0, .triangle 34 0, .triangle 12 0, .triangle 9 1, .gapLower 3 0]

-- Cycle fingerprint b296906f5e4273d2835b3d50f5c47a35782bfdd1b7c0ace9f8a0de6c1684a1da.
def localCycle00229 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 2 5, .distance 1 2, .distance 0 1, .theta 1, .theta 0, .zero]
    constant := ![0, 3, -1, -1, -2, -2, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 30 0, .triangle 17 0, .gapLower 1 1, .gapLower 1 0, .thetaNext 0, .thetaLower 0]

-- Cycle fingerprint b38f819ac6e8037d268f21d97ea79112e3de0576ac967d3a8d29501408ea6c07.
def localCycle00230 : Cycle where
  length := 10
  data := {
    node := ![.distance 2 4, .distance 4 5, .distance 4 6, .distance 1 4, .distance 1 2, .distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 2 4]
    constant := ![-1, 0, -1, 0, -2, -1, 0, 0, 3, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![false, true, false, false, false, false, false, false, false, true] }
  origin := ![.triangle 28 0, .triangle 34 2, .triangle 23 0, .gapLower 1 2, .gapLower 1 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 25 2]

-- Cycle fingerprint b3c275ff1849aaca64f0d3fa2de6886331ef751de6b78a055f43bf09cd37c5ec.
def localCycle00231 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 5 6, .distance 2 5, .distance 2 4, .distance 1 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, -1, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 34 0, .triangle 30 0, .gapLower 2 3, .triangle 16 0, .triangle 0 0, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint b3d41b171d64f688404ec3728ddc23f8ae2aaeee215eca1d0b73ad1be07eaafc.
def localCycle00232 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 2 4, .distance 4 5, .distance 3 5, .distance 1 3, .distance 3 4, .distance 4 6, .theta 4]
    constant := ![3, -1, 0, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false] }
  origin := ![.corridorUpper 2 4, .triangle 28 0, .triangle 31 2, .triangle 20 0, .triangle 19 0, .triangle 32 0, .corridorLower 4 6]

-- Cycle fingerprint b4e4459a1ef13b1651101a165ae3a3dfe733001cc8f5e8cf35416d58b3be1e8a.
def localCycle00233 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 2 4, .distance 4 5, .distance 1 4, .distance 4 6, .distance 5 6, .distance 0 5, .theta 0, .zero]
    constant := ![0, 3, 0, -1, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, true, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 28 0, .triangle 22 0, .triangle 23 0, .triangle 34 1, .triangle 14 0, .corridorLower 0 5, .thetaLower 0]

-- Cycle fingerprint b57257c749df6f95d8bf332f60b6429d4fee91fd801e0d222685b5b8b78242a0.
def localCycle00234 : Cycle where
  length := 10
  data := {
    node := ![.theta 0, .zero, .theta 3, .distance 2 3, .distance 2 4, .distance 4 5, .distance 4 6, .distance 1 4, .distance 1 2, .distance 0 1, .theta 0]
    constant := ![0, 0, 3, 0, -1, 0, -1, 0, -3, -1]
    coefficient := ![0, 1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true, false, false, false, false] }
  origin := ![.thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 25 2, .triangle 28 0, .triangle 34 2, .triangle 23 0, .gapLower 1 2, .gapLower 1 1, .corridorLower 0 1]

-- Cycle fingerprint b6032f41459296019b6cc8681df68cfe3004ff762324a537c798ba67b0b5282f.
def localCycle00235 : Cycle where
  length := 13
  data := {
    node := ![.zero, .theta 3, .distance 2 3, .distance 2 4, .distance 4 5, .distance 3 5, .distance 1 3, .distance 3 6, .distance 3 4, .distance 0 3, .distance 0 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, -1, 0, -1, -1, 0, -1, 0, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false, true, false, true, true, false, false] }
  origin := ![.thetaUpper 3, .corridorUpper 2 3, .triangle 25 2, .triangle 28 0, .triangle 31 2, .triangle 20 0, .triangle 21 0, .triangle 32 1, .triangle 9 0, .triangle 5 1, .triangle 0 1, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint ba75633932944189c64274d3eba812f581ea5dee5bb4bf7a1a3f906cf12a2f48.
def localCycle00236 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 3, .distance 2 3, .distance 2 4, .distance 4 6, .distance 4 5, .distance 1 5, .distance 1 4, .distance 1 2, .distance 0 1, .theta 1, .zero]
    constant := ![0, 3, 0, -1, 0, 0, -2, 0, -1, -2, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false, true, false, false, false] }
  origin := ![.thetaUpper 3, .corridorUpper 2 3, .triangle 25 2, .triangle 29 0, .triangle 34 1, .gapLower 5 3, .gapLower 1 3, .triangle 16 1, .triangle 0 0, .gapLower 1 0, .thetaLower 1]

-- Cycle fingerprint bae473f0cf77d3643d49a656866b90150b7987d499a69e39ba9821ab8a453bd9.
def localCycle00237 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 3, .distance 2 3, .distance 3 4, .distance 4 5, .distance 5 6, .distance 0 5, .theta 0, .zero]
    constant := ![0, 3, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 3, .corridorUpper 2 3, .triangle 25 0, .triangle 31 0, .triangle 34 0, .triangle 14 0, .corridorLower 0 5, .thetaLower 0]

-- Cycle fingerprint bb2ced09b4e83112e64ad673464ad22d2576f2297e2d2197eacc63f41a64b9a3.
def localCycle00238 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .theta 1, .zero, .theta 3, .distance 2 3, .distance 2 5, .distance 5 6, .distance 1 5, .distance 1 4, .distance 1 2, .distance 0 1]
    constant := ![-2, 0, 0, 3, 0, -1, -1, 0, -2, -1]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, false, false, false] }
  origin := ![.gapLower 1 0, .thetaLower 1, .thetaUpper 3, .corridorUpper 2 3, .triangle 26 2, .triangle 30 0, .triangle 24 0, .gapLower 1 3, .gapLower 1 2, .triangle 0 0]

-- Cycle fingerprint bb474025541cf4e41b3db8f6aa5bcae70991943d84e0594919d67bfc3416dca5.
def localCycle00239 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 2 4, .distance 4 5, .distance 1 5, .distance 1 6, .distance 3 6, .distance 3 4, .theta 3]
    constant := ![3, 0, -1, 0, -3, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, true, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 25 2, .triangle 28 0, .gapLower 5 4, .gapLower 1 4, .triangle 21 1, .triangle 32 1, .corridorLower 3 4]

-- Cycle fingerprint bb53c57bd3f3febd533fe18244e7474f489bc8628af17cc2b782be3389ec0716.
def localCycle00240 : Cycle where
  length := 13
  data := {
    node := ![.distance 0 5, .distance 0 4, .distance 0 1, .theta 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 1 3, .distance 1 4, .distance 4 5, .distance 3 5, .distance 5 6, .distance 0 5]
    constant := ![0, 0, -3, 0, 0, 0, 3, 0, 0, -1, 0, -1, -1]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, false, true, true, false, true, false, false] }
  origin := ![.gapLower 0 4, .triangle 2 1, .gapLower 1 0, .thetaNext 0, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 15 2, .triangle 19 2, .triangle 22 0, .triangle 31 2, .triangle 33 0, .triangle 14 0]

-- Cycle fingerprint bb687b44b7bb2c6871f7411fdbc5efd2f3773379af9fcca61f4dfa05f28a0ba5.
def localCycle00241 : Cycle where
  length := 11
  data := {
    node := ![.distance 0 3, .distance 0 2, .distance 1 2, .distance 0 1, .theta 0, .zero, .theta 1, .distance 1 3, .distance 1 4, .distance 4 5, .distance 3 4, .distance 0 3]
    constant := ![0, 2, -2, -1, 0, 0, 2, 0, -1, -1, -1]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false, true, false, false, false] }
  origin := ![.gapLower 0 2, .gapUpper 2 1, .gapLower 1 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 1, .gapLower 1 6, .triangle 19 2, .triangle 22 0, .triangle 31 0, .triangle 9 0]

-- Cycle fingerprint bca4f62b8c3cb949c32ee8ca9890f53691df767f39569fd5dd023c0aa19aacb2.
def localCycle00242 : Cycle where
  length := 11
  data := {
    node := ![.theta 1, .zero, .theta 3, .distance 2 3, .distance 2 5, .distance 5 6, .distance 1 6, .distance 1 5, .distance 1 4, .distance 1 2, .distance 0 1, .theta 1]
    constant := ![0, 0, 3, 0, -1, 0, -2, 0, 0, -1, -2]
    coefficient := ![0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, true, true, false, false] }
  origin := ![.thetaLower 1, .thetaUpper 3, .corridorUpper 2 3, .triangle 26 2, .triangle 30 0, .gapLower 6 3, .gapLower 1 4, .triangle 22 1, .triangle 16 1, .triangle 0 0, .gapLower 1 0]

-- Cycle fingerprint bcb4186d15bfcf98df4c66d7240997b5a56d9a79501f7a4ce8eec2ec83400839.
def localCycle00243 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 3, .distance 1 6, .distance 1 5, .distance 1 2, .distance 0 1, .theta 1, .zero, .theta 4, .distance 3 4, .distance 1 3]
    constant := ![0, -2, 0, -1, -2, 0, 0, 3, -1]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![true, false, true, false, false, false, false, false, false] }
  origin := ![.triangle 21 2, .gapLower 1 3, .triangle 17 1, .triangle 0 0, .gapLower 1 0, .thetaLower 1, .thetaUpper 4, .corridorUpper 3 4, .triangle 19 0]

-- Cycle fingerprint bd59dbf5af3548c7ddc92b50f9e73b12d04342cf4846ecd074cd02469a9a92ce.
def localCycle00244 : Cycle where
  length := 8
  data := {
    node := ![.theta 0, .zero, .theta 3, .distance 2 3, .distance 1 3, .distance 1 5, .distance 1 2, .distance 0 1, .theta 0]
    constant := ![0, 0, 3, 0, -2, 0, -2, -1]
    coefficient := ![0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true, false, false] }
  origin := ![.thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 15 2, .gapLower 1 5, .triangle 17 1, .gapLower 1 1, .corridorLower 0 1]

-- Cycle fingerprint bdccb055834d9b90eb630e5553a86a2c8c7ca9c3b41da9a61b4c202e345fa42a.
def localCycle00245 : Cycle where
  length := 6
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 6, .distance 3 5, .distance 1 3, .distance 3 4, .theta 3]
    constant := ![3, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 27 0, .triangle 33 1, .triangle 20 0, .triangle 19 0, .corridorLower 3 4]

-- Cycle fingerprint beaeb5afc693b05afc9988e44f5d751e5fd165dc00a9d7dfb2f309a561f2265e.
def localCycle00246 : Cycle where
  length := 15
  data := {
    node := ![.zero, .theta 3, .distance 2 3, .distance 3 5, .distance 3 4, .distance 1 3, .distance 3 6, .distance 4 6, .distance 5 6, .distance 0 5, .distance 0 4, .distance 0 3, .distance 0 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, -1, 0, -1, -1, 0, 0, -1, 0, 0, 0, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, true, true, false, true, true, true, true, false, false] }
  origin := ![.thetaUpper 3, .corridorUpper 2 3, .triangle 26 0, .triangle 31 1, .triangle 19 0, .triangle 21 0, .triangle 32 1, .triangle 34 1, .triangle 14 0, .triangle 12 1, .triangle 9 1, .triangle 5 1, .triangle 0 1, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint bedb7b72619196d5aa5287b289d8ceeeae841a29b7a8c737d8717cc822f60790.
def localCycle00247 : Cycle where
  length := 11
  data := {
    node := ![.theta 0, .zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 1 5, .distance 1 6, .distance 1 3, .distance 1 4, .distance 0 1, .theta 0]
    constant := ![0, 0, 3, 0, 0, 0, -2, 0, -2, -1, -1]
    coefficient := ![0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, true, false, true, false, false, false] }
  origin := ![.thetaLower 0, .thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 17 2, .gapLower 1 5, .triangle 21 1, .gapLower 1 3, .triangle 2 0, .corridorLower 0 1]

-- Cycle fingerprint bfefb617506baafceb576026eafe17f592309dce89b44fb3eed34abe05a9578f.
def localCycle00248 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 3, .distance 1 4, .distance 1 6, .distance 1 5, .distance 4 5, .distance 3 4, .theta 3]
    constant := ![3, 0, 0, 0, -3, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, true, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 2, .triangle 19 2, .triangle 23 2, .gapLower 1 3, .triangle 22 1, .triangle 31 0, .corridorLower 3 4]

-- Cycle fingerprint c00388e76c51f92b117d46109bc7a0f260f32b291fc71343e52b826915f0b1b0.
def localCycle00249 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 2 4, .distance 4 5, .distance 3 4, .distance 1 3, .distance 3 6, .distance 4 6, .theta 4]
    constant := ![3, -1, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false] }
  origin := ![.corridorUpper 2 4, .triangle 28 0, .triangle 31 0, .triangle 19 0, .triangle 21 0, .triangle 32 1, .corridorLower 4 6]

-- Cycle fingerprint c01afb07aa35b287026f5a3945cf6a1f785165c4886127aff655c2900dc5efdb.
def localCycle00250 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 5, .distance 1 2, .distance 0 1, .theta 1, .zero, .theta 6, .distance 5 6, .distance 1 5]
    constant := ![-2, -1, -2, 0, 0, 3, -1]
    coefficient := ![0, 0, 0, 0, 1, 1, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 1 2, .triangle 0 0, .gapLower 1 0, .thetaLower 1, .thetaUpper 6, .corridorUpper 5 6, .triangle 24 0]

-- Cycle fingerprint c0fe9b37db6a8777229f3f1447f4df26f675828ebafd7487601a75eaf0e02235.
def localCycle00251 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 2 4, .distance 4 6, .distance 5 6, .distance 3 5, .distance 1 3, .distance 3 4, .distance 0 3, .theta 0, .zero]
    constant := ![0, 3, -1, -1, 0, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 28 0, .triangle 29 0, .triangle 34 1, .triangle 33 0, .triangle 20 0, .triangle 19 0, .triangle 9 0, .corridorLower 0 3, .thetaLower 0]

-- Cycle fingerprint c205b1c7678706edd3b8a7f70f883c4234b5d3a0cd22a231355d22293023726a.
def localCycle00252 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 2, .distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 2 4, .distance 4 5, .distance 1 5, .distance 1 6, .distance 1 2]
    constant := ![-2, -1, 0, 0, 3, 0, -1, 0, -2, 0]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, true, false, true] }
  origin := ![.gapLower 1 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 25 2, .triangle 28 0, .triangle 22 2, .gapLower 1 4, .triangle 18 1]

-- Cycle fingerprint c3f487f2d5ca031e1e45d083bcf11681b2787248a21492fe598ad4b2ccc013bf.
def localCycle00253 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 4 5, .distance 1 4, .distance 4 6, .distance 5 6, .distance 0 5, .theta 0, .zero]
    constant := ![0, 3, -1, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 31 0, .triangle 22 0, .triangle 23 0, .triangle 34 1, .triangle 14 0, .corridorLower 0 5, .thetaLower 0]

-- Cycle fingerprint c46d28195ca89e071cf3824db0e342b31627256563416c57a1b8d3bd9b112352.
def localCycle00254 : Cycle where
  length := 11
  data := {
    node := ![.distance 2 3, .distance 1 3, .distance 3 5, .distance 5 6, .distance 0 5, .distance 0 4, .distance 0 1, .theta 1, .theta 0, .zero, .theta 3, .distance 2 3]
    constant := ![0, -1, -1, -1, 0, 0, -3, 0, 0, 0, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1]
    strict := ![true, false, false, false, false, true, false, true, false, false, false] }
  origin := ![.triangle 15 2, .triangle 20 0, .triangle 33 0, .triangle 14 0, .gapLower 0 4, .triangle 2 1, .gapLower 1 0, .thetaNext 0, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3]

-- Cycle fingerprint c46ef43eae6d4674bb9e1a6c2f26f8b36287f951850f61adbb092378916c9b57.
def localCycle00255 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 4, .distance 4 5, .distance 1 4, .distance 4 6, .distance 5 6, .distance 0 5, .distance 0 3, .theta 3]
    constant := ![3, -1, -1, -1, -1, 0, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 25 0, .triangle 31 0, .triangle 22 0, .triangle 23 0, .triangle 34 1, .triangle 14 0, .triangle 10 1, .gapLower 3 0]

-- Cycle fingerprint c4db3e0430c3bd7ecd52bcc5d0610f0aa21ac0930f8febc36a8ea47c42c6bdc6.
def localCycle00256 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 5, .distance 1 2, .distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 1 3, .distance 1 4, .distance 1 6, .distance 1 5]
    constant := ![-2, -1, -1, 0, 0, 3, 0, 0, -2, 0]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, true, false, true] }
  origin := ![.gapLower 1 2, .triangle 0 0, .corridorLower 0 1, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 15 2, .triangle 19 2, .gapLower 1 4, .triangle 24 1]

-- Cycle fingerprint c554c3a00c395f795494058ec4bdb0fab92e609ce22674d9caa602008c49ab24.
def localCycle00257 : Cycle where
  length := 13
  data := {
    node := ![.distance 0 3, .distance 0 2, .distance 0 1, .theta 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 1 3, .distance 1 5, .distance 5 6, .distance 3 5, .distance 3 4, .distance 0 3]
    constant := ![0, 0, -3, 0, 0, 0, 3, 0, 0, -1, -1, 0, -1]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, false, true, true, false, false, true, false] }
  origin := ![.gapLower 0 2, .triangle 0 1, .gapLower 1 0, .thetaNext 0, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 15 2, .triangle 20 2, .triangle 24 0, .triangle 33 0, .triangle 31 1, .triangle 9 0]

-- Cycle fingerprint c6c4da7dbb19e254736e537b1ff23b87d2dcdd26426c8f9913d06cdd076c1d9d.
def localCycle00258 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 2 4, .distance 4 6, .distance 3 4, .distance 0 3, .theta 0, .zero]
    constant := ![0, 3, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 28 0, .triangle 29 0, .triangle 32 0, .triangle 9 0, .corridorLower 0 3, .thetaLower 0]

-- Cycle fingerprint c6fcd1c8f6fb990f2ce99d6aa287620e740b51cdd3eb354ade8578bdcb9552a2.
def localCycle00259 : Cycle where
  length := 7
  data := {
    node := ![.theta 1, .distance 1 3, .distance 3 5, .distance 5 6, .distance 0 5, .distance 0 4, .distance 0 1, .theta 1]
    constant := ![2, -1, -1, -1, 0, 0, -2]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false] }
  origin := ![.gapLower 1 6, .triangle 20 0, .triangle 33 0, .triangle 14 0, .gapLower 0 4, .triangle 2 1, .gapLower 1 0]

-- Cycle fingerprint c7134f82acd4f8da5993fa736c42358ac436f582070f9db970080dbcb228e00f.
def localCycle00260 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 3, .distance 3 5, .distance 4 5, .distance 0 4, .distance 0 3, .theta 3, .distance 2 3, .distance 3 4, .distance 4 6, .distance 1 4, .distance 1 3]
    constant := ![-1, 0, -1, 0, 0, 3, -1, -1, -1, 0]
    coefficient := ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false, false, false, false] }
  origin := ![.triangle 20 0, .triangle 31 1, .triangle 12 0, .gapLower 0 3, .gapLower 3 0, .corridorUpper 2 3, .triangle 25 0, .triangle 32 0, .triangle 23 0, .gapLower 1 4]

-- Cycle fingerprint c77d01743cc3b01b1ef0a24e46c2a59e705bf501d14978b4e35935fe68dacc04.
def localCycle00261 : Cycle where
  length := 13
  data := {
    node := ![.distance 0 3, .distance 0 2, .distance 0 1, .theta 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 1 3, .distance 1 4, .distance 4 6, .distance 4 5, .distance 3 4, .distance 0 3]
    constant := ![0, 0, -3, 0, 0, 0, 3, 0, 0, -1, 0, -1, -1]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, false, true, true, false, true, false, false] }
  origin := ![.gapLower 0 2, .triangle 0 1, .gapLower 1 0, .thetaNext 0, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 15 2, .triangle 19 2, .triangle 23 0, .triangle 34 1, .triangle 31 0, .triangle 9 0]

-- Cycle fingerprint c79732f4317e7bf2504e441f1234944da57fb63a4c3e243f5a339a75616c0945.
def localCycle00262 : Cycle where
  length := 4
  data := {
    node := ![.distance 4 6, .distance 1 4, .distance 1 2, .distance 2 6, .distance 4 6]
    constant := ![-1, -2, 2, 0]
    coefficient := ![0, 0, 0, 0]
    strict := ![false, false, true, false] }
  origin := ![.triangle 23 0, .gapLower 1 2, .gapUpper 2 2, .gapLower 6 5]

-- Cycle fingerprint c7f2ee99b316b0c3f513e8e2516149724dde80a796ab0fc387e8577d0bfff897.
def localCycle00263 : Cycle where
  length := 10
  data := {
    node := ![.theta 3, .distance 2 3, .distance 2 4, .distance 2 5, .distance 5 6, .distance 3 6, .distance 1 3, .distance 3 4, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, 0, 0, -1, 0, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, false, false, false, true] }
  origin := ![.corridorUpper 2 3, .triangle 25 2, .triangle 28 2, .triangle 30 0, .triangle 33 2, .triangle 21 0, .triangle 19 0, .triangle 31 0, .corridorLower 4 5, .thetaNext 3]

-- Cycle fingerprint c9ddc208af3c5cfaa34c1b57aed353545b3e3d2a54e95c433406963aa93dc07f.
def localCycle00264 : Cycle where
  length := 7
  data := {
    node := ![.theta 5, .distance 4 5, .distance 2 4, .distance 1 2, .distance 0 1, .theta 0, .zero, .theta 5]
    constant := ![3, -1, -1, -2, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 1]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.corridorUpper 4 5, .triangle 28 0, .triangle 16 0, .gapLower 1 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 5]

-- Cycle fingerprint ca4885f03d6afe438926a7393ac939d90de0891b092f7108872cf14002950f84.
def localCycle00265 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 3, .distance 2 3, .distance 1 3, .distance 1 5, .distance 1 6, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, 0, -3, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, false] }
  origin := ![.thetaUpper 3, .corridorUpper 2 3, .triangle 15 2, .triangle 20 2, .gapLower 1 4, .triangle 4 0, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint cd9c75a71d03ef2ceaf2a2e7f4c5d81e808418da7719e8b6f3aec928b5b36768.
def localCycle00266 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 3, .distance 3 6, .distance 1 3, .distance 3 5, .distance 4 5, .theta 4]
    constant := ![3, -1, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 0, .triangle 27 0, .triangle 21 0, .triangle 20 0, .triangle 31 1, .corridorLower 4 5]

-- Cycle fingerprint cdaa8f73e9a48812123d45770d270865e27ed6e4820a8394989d7cc4e994c7bc.
def localCycle00267 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 5 6, .distance 2 5, .distance 2 3, .distance 1 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, -1, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 33 0, .triangle 30 0, .triangle 26 1, .triangle 15 0, .triangle 0 0, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint cf4a08bab08f37ffbff13133fc8fad22f9d0ea4d027f25aaa2958bccec979c2e.
def localCycle00268 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 3, .distance 2 4, .distance 4 6, .distance 3 4, .distance 0 3, .distance 0 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, -1, 0, -1, -1, -1, 0, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false, false, true, true, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 0, .triangle 25 2, .triangle 29 0, .triangle 32 0, .triangle 9 0, .triangle 5 1, .triangle 0 1, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint d0501fb5dce182853880fa75e0a1f0e8ce4a82feeae40884a614a2f8d3196c02.
def localCycle00269 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 3, .distance 2 3, .distance 3 4, .distance 3 5, .distance 5 6, .distance 4 5, .distance 0 4, .theta 0, .zero]
    constant := ![0, 3, -1, 0, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, false, false] }
  origin := ![.thetaUpper 3, .corridorUpper 2 3, .triangle 25 0, .triangle 31 2, .triangle 33 0, .triangle 34 0, .triangle 12 0, .corridorLower 0 4, .thetaLower 0]

-- Cycle fingerprint d060595365b030d0db2fab9f612e7c1e57ebef2a657e15e0a0531d555f9b5c25.
def localCycle00270 : Cycle where
  length := 11
  data := {
    node := ![.theta 1, .zero, .theta 3, .distance 2 3, .distance 2 4, .distance 4 6, .distance 1 6, .distance 1 5, .distance 1 4, .distance 1 2, .distance 0 1, .theta 1]
    constant := ![0, 0, 3, 0, -1, 0, -2, 0, 0, -1, -2]
    coefficient := ![0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, true, true, false, false] }
  origin := ![.thetaLower 1, .thetaUpper 3, .corridorUpper 2 3, .triangle 25 2, .triangle 29 0, .gapLower 6 3, .gapLower 1 4, .triangle 22 1, .triangle 16 1, .triangle 0 0, .gapLower 1 0]

-- Cycle fingerprint d0dd6069e85057802969eec3279ece7f5085aa540c29aaa129b6ea7f216c5609.
def localCycle00271 : Cycle where
  length := 14
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 1 3, .distance 3 4, .distance 4 6, .distance 5 6, .distance 0 5, .distance 0 4, .distance 0 3, .distance 0 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, -1, -1, -1, 0, -1, 0, 0, 0, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, true, false, true, true, true, true, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 20 0, .triangle 19 0, .triangle 32 0, .triangle 34 1, .triangle 14 0, .triangle 12 1, .triangle 9 1, .triangle 5 1, .triangle 0 1, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint d120db563c8ccebde67ccf0f9b340cef81e0f3b25124db9bcd79fb89fe4e0f11.
def localCycle00272 : Cycle where
  length := 3
  data := {
    node := ![.distance 3 5, .distance 1 3, .distance 1 5, .distance 3 5]
    constant := ![2, -3, 0]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.gapUpper 3 4, .gapLower 1 5, .triangle 20 1]

-- Cycle fingerprint d2666dd4ec83606a6ebf73546899001b855d82824db28ddd89b0028731656922.
def localCycle00273 : Cycle where
  length := 3
  data := {
    node := ![.distance 4 5, .distance 1 4, .distance 1 5, .distance 4 5]
    constant := ![2, -3, 0]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.gapUpper 4 4, .gapLower 1 4, .triangle 22 1]

-- Cycle fingerprint d2ae7ba9b32715403d765aababc6bec6067e41e71c3b87a240d4ba577ad29f04.
def localCycle00274 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 3, .distance 2 3, .distance 2 4, .distance 4 5, .distance 4 6, .distance 1 6, .distance 1 4, .distance 1 2, .distance 0 1, .theta 1, .zero]
    constant := ![0, 3, 0, -1, 0, 0, -2, 0, -1, -2, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false, true, false, false, false] }
  origin := ![.thetaUpper 3, .corridorUpper 2 3, .triangle 25 2, .triangle 28 0, .triangle 34 2, .gapLower 6 4, .gapLower 1 3, .triangle 16 1, .triangle 0 0, .gapLower 1 0, .thetaLower 1]

-- Cycle fingerprint d2bbdf37239167176b9793735551687b887063d0e03d122655f51e1772e2f532.
def localCycle00275 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 2 4, .distance 4 5, .distance 4 6, .distance 1 4, .distance 1 2, .distance 0 1]
    constant := ![-1, 0, 0, 3, 0, -1, 0, -1, -2, -2]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, true, false, false, false] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 25 2, .triangle 28 0, .triangle 34 2, .triangle 23 0, .gapLower 1 2, .gapLower 1 1]

-- Cycle fingerprint d4a0e4ca89b9dd1dd0d537294ea9d2d10fe9eaa7bd9574e505f234665e159d43.
def localCycle00276 : Cycle where
  length := 8
  data := {
    node := ![.distance 1 2, .distance 0 1, .theta 0, .zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 3, .distance 1 2]
    constant := ![-2, -1, 0, 0, 3, 0, -1, -1]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, false] }
  origin := ![.gapLower 1 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 0, .triangle 15 0]

-- Cycle fingerprint d4b16e551737c7fc0e8ad7597ae92517452092b2d30e683da9d8dcf5c9bcf909.
def localCycle00277 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 2, .distance 0 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 1 3, .distance 1 6, .distance 1 5, .distance 1 2]
    constant := ![-1, -1, 0, 0, 3, -1, 0, 0, -2]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, true, false] }
  origin := ![.triangle 0 0, .corridorLower 0 1, .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 19 0, .triangle 21 2, .triangle 24 1, .gapLower 1 2]

-- Cycle fingerprint d6c1b6929e16d0e290bbbeacfc46005f5958de80a7790088f7a4ad77a4b54a78.
def localCycle00278 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 2, .distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 2 4, .distance 4 6, .distance 1 6, .distance 1 5, .distance 1 2]
    constant := ![-2, -1, 0, 0, 3, 0, -1, 0, -2, 0]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, true, false, true] }
  origin := ![.gapLower 1 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 25 2, .triangle 29 0, .triangle 23 2, .gapLower 1 4, .triangle 17 1]

-- Cycle fingerprint da2960d7b6aaf88731de0cc7cbc90d12c0c91ef65c883fb24a2d8742b3d7ff9e.
def localCycle00279 : Cycle where
  length := 8
  data := {
    node := ![.distance 2 4, .distance 4 6, .distance 1 6, .distance 1 5, .distance 3 5, .distance 3 4, .theta 3, .distance 2 3, .distance 2 4]
    constant := ![-1, 0, -2, 0, 0, -1, 3, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 0]
    strict := ![false, false, false, true, true, false, false, true] }
  origin := ![.triangle 29 0, .gapLower 6 3, .gapLower 1 4, .triangle 20 1, .triangle 31 1, .corridorLower 3 4, .corridorUpper 2 3, .triangle 25 2]

-- Cycle fingerprint dbe105d62e9f57078e9b5dff5ec4a34935da3700703b5e4d342425adfded4992.
def localCycle00280 : Cycle where
  length := 11
  data := {
    node := ![.distance 4 5, .distance 3 5, .distance 2 3, .distance 2 6, .distance 2 4, .distance 1 2, .distance 0 1, .theta 1, .theta 0, .zero, .theta 5, .distance 4 5]
    constant := ![0, -1, 0, 0, -1, -1, -3, 0, 0, 0, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1]
    strict := ![true, false, true, true, false, false, false, true, false, false, false] }
  origin := ![.triangle 31 2, .triangle 26 0, .triangle 27 2, .triangle 29 1, .triangle 16 0, .triangle 0 0, .gapLower 1 0, .thetaNext 0, .thetaLower 0, .thetaUpper 5, .corridorUpper 4 5]

-- Cycle fingerprint dc001319960936f631e7aa3f289e831aba25f308cedf61cbe07d4f48b5dc3112.
def localCycle00281 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 2 4, .distance 4 6, .distance 3 6, .distance 1 3, .distance 3 4, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, 0, -1, 0, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, false, false, true] }
  origin := ![.corridorUpper 2 3, .triangle 25 2, .triangle 29 0, .triangle 32 2, .triangle 21 0, .triangle 19 0, .triangle 31 0, .corridorLower 4 5, .thetaNext 3]

-- Cycle fingerprint dd3a3a7bde32779e6ee6a5de1188bec81c8ec0f01bc26ca6165cca191da12a0c.
def localCycle00282 : Cycle where
  length := 12
  data := {
    node := ![.distance 4 5, .distance 3 5, .distance 2 5, .distance 1 5, .distance 1 6, .distance 1 3, .distance 1 4, .distance 1 2, .distance 0 1, .theta 0, .zero, .theta 5, .distance 4 5]
    constant := ![0, 0, 0, 0, -2, 0, -2, -1, -1, 0, 0, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1]
    strict := ![true, true, true, true, false, true, false, false, false, false, false, false] }
  origin := ![.triangle 31 2, .triangle 26 2, .triangle 17 2, .triangle 24 2, .gapLower 1 4, .triangle 19 2, .gapLower 1 2, .triangle 0 0, .corridorLower 0 1, .thetaLower 0, .thetaUpper 5, .corridorUpper 4 5]

-- Cycle fingerprint df2dfd883d8a3d7cc9d7a10e0a882b30c01a082ddac6280c0be4585de4a03048.
def localCycle00283 : Cycle where
  length := 8
  data := {
    node := ![.distance 4 5, .distance 3 5, .distance 2 3, .distance 1 2, .distance 0 1, .theta 1, .zero, .theta 5, .distance 4 5]
    constant := ![0, -1, -1, -1, -3, 0, 0, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 1]
    strict := ![true, false, false, false, false, false, false, false] }
  origin := ![.triangle 31 2, .triangle 26 0, .triangle 15 0, .triangle 0 0, .gapLower 1 0, .thetaLower 1, .thetaUpper 5, .corridorUpper 4 5]

-- Cycle fingerprint df855051e1c97bd482208ee5ace152a0a7b1e34a84cddb9d8fe31569cdea32a2.
def localCycle00284 : Cycle where
  length := 14
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 4, .distance 1 3, .distance 3 6, .distance 4 6, .distance 5 6, .distance 0 5, .distance 0 4, .distance 0 3, .distance 0 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, -1, -1, -1, 0, 0, -1, 0, 0, 0, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, false, true, true, true, true, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 0, .triangle 19 0, .triangle 21 0, .triangle 32 1, .triangle 34 1, .triangle 14 0, .triangle 12 1, .triangle 9 1, .triangle 5 1, .triangle 0 1, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint dfd318b9403c8af76a6777391919d6cf464e00df578d1ecf63e4020ac7cd6437.
def localCycle00285 : Cycle where
  length := 9
  data := {
    node := ![.distance 3 5, .distance 1 3, .distance 1 6, .distance 1 4, .distance 0 1, .theta 0, .zero, .theta 5, .distance 4 5, .distance 3 5]
    constant := ![-1, -2, -2, -1, -1, 0, 0, 3, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![false, false, false, false, false, false, false, false, true] }
  origin := ![.triangle 20 0, .gapLower 1 4, .gapLower 1 3, .triangle 2 0, .corridorLower 0 1, .thetaLower 0, .thetaUpper 5, .corridorUpper 4 5, .triangle 31 2]

-- Cycle fingerprint e06c0278487e1edc6fe50f5586543a78501ee2ebd548ef78a01d0dad7a0cf027.
def localCycle00286 : Cycle where
  length := 4
  data := {
    node := ![.distance 1 3, .distance 1 4, .distance 4 6, .distance 3 6, .distance 1 3]
    constant := ![-3, -1, 0, 2]
    coefficient := ![0, 0, 0, 0]
    strict := ![false, false, true, true] }
  origin := ![.gapLower 1 5, .triangle 23 0, .triangle 32 2, .gapUpper 3 4]

-- Cycle fingerprint e10f286ac04c10b35271e38e177909873369e47244aa0e02d2b9d82089b7a992.
def localCycle00287 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 3, .distance 1 4, .distance 1 2, .distance 0 1, .theta 0, .zero, .theta 5, .distance 4 5, .distance 3 5, .distance 1 3]
    constant := ![0, -2, -2, -1, 0, 0, 3, 0, -1]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![true, false, false, false, false, false, false, true, false] }
  origin := ![.triangle 19 2, .gapLower 1 2, .gapLower 1 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 20 0]

-- Cycle fingerprint e14f7386a1e5116bc964e4b6ee45ebce46d6afd48676c2df4a1eefc5b251c2c9.
def localCycle00288 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 2 4, .distance 2 5, .distance 5 6, .distance 3 5, .distance 1 3, .distance 3 4, .theta 3]
    constant := ![3, 0, 0, -1, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 25 2, .triangle 28 2, .triangle 30 0, .triangle 33 0, .triangle 20 0, .triangle 19 0, .corridorLower 3 4]

-- Cycle fingerprint e1f841a8b883d0a3dd1ec567175add4c7da0fdee0e0dd293276460506cc01186.
def localCycle00289 : Cycle where
  length := 13
  data := {
    node := ![.distance 2 3, .distance 1 3, .distance 1 5, .distance 1 6, .distance 5 6, .distance 3 5, .distance 3 4, .distance 0 3, .distance 0 2, .distance 0 1, .theta 1, .zero, .theta 3, .distance 2 3]
    constant := ![0, 0, -2, 0, -1, 0, -1, 0, 0, -2, 0, 0, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1]
    strict := ![true, true, false, true, false, false, false, false, true, false, false, false, false] }
  origin := ![.triangle 15 2, .triangle 20 2, .gapLower 1 4, .triangle 24 1, .triangle 33 0, .gapLower 3 2, .triangle 9 0, .gapLower 0 2, .triangle 0 1, .gapLower 1 0, .thetaLower 1, .thetaUpper 3, .corridorUpper 2 3]

-- Cycle fingerprint e22763b22e15d15084ab0d1cd4b585974ca137c2e78d0a0deeea7f47f294da2a.
def localCycle00290 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 3, .distance 1 5, .distance 1 6, .distance 1 2, .distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 1 3]
    constant := ![0, -2, 0, -2, -1, 0, 0, 3, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![true, false, true, false, false, false, false, false, true] }
  origin := ![.triangle 20 2, .gapLower 1 4, .triangle 18 1, .gapLower 1 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 15 2]

-- Cycle fingerprint e2fc335aa4904a2e7278cec11844b0eff64fbaaa8790e568d5323e897a0f5fde.
def localCycle00291 : Cycle where
  length := 5
  data := {
    node := ![.distance 4 6, .distance 3 6, .distance 1 3, .distance 1 4, .distance 1 6, .distance 4 6]
    constant := ![0, 2, 0, -2, 0]
    coefficient := ![0, 0, 0, 0, 0]
    strict := ![true, true, true, false, true] }
  origin := ![.triangle 32 2, .gapUpper 3 4, .triangle 19 2, .gapLower 1 4, .triangle 23 1]

-- Cycle fingerprint e5b377f9776cb84f16b5904cc88165dfcc32d114d825a653c5ebed61189d4478.
def localCycle00292 : Cycle where
  length := 3
  data := {
    node := ![.distance 3 6, .distance 1 3, .distance 1 6, .distance 3 6]
    constant := ![2, -3, 0]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.gapUpper 3 4, .gapLower 1 5, .triangle 21 1]

-- Cycle fingerprint e6674f04dbe55728927fa8d4bac3556ef39291a9731404765b237b7261514c16.
def localCycle00293 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .theta 1, .distance 1 3, .distance 1 4, .distance 4 5, .distance 3 5, .distance 5 6, .distance 0 5, .distance 0 4, .distance 0 1]
    constant := ![-2, 2, 0, -1, 0, -1, -1, 0, 0]
    coefficient := ![0, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false, false, true] }
  origin := ![.gapLower 1 0, .gapLower 1 6, .triangle 19 2, .triangle 22 0, .triangle 31 2, .triangle 33 0, .triangle 14 0, .gapLower 0 4, .triangle 2 1]

-- Cycle fingerprint e679aeb0775d359346b4ac1f117e5724cc5508a57d31ac106cfd1c08f59cda8c.
def localCycle00294 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 3, .distance 1 5, .distance 0 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 2 4, .distance 1 4, .distance 1 6, .distance 1 3]
    constant := ![-2, -1, -1, 0, 0, 3, 0, 0, -2, 0]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, true, false, true] }
  origin := ![.gapLower 1 3, .triangle 3 0, .corridorLower 0 1, .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 16 2, .gapLower 1 5, .triangle 21 1]

-- Cycle fingerprint e813e78db01c577444132a631a93c4c532016fdb8122f7c29e356b9028996be0.
def localCycle00295 : Cycle where
  length := 11
  data := {
    node := ![.distance 0 4, .distance 0 1, .theta 1, .zero, .theta 3, .distance 2 3, .distance 1 3, .distance 1 5, .distance 3 5, .distance 5 6, .distance 0 5, .distance 0 4]
    constant := ![0, -2, 0, 0, 3, 0, -2, 0, -1, -1, 0]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![true, false, false, false, false, true, false, true, false, false, false] }
  origin := ![.triangle 2 1, .gapLower 1 0, .thetaLower 1, .thetaUpper 3, .corridorUpper 2 3, .triangle 15 2, .gapLower 1 5, .triangle 20 1, .triangle 33 0, .triangle 14 0, .gapLower 0 4]

-- Cycle fingerprint e841e3efb2ae5eb1b8ee122ef6b051ffc4afbc2be739fef15a6d8fc8e2c67913.
def localCycle00296 : Cycle where
  length := 6
  data := {
    node := ![.distance 1 5, .distance 1 6, .distance 1 4, .distance 1 2, .theta 1, .distance 1 3, .distance 1 5]
    constant := ![0, -2, 0, -1, 2, 0]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![true, false, true, false, false, true] }
  origin := ![.triangle 24 2, .gapLower 1 3, .triangle 16 1, .corridorLower 1 2, .gapLower 1 6, .triangle 20 2]

-- Cycle fingerprint e8ba35ab1f430aa73eb812c2e9918c827369b0084b1f441ef23bb2dcda4eb5b3.
def localCycle00297 : Cycle where
  length := 8
  data := {
    node := ![.distance 3 4, .distance 1 3, .distance 1 5, .distance 1 2, .distance 0 1, .theta 0, .zero, .theta 4, .distance 3 4]
    constant := ![-1, 0, -2, -1, -1, 0, 0, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 1]
    strict := ![false, true, false, false, false, false, false, false] }
  origin := ![.triangle 19 0, .triangle 20 2, .gapLower 1 2, .triangle 0 0, .corridorLower 0 1, .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4]

-- Cycle fingerprint e8bbbdede634863b67a3fbef55daaa340255ebd7e9ed9d4fcce19604d29a4271.
def localCycle00298 : Cycle where
  length := 8
  data := {
    node := ![.distance 4 5, .distance 0 4, .distance 0 3, .distance 0 1, .theta 1, .distance 1 4, .distance 1 3, .distance 3 5, .distance 4 5]
    constant := ![-1, 0, 0, -2, 2, 0, -1, 0]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![false, false, true, false, false, true, false, true] }
  origin := ![.triangle 12 0, .gapLower 0 3, .triangle 1 1, .gapLower 1 0, .gapLower 1 6, .triangle 19 1, .triangle 20 0, .triangle 31 1]

-- Cycle fingerprint e8d6445f3451cde4d3b012655461076b83b8fc573ae3d92f62cd9d99094c1d0d.
def localCycle00299 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 3, .distance 2 3, .distance 3 4, .distance 1 3, .distance 3 6, .distance 3 5, .distance 0 3, .distance 0 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, -1, -1, -1, 0, -1, 0, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, true, true, false, false] }
  origin := ![.thetaUpper 3, .corridorUpper 2 3, .triangle 25 0, .triangle 19 0, .triangle 21 0, .triangle 33 1, .triangle 10 0, .triangle 5 1, .triangle 0 1, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint e8ec8357f863d275000855573021003e33766a471863fa4f6e896e7eb95f6f96.
def localCycle00300 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 5 6, .distance 3 6, .distance 2 3, .distance 2 5, .distance 2 4, .distance 1 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, -1, 0, -1, 0, 0, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true, true, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 34 0, .triangle 33 2, .triangle 27 0, .triangle 26 2, .triangle 28 1, .triangle 16 0, .triangle 0 0, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint e988d55943747bbab3fb25a36c27c82a288a10cf05422b2682cfcd771d954d7d.
def localCycle00301 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 3 6, .distance 2 6, .distance 1 6, .distance 1 3, .distance 1 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, 0, 0, 0, -2, 0, -2, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, true, true, false, true, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 33 2, .triangle 27 2, .triangle 18 2, .gapLower 1 4, .triangle 15 1, .gapLower 1 1, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint ea57cd2d52dde75aebb7f35c57f86dc96e43fed5d5687e4d2929db130f2d7be4.
def localCycle00302 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 2, .distance 0 1, .theta 1, .zero, .theta 5, .distance 4 5, .distance 3 5, .distance 1 3, .distance 1 6, .distance 1 4, .distance 1 2]
    constant := ![-1, -2, 0, 0, 3, 0, -1, 0, -2, 0]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, true, false, true] }
  origin := ![.triangle 0 0, .gapLower 1 0, .thetaLower 1, .thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 20 0, .triangle 21 2, .gapLower 1 3, .triangle 16 1]

-- Cycle fingerprint eac40286db67525356d052a6c8de2ad24c6edb740d52c9b3b683c466ce253f2b.
def localCycle00303 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 4, .distance 1 2, .distance 0 1, .theta 1, .zero, .theta 3, .distance 2 3, .distance 1 3, .distance 1 5, .distance 1 6, .distance 1 4]
    constant := ![0, -1, -2, 0, 0, 3, 0, 0, -2, 0]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![true, false, false, false, false, false, true, true, false, true] }
  origin := ![.triangle 16 1, .triangle 0 0, .gapLower 1 0, .thetaLower 1, .thetaUpper 3, .corridorUpper 2 3, .triangle 15 2, .triangle 20 2, .gapLower 1 4, .triangle 23 1]

-- Cycle fingerprint eaf55b498e55c314791361eef4e4bb8276742e197d39314c5234b692635e3977.
def localCycle00304 : Cycle where
  length := 11
  data := {
    node := ![.theta 3, .distance 2 3, .distance 2 4, .distance 4 5, .distance 4 6, .distance 1 4, .distance 1 2, .distance 0 1, .theta 1, .theta 0, .zero, .theta 3]
    constant := ![3, 0, -1, 0, -1, 0, -2, -2, 0, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, false, true, false, false, false, false, true, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 25 2, .triangle 28 0, .triangle 34 2, .triangle 23 0, .gapLower 1 2, .gapLower 1 1, .gapLower 1 0, .thetaNext 0, .thetaLower 0, .thetaUpper 3]

-- Cycle fingerprint eb63669cd43234dc68cb37f07af75843b30a3dba511d30987414fa5dff48975f.
def localCycle00305 : Cycle where
  length := 8
  data := {
    node := ![.distance 3 4, .distance 0 3, .distance 0 2, .distance 0 1, .theta 1, .distance 1 3, .distance 3 6, .distance 3 5, .distance 3 4]
    constant := ![-1, 0, 0, -2, 2, -1, 0, 0]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![false, false, true, false, false, false, true, true] }
  origin := ![.triangle 9 0, .gapLower 0 2, .triangle 0 1, .gapLower 1 0, .gapLower 1 6, .triangle 21 0, .triangle 33 1, .triangle 31 1]

-- Cycle fingerprint ed8c5cb4d7bc8981e1c7d168896bb60515fa165747f8fec8905bf8d687feacab.
def localCycle00306 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 3, .distance 2 5, .distance 1 2, .distance 0 1, .theta 0, .zero, .theta 4]
    constant := ![3, -1, 0, -1, -3, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 1]
    strict := ![false, false, true, false, false, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 0, .triangle 26 2, .triangle 17 0, .gapLower 1 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 4]

-- Cycle fingerprint edbe47c92e8318715c1c1359ab0477423e4a27651a9faf442d0b87ef10f58b2e.
def localCycle00307 : Cycle where
  length := 8
  data := {
    node := ![.distance 3 4, .theta 3, .distance 2 3, .distance 1 3, .distance 1 4, .distance 1 5, .distance 1 6, .distance 4 6, .distance 3 4]
    constant := ![-1, 3, 0, 0, -2, -2, 0, -1]
    coefficient := ![0, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, true, false] }
  origin := ![.corridorLower 3 4, .corridorUpper 2 3, .triangle 15 2, .triangle 19 2, .gapLower 1 4, .gapLower 1 3, .triangle 23 1, .triangle 32 0]

-- Cycle fingerprint edd183f4d51f91d67ee616be57b90c7b034a602ccaecf2bc5957282dacc98a62.
def localCycle00308 : Cycle where
  length := 9
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 2 3, .distance 3 4, .distance 1 3, .distance 3 6, .distance 4 6, .distance 5 6, .theta 5]
    constant := ![3, 0, -1, -1, -1, -1, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, true, true, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 26 0, .triangle 25 0, .triangle 19 0, .triangle 21 0, .triangle 32 1, .triangle 34 1, .corridorLower 5 6]

-- Cycle fingerprint eec9567d242dd2f42c82db86475257d3b050d1984e2364d3de40ad581f1b1b3d.
def localCycle00309 : Cycle where
  length := 10
  data := {
    node := ![.theta 0, .zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 3, .distance 2 6, .distance 2 4, .distance 1 2, .distance 0 1, .theta 0]
    constant := ![0, 0, 3, 0, -1, 0, 0, -1, -3, -1]
    coefficient := ![0, 1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true, true, false, false, false] }
  origin := ![.thetaLower 0, .thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 0, .triangle 27 2, .triangle 29 1, .triangle 16 0, .gapLower 1 1, .corridorLower 0 1]

-- Cycle fingerprint ef4cfe4a99231008ef49ba7099b0478f8e7685c127b57242abb814053657bbcf.
def localCycle00310 : Cycle where
  length := 9
  data := {
    node := ![.distance 2 4, .distance 1 4, .distance 1 6, .distance 1 2, .distance 0 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 2 4]
    constant := ![0, -2, 0, -2, -1, 0, 0, 3, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![true, false, true, false, false, false, false, false, true] }
  origin := ![.triangle 16 2, .gapLower 1 5, .triangle 18 1, .gapLower 1 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 25 2]

-- Cycle fingerprint ef65b905b00ffdd033402825d7ef090bfdde6be1b7f0a386bb4eade246db3bd5.
def localCycle00311 : Cycle where
  length := 6
  data := {
    node := ![.theta 4, .distance 3 4, .distance 1 3, .distance 1 5, .distance 3 5, .distance 4 5, .theta 4]
    constant := ![3, -1, -2, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 19 0, .gapLower 1 3, .triangle 20 1, .triangle 31 1, .corridorLower 4 5]

-- Cycle fingerprint f0e3bbe206cee15c7119f051cb58eb4b46bf86eb7740a08a14b46f1d530c6100.
def localCycle00312 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 1 5, .distance 1 6, .distance 1 3, .distance 1 4, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, 0, 0, 0, -2, -2, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, true, true, false, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 17 2, .triangle 24 2, .gapLower 1 4, .gapLower 1 3, .triangle 2 0, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint f150b1fc1433ae759aae0332701eabecfcbc83a841a621cd4b309559c2429bd6.
def localCycle00313 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 2 3, .distance 2 4, .distance 4 5, .distance 1 4, .distance 4 6, .distance 3 4, .theta 3]
    constant := ![3, 0, -1, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 25 2, .triangle 28 0, .triangle 22 0, .triangle 23 0, .triangle 32 0, .corridorLower 3 4]

-- Cycle fingerprint f1fa62db4d8d99901136172053ac45bf3e2256bc1f20800c64f86f718674b7bf.
def localCycle00314 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 1, .distance 1 3, .distance 1 5, .distance 3 5, .distance 5 6, .distance 0 5, .distance 0 4, .theta 0, .zero]
    constant := ![0, 2, -2, 0, -1, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, false, false] }
  origin := ![.thetaUpper 1, .gapLower 1 6, .gapLower 1 5, .triangle 20 1, .triangle 33 0, .triangle 14 0, .gapLower 0 4, .corridorLower 0 4, .thetaLower 0]

-- Cycle fingerprint f257c26828af5bf535c65467c51730864168a66a8ab27a03e8993f48d03d0c7a.
def localCycle00315 : Cycle where
  length := 7
  data := {
    node := ![.distance 3 6, .distance 5 6, .theta 5, .distance 4 5, .distance 3 5, .distance 1 3, .distance 1 6, .distance 3 6]
    constant := ![0, -1, 3, 0, -1, -2, 0]
    coefficient := ![0, 0, 1, 0, 0, 0, 0]
    strict := ![true, false, false, true, false, false, true] }
  origin := ![.triangle 33 1, .corridorLower 5 6, .corridorUpper 4 5, .triangle 31 2, .triangle 20 0, .gapLower 1 4, .triangle 21 1]

-- Cycle fingerprint f282f8004ba74d12946e273297ac2d80989f54ec4a27a7350c637632d983d815.
def localCycle00316 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 4, .distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 2 4, .distance 4 6, .distance 1 6, .distance 1 5, .distance 1 4]
    constant := ![-1, -1, 0, 0, 3, 0, -1, 0, -2, -2]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, false, false, false] }
  origin := ![.triangle 2 0, .corridorLower 0 1, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 25 2, .triangle 29 0, .gapLower 6 3, .gapLower 1 4, .gapLower 1 3]

-- Cycle fingerprint f2fd1d510c371647302fac5e3764e4a8cb5e97b5a580232b81dca9f76d74b64f.
def localCycle00317 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 2, .distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 2 5, .distance 5 6, .distance 1 6, .distance 1 5, .distance 1 2]
    constant := ![-2, -1, 0, 0, 3, 0, -1, 0, -2, 0]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, true, false, true] }
  origin := ![.gapLower 1 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 26 2, .triangle 30 0, .triangle 24 2, .gapLower 1 4, .triangle 17 1]

-- Cycle fingerprint f309dd6c6c266fb055c208b2f5d0d23bf3c3aa313dd07ae7d5ef4bbd4f7b2129.
def localCycle00318 : Cycle where
  length := 4
  data := {
    node := ![.distance 1 4, .distance 1 2, .distance 2 6, .distance 4 6, .distance 1 4]
    constant := ![-3, 2, 0, -1]
    coefficient := ![0, 0, 0, 0]
    strict := ![false, true, false, false] }
  origin := ![.gapLower 1 2, .gapUpper 2 2, .gapLower 6 5, .triangle 23 0]

-- Cycle fingerprint f35b45b87e24f0a7d84682a9c28019aa997214d76b64fe05898bd8b0897cc1bf.
def localCycle00319 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .theta 1, .zero, .theta 5, .distance 4 5, .distance 3 5, .distance 1 3, .distance 1 6, .distance 1 4, .distance 1 2, .distance 0 1]
    constant := ![-2, 0, 0, 3, 0, -1, 0, 0, -2, -1]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, true, true, false, false] }
  origin := ![.gapLower 1 0, .thetaLower 1, .thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 20 0, .triangle 21 2, .triangle 23 1, .gapLower 1 2, .triangle 0 0]

-- Cycle fingerprint f40b9cb3ebf655ac278de1bb22132eaedff1ceed224c93fe1390397c8285d03f.
def localCycle00320 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 5, .distance 1 3, .distance 1 4, .distance 4 6, .distance 3 4, .theta 3]
    constant := ![3, -1, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 26 0, .triangle 20 0, .gapLower 1 4, .triangle 23 0, .triangle 32 0, .corridorLower 3 4]

-- Cycle fingerprint f485f63e7494db9808a463c3d9e00dad33855fb5645da5c09703df29ccbec281.
def localCycle00321 : Cycle where
  length := 9
  data := {
    node := ![.distance 2 5, .distance 1 2, .distance 0 1, .theta 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 2 3, .distance 2 5]
    constant := ![-1, -2, -2, 0, 0, 0, 3, -1, 0]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, true, false, false, false, false, true] }
  origin := ![.triangle 17 0, .gapLower 1 1, .gapLower 1 0, .thetaNext 0, .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 25 0, .triangle 26 2]

-- Cycle fingerprint f4d4f2bd49a24d1675d8a762bdb8d132d16550bc5dd8a84dc9d70cff0ec01a31.
def localCycle00322 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 5, .distance 1 6, .distance 1 4, .distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 1 3, .distance 1 5]
    constant := ![0, -3, -1, -1, 0, 0, 3, 0, 0]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![true, false, false, false, false, false, false, true, true] }
  origin := ![.triangle 24 2, .gapLower 1 3, .triangle 2 0, .corridorLower 0 1, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 15 2, .triangle 20 2]

-- Cycle fingerprint f5c1685e013c9c90ae745a5e0aa05f6a150db0a07a4e5f28ab9ccdc73a134436.
def localCycle00323 : Cycle where
  length := 10
  data := {
    node := ![.theta 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 2 3, .distance 2 6, .distance 2 5, .distance 1 2, .distance 0 1, .theta 1]
    constant := ![0, 0, 0, 3, -1, 0, 0, -1, -2, -2]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![true, false, false, false, false, true, true, false, false, false] }
  origin := ![.thetaNext 0, .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 25 0, .triangle 27 2, .triangle 30 1, .triangle 17 0, .gapLower 1 1, .gapLower 1 0]

-- Cycle fingerprint f5ebd9eb1d535c81b780118bf6b7c38242792b5619b6fb1bfa5ae243e4474fea.
def localCycle00324 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 2 3, .distance 2 6, .distance 2 5, .distance 1 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, -1, 0, 0, -1, -2, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 25 0, .triangle 27 2, .triangle 30 1, .triangle 17 0, .gapLower 1 1, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint f630c8b56128b9efbb8fbd0d72e85666ca06ebbbac0cfd3ef669fe745caf0615.
def localCycle00325 : Cycle where
  length := 11
  data := {
    node := ![.distance 3 5, .distance 5 6, .distance 0 5, .distance 0 4, .theta 0, .zero, .theta 1, .distance 1 3, .distance 1 4, .distance 1 5, .distance 4 5, .distance 3 5]
    constant := ![-1, -1, 0, -1, 0, 0, 2, 0, -2, 0, 0]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, true, false, true, true] }
  origin := ![.triangle 33 0, .triangle 14 0, .gapLower 0 4, .corridorLower 0 4, .thetaLower 0, .thetaUpper 1, .gapLower 1 6, .triangle 19 2, .gapLower 1 4, .triangle 22 1, .triangle 31 2]

-- Cycle fingerprint f688318c554d03945d75815ae3886b40d74cc74c6eafec419ca82025e7b570f8.
def localCycle00326 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 5 6, .distance 2 5, .distance 2 4, .distance 1 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, -1, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 34 0, .triangle 30 0, .triangle 28 1, .triangle 16 0, .triangle 0 0, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint f6ed8230b39601d3b9cae7c6b0c1a94cb2e0625b9c74bf7e006361f83eab05e1.
def localCycle00327 : Cycle where
  length := 8
  data := {
    node := ![.theta 0, .zero, .theta 4, .distance 3 4, .distance 1 3, .distance 1 6, .distance 1 5, .distance 0 1, .theta 0]
    constant := ![0, 0, 3, -1, -2, -2, -1, -1]
    coefficient := ![0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 19 0, .gapLower 1 4, .gapLower 1 3, .triangle 3 0, .corridorLower 0 1]

-- Cycle fingerprint f70a988cd39aac02682326052dc2745574da9de6257931be83c17578e5fc5db4.
def localCycle00328 : Cycle where
  length := 11
  data := {
    node := ![.theta 0, .zero, .theta 3, .distance 2 3, .distance 2 5, .distance 5 6, .distance 1 6, .distance 1 5, .distance 1 4, .distance 1 2, .distance 0 1, .theta 0]
    constant := ![0, 0, 3, 0, -1, 0, -2, 0, -2, -1, -1]
    coefficient := ![0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, true, false, false, false] }
  origin := ![.thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 26 2, .triangle 30 0, .gapLower 6 3, .gapLower 1 4, .triangle 22 1, .gapLower 1 2, .triangle 0 0, .corridorLower 0 1]

-- Cycle fingerprint f72056c89fc415c1e592a1c873efa5a01e039f6a4604814d36e59fb50dcf1cea.
def localCycle00329 : Cycle where
  length := 7
  data := {
    node := ![.theta 1, .distance 1 5, .distance 5 6, .distance 0 5, .distance 0 4, .theta 0, .zero, .theta 1]
    constant := ![1, -1, -1, 0, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 1]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 1 6, .triangle 24 0, .triangle 14 0, .gapLower 0 4, .corridorLower 0 4, .thetaLower 0, .thetaUpper 1]

-- Cycle fingerprint f7426e7ede10dc413047f0b35f4c49ecb00695e45beddd2750ad633b13642d8b.
def localCycle00330 : Cycle where
  length := 8
  data := {
    node := ![.theta 0, .zero, .theta 3, .distance 2 3, .distance 1 3, .distance 1 6, .distance 1 2, .distance 0 1, .theta 0]
    constant := ![0, 0, 3, 0, -2, 0, -2, -1]
    coefficient := ![0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true, false, false] }
  origin := ![.thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 15 2, .gapLower 1 5, .triangle 18 1, .gapLower 1 1, .corridorLower 0 1]

-- Cycle fingerprint f865562efad7d922ac5a9569825d6b9ea0db14ae02914cb0fb410bb4024a7520.
def localCycle00331 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 4, .distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 2 4, .distance 4 5, .distance 1 5, .distance 1 6, .distance 1 4]
    constant := ![-1, -1, 0, 0, 3, 0, -1, 0, -2, -2]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, false, false, false] }
  origin := ![.triangle 2 0, .corridorLower 0 1, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 25 2, .triangle 28 0, .gapLower 5 4, .gapLower 1 4, .gapLower 1 3]

-- Cycle fingerprint f8956432bf5bb39f46ca001fc8d2ac149f57409128b6660f15c7c81325008600.
def localCycle00332 : Cycle where
  length := 5
  data := {
    node := ![.theta 5, .distance 4 5, .distance 2 4, .distance 2 6, .theta 6, .theta 5]
    constant := ![3, -1, 0, -2, 0]
    coefficient := ![1, 0, 0, -1, 0]
    strict := ![false, false, true, true, true] }
  origin := ![.corridorUpper 4 5, .triangle 28 0, .triangle 29 2, .gapUpper 6 6, .thetaNext 5]

-- Cycle fingerprint f8ddc4aa5ea13ebe3df97ca80fd75d4cc700e3da80c6ade6aeeed363e9559b8c.
def localCycle00333 : Cycle where
  length := 6
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 6, .distance 1 3, .distance 3 5, .distance 3 4, .theta 3]
    constant := ![3, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 27 0, .triangle 21 0, .triangle 20 0, .triangle 31 1, .corridorLower 3 4]

-- Cycle fingerprint f93cb8ee312650c13631ecc97d9431a188deaf854ea3c72fb0356aa6e08400e9.
def localCycle00334 : Cycle where
  length := 13
  data := {
    node := ![.zero, .theta 3, .distance 2 3, .distance 1 3, .distance 1 4, .distance 1 5, .distance 5 6, .distance 4 5, .distance 3 4, .distance 0 3, .distance 0 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, 0, 0, -1, -1, -1, -1, 0, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, true, false, false, false, false, true, true, false, false] }
  origin := ![.thetaUpper 3, .corridorUpper 2 3, .triangle 15 2, .triangle 19 2, .triangle 22 2, .triangle 24 0, .triangle 34 0, .triangle 31 0, .triangle 9 0, .triangle 5 1, .triangle 0 1, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint fa30e049f833b6186c52f37ed7457eb71906230a41a8f85fa03cf088bd4d91b9.
def localCycle00335 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 1 3, .distance 3 5, .distance 4 5, .distance 5 6, .distance 0 5, .theta 0, .zero]
    constant := ![0, 3, -1, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 19 0, .triangle 20 0, .triangle 31 1, .triangle 34 0, .triangle 14 0, .corridorLower 0 5, .thetaLower 0]

-- Cycle fingerprint fb21f9076743db575fbeff52e51cc6e09bdd094ea489610b002587aa684b54a6.
def localCycle00336 : Cycle where
  length := 9
  data := {
    node := ![.distance 4 6, .distance 3 6, .distance 1 3, .distance 1 4, .distance 4 5, .distance 3 4, .theta 3, .distance 2 3, .distance 2 4, .distance 4 6]
    constant := ![0, -1, 0, -1, -1, -1, 3, 0, -1]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 0, 0]
    strict := ![true, false, false, false, false, false, false, true, false] }
  origin := ![.triangle 32 2, .triangle 21 0, .gapLower 1 4, .triangle 22 0, .triangle 31 0, .corridorLower 3 4, .corridorUpper 2 3, .triangle 25 2, .triangle 29 0]

-- Cycle fingerprint fb2642c7fb7ee8ad5c8965c1478fe20e8d31d226bf7d5dc44f240f5f4cd35f64.
def localCycle00337 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 2, .distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 1 3, .distance 1 4, .distance 1 5, .distance 1 6, .distance 1 2]
    constant := ![-1, -1, 0, 0, 3, 0, 0, 0, -2, -2]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, true, false, false] }
  origin := ![.triangle 0 0, .corridorLower 0 1, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 15 2, .triangle 19 2, .triangle 22 2, .gapLower 1 3, .gapLower 1 2]

-- Cycle fingerprint fb9af06078fdfeee28f5ac13a9a19b000f6eb523ced2db5a0716d2764d4245c6.
def localCycle00338 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 5 6, .distance 3 5, .distance 2 3, .distance 1 3, .distance 3 4, .distance 0 3, .theta 0, .zero]
    constant := ![0, 3, -1, -1, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 34 0, .triangle 33 0, .triangle 26 0, .triangle 15 2, .triangle 19 0, .triangle 9 0, .corridorLower 0 3, .thetaLower 0]

-- Cycle fingerprint fc006d36973ba78c03b1467c5ce69b59b795f14d3c4d91ec412fa70100460816.
def localCycle00339 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .theta 1, .distance 1 3, .distance 1 4, .distance 4 6, .distance 4 5, .distance 3 4, .distance 0 3, .distance 0 2, .theta 2]
    constant := ![0, 1, 0, -1, 0, -1, -1, 0, 0]
    coefficient := ![0, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![true, false, true, false, true, false, false, false, false] }
  origin := ![.thetaNext 1, .gapLower 1 6, .triangle 19 2, .triangle 23 0, .triangle 34 1, .triangle 31 0, .triangle 9 0, .gapLower 0 2, .gapLower 2 0]

-- Cycle fingerprint fcc3bec42e1bb6f7f51467fcf1fc6d4b697edd15e56765b915f19db94da11147.
def localCycle00340 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 2 3, .distance 2 5, .distance 5 6, .distance 3 5, .distance 1 3, .distance 3 4, .theta 3]
    constant := ![3, 0, -1, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 26 2, .triangle 30 0, .triangle 33 0, .triangle 20 0, .triangle 19 0, .corridorLower 3 4]

-- Cycle fingerprint fce6a4ddc9a335d6fee031099c2eea2547a7ba98489e1e085bb4ec1dbe444794.
def localCycle00341 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 4, .distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 2 5, .distance 5 6, .distance 1 6, .distance 1 5, .distance 1 4]
    constant := ![-1, -1, 0, 0, 3, 0, -1, 0, -2, -2]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, false, false, false] }
  origin := ![.triangle 2 0, .corridorLower 0 1, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 26 2, .triangle 30 0, .gapLower 6 3, .gapLower 1 4, .gapLower 1 3]

-- Cycle fingerprint fddd90d4596465193b06ee2dd1b41d281c11462154ddc1ed0f77d65a09f5ef11.
def localCycle00342 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 4, .distance 4 6, .distance 3 4, .theta 3, .distance 2 3, .distance 2 4, .distance 4 5, .distance 3 5, .distance 1 3, .distance 1 4]
    constant := ![-1, -1, -1, 3, 0, -1, 0, -1, 0]
    coefficient := ![0, 0, 0, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, true, false, false] }
  origin := ![.triangle 23 0, .triangle 32 0, .corridorLower 3 4, .corridorUpper 2 3, .triangle 25 2, .triangle 28 0, .triangle 31 2, .triangle 20 0, .gapLower 1 4]

def library : Library := fun id => if id < 171 then (if id < 85 then (if id < 42 then (if id < 21 then (if id < 10 then (if id < 5 then (if id < 2 then (if id < 1 then (if id = 0 then some localCycle00000 else none) else (if id = 1 then some localCycle00001 else none)) else (if id < 3 then (if id = 2 then some localCycle00002 else none) else (if id < 4 then (if id = 3 then some localCycle00003 else none) else (if id = 4 then some localCycle00004 else none)))) else (if id < 7 then (if id < 6 then (if id = 5 then some localCycle00005 else none) else (if id = 6 then some localCycle00006 else none)) else (if id < 8 then (if id = 7 then some localCycle00007 else none) else (if id < 9 then (if id = 8 then some localCycle00008 else none) else (if id = 9 then some localCycle00009 else none))))) else (if id < 15 then (if id < 12 then (if id < 11 then (if id = 10 then some localCycle00010 else none) else (if id = 11 then some localCycle00011 else none)) else (if id < 13 then (if id = 12 then some localCycle00012 else none) else (if id < 14 then (if id = 13 then some localCycle00013 else none) else (if id = 14 then some localCycle00014 else none)))) else (if id < 18 then (if id < 16 then (if id = 15 then some localCycle00015 else none) else (if id < 17 then (if id = 16 then some localCycle00016 else none) else (if id = 17 then some localCycle00017 else none))) else (if id < 19 then (if id = 18 then some localCycle00018 else none) else (if id < 20 then (if id = 19 then some localCycle00019 else none) else (if id = 20 then some localCycle00020 else none)))))) else (if id < 31 then (if id < 26 then (if id < 23 then (if id < 22 then (if id = 21 then some localCycle00021 else none) else (if id = 22 then some localCycle00022 else none)) else (if id < 24 then (if id = 23 then some localCycle00023 else none) else (if id < 25 then (if id = 24 then some localCycle00024 else none) else (if id = 25 then some localCycle00025 else none)))) else (if id < 28 then (if id < 27 then (if id = 26 then some localCycle00026 else none) else (if id = 27 then some localCycle00027 else none)) else (if id < 29 then (if id = 28 then some localCycle00028 else none) else (if id < 30 then (if id = 29 then some localCycle00029 else none) else (if id = 30 then some localCycle00030 else none))))) else (if id < 36 then (if id < 33 then (if id < 32 then (if id = 31 then some localCycle00031 else none) else (if id = 32 then some localCycle00032 else none)) else (if id < 34 then (if id = 33 then some localCycle00033 else none) else (if id < 35 then (if id = 34 then some localCycle00034 else none) else (if id = 35 then some localCycle00035 else none)))) else (if id < 39 then (if id < 37 then (if id = 36 then some localCycle00036 else none) else (if id < 38 then (if id = 37 then some localCycle00037 else none) else (if id = 38 then some localCycle00038 else none))) else (if id < 40 then (if id = 39 then some localCycle00039 else none) else (if id < 41 then (if id = 40 then some localCycle00040 else none) else (if id = 41 then some localCycle00041 else none))))))) else (if id < 63 then (if id < 52 then (if id < 47 then (if id < 44 then (if id < 43 then (if id = 42 then some localCycle00042 else none) else (if id = 43 then some localCycle00043 else none)) else (if id < 45 then (if id = 44 then some localCycle00044 else none) else (if id < 46 then (if id = 45 then some localCycle00045 else none) else (if id = 46 then some localCycle00046 else none)))) else (if id < 49 then (if id < 48 then (if id = 47 then some localCycle00047 else none) else (if id = 48 then some localCycle00048 else none)) else (if id < 50 then (if id = 49 then some localCycle00049 else none) else (if id < 51 then (if id = 50 then some localCycle00050 else none) else (if id = 51 then some localCycle00051 else none))))) else (if id < 57 then (if id < 54 then (if id < 53 then (if id = 52 then some localCycle00052 else none) else (if id = 53 then some localCycle00053 else none)) else (if id < 55 then (if id = 54 then some localCycle00054 else none) else (if id < 56 then (if id = 55 then some localCycle00055 else none) else (if id = 56 then some localCycle00056 else none)))) else (if id < 60 then (if id < 58 then (if id = 57 then some localCycle00057 else none) else (if id < 59 then (if id = 58 then some localCycle00058 else none) else (if id = 59 then some localCycle00059 else none))) else (if id < 61 then (if id = 60 then some localCycle00060 else none) else (if id < 62 then (if id = 61 then some localCycle00061 else none) else (if id = 62 then some localCycle00062 else none)))))) else (if id < 74 then (if id < 68 then (if id < 65 then (if id < 64 then (if id = 63 then some localCycle00063 else none) else (if id = 64 then some localCycle00064 else none)) else (if id < 66 then (if id = 65 then some localCycle00065 else none) else (if id < 67 then (if id = 66 then some localCycle00066 else none) else (if id = 67 then some localCycle00067 else none)))) else (if id < 71 then (if id < 69 then (if id = 68 then some localCycle00068 else none) else (if id < 70 then (if id = 69 then some localCycle00069 else none) else (if id = 70 then some localCycle00070 else none))) else (if id < 72 then (if id = 71 then some localCycle00071 else none) else (if id < 73 then (if id = 72 then some localCycle00072 else none) else (if id = 73 then some localCycle00073 else none))))) else (if id < 79 then (if id < 76 then (if id < 75 then (if id = 74 then some localCycle00074 else none) else (if id = 75 then some localCycle00075 else none)) else (if id < 77 then (if id = 76 then some localCycle00076 else none) else (if id < 78 then (if id = 77 then some localCycle00077 else none) else (if id = 78 then some localCycle00078 else none)))) else (if id < 82 then (if id < 80 then (if id = 79 then some localCycle00079 else none) else (if id < 81 then (if id = 80 then some localCycle00080 else none) else (if id = 81 then some localCycle00081 else none))) else (if id < 83 then (if id = 82 then some localCycle00082 else none) else (if id < 84 then (if id = 83 then some localCycle00083 else none) else (if id = 84 then some localCycle00084 else none)))))))) else (if id < 128 then (if id < 106 then (if id < 95 then (if id < 90 then (if id < 87 then (if id < 86 then (if id = 85 then some localCycle00085 else none) else (if id = 86 then some localCycle00086 else none)) else (if id < 88 then (if id = 87 then some localCycle00087 else none) else (if id < 89 then (if id = 88 then some localCycle00088 else none) else (if id = 89 then some localCycle00089 else none)))) else (if id < 92 then (if id < 91 then (if id = 90 then some localCycle00090 else none) else (if id = 91 then some localCycle00091 else none)) else (if id < 93 then (if id = 92 then some localCycle00092 else none) else (if id < 94 then (if id = 93 then some localCycle00093 else none) else (if id = 94 then some localCycle00094 else none))))) else (if id < 100 then (if id < 97 then (if id < 96 then (if id = 95 then some localCycle00095 else none) else (if id = 96 then some localCycle00096 else none)) else (if id < 98 then (if id = 97 then some localCycle00097 else none) else (if id < 99 then (if id = 98 then some localCycle00098 else none) else (if id = 99 then some localCycle00099 else none)))) else (if id < 103 then (if id < 101 then (if id = 100 then some localCycle00100 else none) else (if id < 102 then (if id = 101 then some localCycle00101 else none) else (if id = 102 then some localCycle00102 else none))) else (if id < 104 then (if id = 103 then some localCycle00103 else none) else (if id < 105 then (if id = 104 then some localCycle00104 else none) else (if id = 105 then some localCycle00105 else none)))))) else (if id < 117 then (if id < 111 then (if id < 108 then (if id < 107 then (if id = 106 then some localCycle00106 else none) else (if id = 107 then some localCycle00107 else none)) else (if id < 109 then (if id = 108 then some localCycle00108 else none) else (if id < 110 then (if id = 109 then some localCycle00109 else none) else (if id = 110 then some localCycle00110 else none)))) else (if id < 114 then (if id < 112 then (if id = 111 then some localCycle00111 else none) else (if id < 113 then (if id = 112 then some localCycle00112 else none) else (if id = 113 then some localCycle00113 else none))) else (if id < 115 then (if id = 114 then some localCycle00114 else none) else (if id < 116 then (if id = 115 then some localCycle00115 else none) else (if id = 116 then some localCycle00116 else none))))) else (if id < 122 then (if id < 119 then (if id < 118 then (if id = 117 then some localCycle00117 else none) else (if id = 118 then some localCycle00118 else none)) else (if id < 120 then (if id = 119 then some localCycle00119 else none) else (if id < 121 then (if id = 120 then some localCycle00120 else none) else (if id = 121 then some localCycle00121 else none)))) else (if id < 125 then (if id < 123 then (if id = 122 then some localCycle00122 else none) else (if id < 124 then (if id = 123 then some localCycle00123 else none) else (if id = 124 then some localCycle00124 else none))) else (if id < 126 then (if id = 125 then some localCycle00125 else none) else (if id < 127 then (if id = 126 then some localCycle00126 else none) else (if id = 127 then some localCycle00127 else none))))))) else (if id < 149 then (if id < 138 then (if id < 133 then (if id < 130 then (if id < 129 then (if id = 128 then some localCycle00128 else none) else (if id = 129 then some localCycle00129 else none)) else (if id < 131 then (if id = 130 then some localCycle00130 else none) else (if id < 132 then (if id = 131 then some localCycle00131 else none) else (if id = 132 then some localCycle00132 else none)))) else (if id < 135 then (if id < 134 then (if id = 133 then some localCycle00133 else none) else (if id = 134 then some localCycle00134 else none)) else (if id < 136 then (if id = 135 then some localCycle00135 else none) else (if id < 137 then (if id = 136 then some localCycle00136 else none) else (if id = 137 then some localCycle00137 else none))))) else (if id < 143 then (if id < 140 then (if id < 139 then (if id = 138 then some localCycle00138 else none) else (if id = 139 then some localCycle00139 else none)) else (if id < 141 then (if id = 140 then some localCycle00140 else none) else (if id < 142 then (if id = 141 then some localCycle00141 else none) else (if id = 142 then some localCycle00142 else none)))) else (if id < 146 then (if id < 144 then (if id = 143 then some localCycle00143 else none) else (if id < 145 then (if id = 144 then some localCycle00144 else none) else (if id = 145 then some localCycle00145 else none))) else (if id < 147 then (if id = 146 then some localCycle00146 else none) else (if id < 148 then (if id = 147 then some localCycle00147 else none) else (if id = 148 then some localCycle00148 else none)))))) else (if id < 160 then (if id < 154 then (if id < 151 then (if id < 150 then (if id = 149 then some localCycle00149 else none) else (if id = 150 then some localCycle00150 else none)) else (if id < 152 then (if id = 151 then some localCycle00151 else none) else (if id < 153 then (if id = 152 then some localCycle00152 else none) else (if id = 153 then some localCycle00153 else none)))) else (if id < 157 then (if id < 155 then (if id = 154 then some localCycle00154 else none) else (if id < 156 then (if id = 155 then some localCycle00155 else none) else (if id = 156 then some localCycle00156 else none))) else (if id < 158 then (if id = 157 then some localCycle00157 else none) else (if id < 159 then (if id = 158 then some localCycle00158 else none) else (if id = 159 then some localCycle00159 else none))))) else (if id < 165 then (if id < 162 then (if id < 161 then (if id = 160 then some localCycle00160 else none) else (if id = 161 then some localCycle00161 else none)) else (if id < 163 then (if id = 162 then some localCycle00162 else none) else (if id < 164 then (if id = 163 then some localCycle00163 else none) else (if id = 164 then some localCycle00164 else none)))) else (if id < 168 then (if id < 166 then (if id = 165 then some localCycle00165 else none) else (if id < 167 then (if id = 166 then some localCycle00166 else none) else (if id = 167 then some localCycle00167 else none))) else (if id < 169 then (if id = 168 then some localCycle00168 else none) else (if id < 170 then (if id = 169 then some localCycle00169 else none) else (if id = 170 then some localCycle00170 else none))))))))) else (if id < 257 then (if id < 214 then (if id < 192 then (if id < 181 then (if id < 176 then (if id < 173 then (if id < 172 then (if id = 171 then some localCycle00171 else none) else (if id = 172 then some localCycle00172 else none)) else (if id < 174 then (if id = 173 then some localCycle00173 else none) else (if id < 175 then (if id = 174 then some localCycle00174 else none) else (if id = 175 then some localCycle00175 else none)))) else (if id < 178 then (if id < 177 then (if id = 176 then some localCycle00176 else none) else (if id = 177 then some localCycle00177 else none)) else (if id < 179 then (if id = 178 then some localCycle00178 else none) else (if id < 180 then (if id = 179 then some localCycle00179 else none) else (if id = 180 then some localCycle00180 else none))))) else (if id < 186 then (if id < 183 then (if id < 182 then (if id = 181 then some localCycle00181 else none) else (if id = 182 then some localCycle00182 else none)) else (if id < 184 then (if id = 183 then some localCycle00183 else none) else (if id < 185 then (if id = 184 then some localCycle00184 else none) else (if id = 185 then some localCycle00185 else none)))) else (if id < 189 then (if id < 187 then (if id = 186 then some localCycle00186 else none) else (if id < 188 then (if id = 187 then some localCycle00187 else none) else (if id = 188 then some localCycle00188 else none))) else (if id < 190 then (if id = 189 then some localCycle00189 else none) else (if id < 191 then (if id = 190 then some localCycle00190 else none) else (if id = 191 then some localCycle00191 else none)))))) else (if id < 203 then (if id < 197 then (if id < 194 then (if id < 193 then (if id = 192 then some localCycle00192 else none) else (if id = 193 then some localCycle00193 else none)) else (if id < 195 then (if id = 194 then some localCycle00194 else none) else (if id < 196 then (if id = 195 then some localCycle00195 else none) else (if id = 196 then some localCycle00196 else none)))) else (if id < 200 then (if id < 198 then (if id = 197 then some localCycle00197 else none) else (if id < 199 then (if id = 198 then some localCycle00198 else none) else (if id = 199 then some localCycle00199 else none))) else (if id < 201 then (if id = 200 then some localCycle00200 else none) else (if id < 202 then (if id = 201 then some localCycle00201 else none) else (if id = 202 then some localCycle00202 else none))))) else (if id < 208 then (if id < 205 then (if id < 204 then (if id = 203 then some localCycle00203 else none) else (if id = 204 then some localCycle00204 else none)) else (if id < 206 then (if id = 205 then some localCycle00205 else none) else (if id < 207 then (if id = 206 then some localCycle00206 else none) else (if id = 207 then some localCycle00207 else none)))) else (if id < 211 then (if id < 209 then (if id = 208 then some localCycle00208 else none) else (if id < 210 then (if id = 209 then some localCycle00209 else none) else (if id = 210 then some localCycle00210 else none))) else (if id < 212 then (if id = 211 then some localCycle00211 else none) else (if id < 213 then (if id = 212 then some localCycle00212 else none) else (if id = 213 then some localCycle00213 else none))))))) else (if id < 235 then (if id < 224 then (if id < 219 then (if id < 216 then (if id < 215 then (if id = 214 then some localCycle00214 else none) else (if id = 215 then some localCycle00215 else none)) else (if id < 217 then (if id = 216 then some localCycle00216 else none) else (if id < 218 then (if id = 217 then some localCycle00217 else none) else (if id = 218 then some localCycle00218 else none)))) else (if id < 221 then (if id < 220 then (if id = 219 then some localCycle00219 else none) else (if id = 220 then some localCycle00220 else none)) else (if id < 222 then (if id = 221 then some localCycle00221 else none) else (if id < 223 then (if id = 222 then some localCycle00222 else none) else (if id = 223 then some localCycle00223 else none))))) else (if id < 229 then (if id < 226 then (if id < 225 then (if id = 224 then some localCycle00224 else none) else (if id = 225 then some localCycle00225 else none)) else (if id < 227 then (if id = 226 then some localCycle00226 else none) else (if id < 228 then (if id = 227 then some localCycle00227 else none) else (if id = 228 then some localCycle00228 else none)))) else (if id < 232 then (if id < 230 then (if id = 229 then some localCycle00229 else none) else (if id < 231 then (if id = 230 then some localCycle00230 else none) else (if id = 231 then some localCycle00231 else none))) else (if id < 233 then (if id = 232 then some localCycle00232 else none) else (if id < 234 then (if id = 233 then some localCycle00233 else none) else (if id = 234 then some localCycle00234 else none)))))) else (if id < 246 then (if id < 240 then (if id < 237 then (if id < 236 then (if id = 235 then some localCycle00235 else none) else (if id = 236 then some localCycle00236 else none)) else (if id < 238 then (if id = 237 then some localCycle00237 else none) else (if id < 239 then (if id = 238 then some localCycle00238 else none) else (if id = 239 then some localCycle00239 else none)))) else (if id < 243 then (if id < 241 then (if id = 240 then some localCycle00240 else none) else (if id < 242 then (if id = 241 then some localCycle00241 else none) else (if id = 242 then some localCycle00242 else none))) else (if id < 244 then (if id = 243 then some localCycle00243 else none) else (if id < 245 then (if id = 244 then some localCycle00244 else none) else (if id = 245 then some localCycle00245 else none))))) else (if id < 251 then (if id < 248 then (if id < 247 then (if id = 246 then some localCycle00246 else none) else (if id = 247 then some localCycle00247 else none)) else (if id < 249 then (if id = 248 then some localCycle00248 else none) else (if id < 250 then (if id = 249 then some localCycle00249 else none) else (if id = 250 then some localCycle00250 else none)))) else (if id < 254 then (if id < 252 then (if id = 251 then some localCycle00251 else none) else (if id < 253 then (if id = 252 then some localCycle00252 else none) else (if id = 253 then some localCycle00253 else none))) else (if id < 255 then (if id = 254 then some localCycle00254 else none) else (if id < 256 then (if id = 255 then some localCycle00255 else none) else (if id = 256 then some localCycle00256 else none)))))))) else (if id < 300 then (if id < 278 then (if id < 267 then (if id < 262 then (if id < 259 then (if id < 258 then (if id = 257 then some localCycle00257 else none) else (if id = 258 then some localCycle00258 else none)) else (if id < 260 then (if id = 259 then some localCycle00259 else none) else (if id < 261 then (if id = 260 then some localCycle00260 else none) else (if id = 261 then some localCycle00261 else none)))) else (if id < 264 then (if id < 263 then (if id = 262 then some localCycle00262 else none) else (if id = 263 then some localCycle00263 else none)) else (if id < 265 then (if id = 264 then some localCycle00264 else none) else (if id < 266 then (if id = 265 then some localCycle00265 else none) else (if id = 266 then some localCycle00266 else none))))) else (if id < 272 then (if id < 269 then (if id < 268 then (if id = 267 then some localCycle00267 else none) else (if id = 268 then some localCycle00268 else none)) else (if id < 270 then (if id = 269 then some localCycle00269 else none) else (if id < 271 then (if id = 270 then some localCycle00270 else none) else (if id = 271 then some localCycle00271 else none)))) else (if id < 275 then (if id < 273 then (if id = 272 then some localCycle00272 else none) else (if id < 274 then (if id = 273 then some localCycle00273 else none) else (if id = 274 then some localCycle00274 else none))) else (if id < 276 then (if id = 275 then some localCycle00275 else none) else (if id < 277 then (if id = 276 then some localCycle00276 else none) else (if id = 277 then some localCycle00277 else none)))))) else (if id < 289 then (if id < 283 then (if id < 280 then (if id < 279 then (if id = 278 then some localCycle00278 else none) else (if id = 279 then some localCycle00279 else none)) else (if id < 281 then (if id = 280 then some localCycle00280 else none) else (if id < 282 then (if id = 281 then some localCycle00281 else none) else (if id = 282 then some localCycle00282 else none)))) else (if id < 286 then (if id < 284 then (if id = 283 then some localCycle00283 else none) else (if id < 285 then (if id = 284 then some localCycle00284 else none) else (if id = 285 then some localCycle00285 else none))) else (if id < 287 then (if id = 286 then some localCycle00286 else none) else (if id < 288 then (if id = 287 then some localCycle00287 else none) else (if id = 288 then some localCycle00288 else none))))) else (if id < 294 then (if id < 291 then (if id < 290 then (if id = 289 then some localCycle00289 else none) else (if id = 290 then some localCycle00290 else none)) else (if id < 292 then (if id = 291 then some localCycle00291 else none) else (if id < 293 then (if id = 292 then some localCycle00292 else none) else (if id = 293 then some localCycle00293 else none)))) else (if id < 297 then (if id < 295 then (if id = 294 then some localCycle00294 else none) else (if id < 296 then (if id = 295 then some localCycle00295 else none) else (if id = 296 then some localCycle00296 else none))) else (if id < 298 then (if id = 297 then some localCycle00297 else none) else (if id < 299 then (if id = 298 then some localCycle00298 else none) else (if id = 299 then some localCycle00299 else none))))))) else (if id < 321 then (if id < 310 then (if id < 305 then (if id < 302 then (if id < 301 then (if id = 300 then some localCycle00300 else none) else (if id = 301 then some localCycle00301 else none)) else (if id < 303 then (if id = 302 then some localCycle00302 else none) else (if id < 304 then (if id = 303 then some localCycle00303 else none) else (if id = 304 then some localCycle00304 else none)))) else (if id < 307 then (if id < 306 then (if id = 305 then some localCycle00305 else none) else (if id = 306 then some localCycle00306 else none)) else (if id < 308 then (if id = 307 then some localCycle00307 else none) else (if id < 309 then (if id = 308 then some localCycle00308 else none) else (if id = 309 then some localCycle00309 else none))))) else (if id < 315 then (if id < 312 then (if id < 311 then (if id = 310 then some localCycle00310 else none) else (if id = 311 then some localCycle00311 else none)) else (if id < 313 then (if id = 312 then some localCycle00312 else none) else (if id < 314 then (if id = 313 then some localCycle00313 else none) else (if id = 314 then some localCycle00314 else none)))) else (if id < 318 then (if id < 316 then (if id = 315 then some localCycle00315 else none) else (if id < 317 then (if id = 316 then some localCycle00316 else none) else (if id = 317 then some localCycle00317 else none))) else (if id < 319 then (if id = 318 then some localCycle00318 else none) else (if id < 320 then (if id = 319 then some localCycle00319 else none) else (if id = 320 then some localCycle00320 else none)))))) else (if id < 332 then (if id < 326 then (if id < 323 then (if id < 322 then (if id = 321 then some localCycle00321 else none) else (if id = 322 then some localCycle00322 else none)) else (if id < 324 then (if id = 323 then some localCycle00323 else none) else (if id < 325 then (if id = 324 then some localCycle00324 else none) else (if id = 325 then some localCycle00325 else none)))) else (if id < 329 then (if id < 327 then (if id = 326 then some localCycle00326 else none) else (if id < 328 then (if id = 327 then some localCycle00327 else none) else (if id = 328 then some localCycle00328 else none))) else (if id < 330 then (if id = 329 then some localCycle00329 else none) else (if id < 331 then (if id = 330 then some localCycle00330 else none) else (if id = 331 then some localCycle00331 else none))))) else (if id < 337 then (if id < 334 then (if id < 333 then (if id = 332 then some localCycle00332 else none) else (if id = 333 then some localCycle00333 else none)) else (if id < 335 then (if id = 334 then some localCycle00334 else none) else (if id < 336 then (if id = 335 then some localCycle00335 else none) else (if id = 336 then some localCycle00336 else none)))) else (if id < 340 then (if id < 338 then (if id = 337 then some localCycle00337 else none) else (if id < 339 then (if id = 338 then some localCycle00338 else none) else (if id = 339 then some localCycle00339 else none))) else (if id < 341 then (if id = 340 then some localCycle00340 else none) else (if id < 342 then (if id = 341 then some localCycle00341 else none) else (if id = 342 then some localCycle00342 else none)))))))))

def namedLeaf000 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 2, 3, 5, 6, 4], ![0, 1, 6, 5, 4, 3], ![0, 1, 5, 6, 4, 2], ![0, 5, 6, 1, 3, 2], ![0, 4, 1, 3, 6, 2], ![0, 4, 1, 3, 5, 2]], proof := .tail 72 }

theorem namedLeaf000_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 128)) namedLeaf000 = true :=
  by decide +kernel

def namedLeaf001 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 2, 3, 5, 6, 4], ![0, 1, 6, 5, 4, 3], ![0, 1, 6, 5, 4, 2], ![0, 5, 6, 1, 3, 2], ![0, 4, 1, 6, 3, 2], ![0, 4, 1, 5, 3, 2]], proof := .tail 269 }

theorem namedLeaf001_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 129)) namedLeaf001 = true :=
  by decide +kernel

def namedLeaf002 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 2, 3, 6, 5, 4], ![0, 1, 6, 5, 4, 3], ![0, 1, 6, 5, 4, 2], ![0, 5, 6, 1, 3, 2], ![0, 4, 6, 1, 3, 2], ![0, 4, 5, 1, 3, 2]], proof := .tail 269 }

theorem namedLeaf002_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 130)) namedLeaf002 = true :=
  by decide +kernel

def namedLeaf003 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 2, 3, 6, 5, 4], ![0, 1, 6, 5, 4, 3], ![0, 1, 6, 5, 4, 2], ![0, 6, 5, 1, 3, 2], ![0, 6, 4, 1, 3, 2], ![0, 5, 4, 1, 3, 2]], proof := .tail 181 }

theorem namedLeaf003_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 131)) namedLeaf003 = true :=
  by decide +kernel

def namedLeaf004 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 2, 6, 3, 4, 5], ![0, 1, 6, 3, 4, 5], ![0, 6, 1, 2, 4, 5], ![0, 6, 1, 2, 3, 5], ![0, 6, 1, 2, 3, 4], ![0, 5, 4, 3, 1, 2]], proof := .tail 284 }

theorem namedLeaf004_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 132)) namedLeaf004 = true :=
  by decide +kernel

def namedLeaf005 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 2, 6, 3, 4, 5], ![0, 1, 6, 3, 4, 5], ![0, 6, 1, 2, 5, 4], ![0, 6, 1, 2, 5, 3], ![0, 6, 1, 2, 4, 3], ![0, 5, 4, 3, 1, 2]], proof := .tail 253 }

theorem namedLeaf005_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 133)) namedLeaf005 = true :=
  by decide +kernel

def namedLeaf006 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 2, 6, 3, 4, 5], ![0, 1, 6, 3, 5, 4], ![0, 6, 1, 2, 5, 4], ![0, 6, 1, 5, 2, 3], ![0, 6, 1, 4, 2, 3], ![0, 5, 4, 3, 1, 2]], proof := .tail 233 }

theorem namedLeaf006_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 134)) namedLeaf006 = true :=
  by decide +kernel

def namedLeaf007 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 2, 6, 3, 4, 5], ![0, 1, 6, 5, 3, 4], ![0, 6, 1, 5, 2, 4], ![0, 6, 1, 5, 2, 3], ![0, 6, 1, 4, 3, 2], ![0, 5, 4, 3, 1, 2]], proof := .tail 180 }

theorem namedLeaf007_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 135)) namedLeaf007 = true :=
  by decide +kernel

def namedLeaf008 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 2, 6, 3, 4, 5], ![0, 1, 6, 4, 3, 5], ![0, 6, 1, 4, 2, 5], ![0, 6, 1, 3, 2, 5], ![0, 6, 1, 2, 3, 4], ![0, 5, 4, 3, 1, 2]], proof := .tail 308 }

theorem namedLeaf008_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 136)) namedLeaf008 = true :=
  by decide +kernel

def namedLeaf009 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 2, 6, 3, 4, 5], ![0, 1, 6, 4, 5, 3], ![0, 6, 1, 4, 5, 2], ![0, 6, 1, 3, 2, 5], ![0, 6, 1, 3, 2, 4], ![0, 5, 4, 3, 1, 2]], proof := .tail 246 }

theorem namedLeaf009_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 137)) namedLeaf009 = true :=
  by decide +kernel

def namedLeaf010 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 2, 6, 3, 4, 5], ![0, 1, 6, 5, 4, 3], ![0, 6, 1, 4, 5, 2], ![0, 6, 1, 3, 5, 2], ![0, 6, 1, 3, 4, 2], ![0, 5, 4, 3, 1, 2]], proof := .tail 249 }

theorem namedLeaf010_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 138)) namedLeaf010 = true :=
  by decide +kernel

def namedLeaf011 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 2, 6, 3, 4, 5], ![0, 1, 6, 5, 4, 3], ![0, 6, 1, 5, 4, 2], ![0, 6, 1, 5, 3, 2], ![0, 6, 1, 4, 3, 2], ![0, 5, 4, 3, 1, 2]], proof := .tail 255 }

theorem namedLeaf011_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 139)) namedLeaf011 = true :=
  by decide +kernel

def namedLeaf012 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 2, 6, 3, 5, 4], ![0, 1, 6, 3, 5, 4], ![0, 6, 1, 2, 5, 4], ![0, 5, 6, 1, 2, 3], ![0, 4, 6, 1, 2, 3], ![0, 4, 5, 3, 1, 2]], proof := .tail 213 }

theorem namedLeaf012_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 140)) namedLeaf012 = true :=
  by decide +kernel

def namedLeaf013 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 2, 6, 3, 5, 4], ![0, 1, 6, 5, 3, 4], ![0, 6, 1, 5, 2, 4], ![0, 5, 6, 1, 2, 3], ![0, 4, 6, 1, 3, 2], ![0, 4, 5, 3, 1, 2]], proof := .tail 115 }

theorem namedLeaf013_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 141)) namedLeaf013 = true :=
  by decide +kernel

def namedLeaf014 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 2, 6, 3, 5, 4], ![0, 1, 6, 5, 4, 3], ![0, 6, 1, 5, 4, 2], ![0, 5, 6, 1, 3, 2], ![0, 4, 6, 1, 3, 2], ![0, 4, 5, 3, 1, 2]], proof := .tail 140 }

theorem namedLeaf014_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 142)) namedLeaf014 = true :=
  by decide +kernel

def namedLeaf015 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 2, 6, 3, 5, 4], ![0, 1, 6, 3, 5, 4], ![0, 6, 1, 2, 5, 4], ![0, 6, 5, 1, 2, 3], ![0, 6, 4, 1, 2, 3], ![0, 5, 4, 3, 1, 2]], proof := .tail 147 }

theorem namedLeaf015_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 143)) namedLeaf015 = true :=
  by decide +kernel

def namedLeaf016 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 2, 6, 3, 5, 4], ![0, 1, 6, 5, 3, 4], ![0, 6, 1, 5, 2, 4], ![0, 6, 5, 1, 2, 3], ![0, 6, 4, 1, 3, 2], ![0, 5, 4, 3, 1, 2]], proof := .tail 79 }

theorem namedLeaf016_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 144)) namedLeaf016 = true :=
  by decide +kernel

def namedLeaf017 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 2, 6, 3, 5, 4], ![0, 1, 6, 5, 4, 3], ![0, 6, 1, 5, 4, 2], ![0, 6, 5, 1, 3, 2], ![0, 6, 4, 1, 3, 2], ![0, 5, 4, 3, 1, 2]], proof := .tail 237 }

theorem namedLeaf017_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 145)) namedLeaf017 = true :=
  by decide +kernel

def namedLeaf018 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 2, 5, 3, 4, 6], ![0, 1, 5, 3, 4, 6], ![0, 5, 1, 2, 4, 6], ![0, 5, 1, 2, 3, 6], ![0, 4, 3, 1, 2, 6], ![0, 1, 2, 3, 4, 5]], proof := .tail 200 }

theorem namedLeaf018_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 146)) namedLeaf018 = true :=
  by decide +kernel

def namedLeaf019 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 2, 5, 3, 4, 6], ![0, 1, 5, 3, 4, 6], ![0, 5, 1, 2, 6, 4], ![0, 5, 1, 2, 6, 3], ![0, 4, 3, 1, 2, 6], ![0, 1, 2, 4, 3, 5]], proof := .tail 145 }

theorem namedLeaf019_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 147)) namedLeaf019 = true :=
  by decide +kernel

def namedLeaf020 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 2, 5, 3, 4, 6], ![0, 1, 5, 3, 6, 4], ![0, 5, 1, 2, 6, 4], ![0, 5, 1, 6, 2, 3], ![0, 4, 3, 1, 2, 6], ![0, 1, 4, 2, 3, 5]], proof := .tail 188 }

theorem namedLeaf020_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 148)) namedLeaf020 = true :=
  by decide +kernel

def namedLeaf021 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 2, 5, 3, 4, 6], ![0, 1, 5, 6, 3, 4], ![0, 5, 1, 6, 2, 4], ![0, 5, 1, 6, 2, 3], ![0, 4, 3, 1, 2, 6], ![0, 1, 4, 3, 2, 5]], proof := .tail 182 }

theorem namedLeaf021_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 149)) namedLeaf021 = true :=
  by decide +kernel

def namedLeaf022 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 2, 5, 3, 4, 6], ![0, 1, 6, 5, 3, 4], ![0, 5, 1, 6, 2, 4], ![0, 5, 1, 6, 2, 3], ![0, 4, 3, 1, 6, 2], ![0, 1, 4, 3, 5, 2]], proof := .tail 37 }

theorem namedLeaf022_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 150)) namedLeaf022 = true :=
  by decide +kernel

def namedLeaf023 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 2, 5, 3, 6, 4], ![0, 1, 5, 3, 6, 4], ![0, 5, 1, 2, 6, 4], ![0, 5, 6, 1, 2, 3], ![0, 4, 3, 1, 2, 6], ![0, 4, 1, 2, 3, 5]], proof := .low (![95, 306, 135, 155, 117, 211, 128, 321, 137, 73, 130, 55, 298, 91, 215, 49, 310, 142, 220, 3, 86, 297, 157, 294, 311, 33, 47, 132]) }

theorem namedLeaf023_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 151)) namedLeaf023 = true :=
  by decide +kernel

def namedLeaf024 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 2, 5, 3, 6, 4], ![0, 1, 5, 6, 3, 4], ![0, 5, 1, 6, 2, 4], ![0, 5, 6, 1, 2, 3], ![0, 4, 3, 1, 2, 6], ![0, 4, 1, 3, 2, 5]], proof := .tail 266 }

theorem namedLeaf024_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 152)) namedLeaf024 = true :=
  by decide +kernel

def namedLeaf025 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 2, 5, 3, 6, 4], ![0, 1, 6, 5, 3, 4], ![0, 5, 1, 6, 2, 4], ![0, 5, 6, 1, 2, 3], ![0, 4, 3, 1, 6, 2], ![0, 4, 1, 3, 5, 2]], proof := .tail 37 }

theorem namedLeaf025_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 153)) namedLeaf025 = true :=
  by decide +kernel

def namedLeaf026 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 2, 5, 6, 3, 4], ![0, 1, 5, 6, 3, 4], ![0, 5, 6, 1, 2, 4], ![0, 5, 6, 1, 2, 3], ![0, 4, 3, 1, 2, 6], ![0, 4, 3, 1, 2, 5]], proof := .low (![225, 152, 135, 14, 172, 12, 28, 323, 159, 243, 6, 207, 19, 45, 105, 149, 207, 324, 59, 9, 207, 277, 327, 207, 214, 207, 212, 207]) }

theorem namedLeaf026_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 154)) namedLeaf026 = true :=
  by decide +kernel

def namedLeaf027 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 2, 5, 6, 3, 4], ![0, 1, 6, 5, 3, 4], ![0, 5, 6, 1, 2, 4], ![0, 5, 6, 1, 2, 3], ![0, 4, 3, 1, 6, 2], ![0, 4, 3, 1, 5, 2]], proof := .tail 34 }

theorem namedLeaf027_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 155)) namedLeaf027 = true :=
  by decide +kernel

def namedLeaf028 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 2, 6, 5, 3, 4], ![0, 1, 6, 5, 3, 4], ![0, 5, 6, 1, 2, 4], ![0, 5, 6, 1, 2, 3], ![0, 4, 3, 6, 1, 2], ![0, 4, 3, 5, 1, 2]], proof := .tail 48 }

theorem namedLeaf028_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 156)) namedLeaf028 = true :=
  by decide +kernel

def namedLeaf029 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 2, 6, 5, 3, 4], ![0, 1, 6, 5, 3, 4], ![0, 6, 5, 1, 2, 4], ![0, 5, 6, 1, 2, 3], ![0, 4, 6, 3, 1, 2], ![0, 4, 5, 3, 1, 2]], proof := .tail 58 }

theorem namedLeaf029_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 157)) namedLeaf029 = true :=
  by decide +kernel

def namedLeaf030 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 2, 6, 5, 3, 4], ![0, 1, 6, 5, 3, 4], ![0, 6, 5, 1, 2, 4], ![0, 6, 5, 1, 2, 3], ![0, 6, 4, 3, 1, 2], ![0, 5, 4, 3, 1, 2]], proof := .tail 335 }

theorem namedLeaf030_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 158)) namedLeaf030 = true :=
  by decide +kernel

def namedLeaf031 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 2, 5, 3, 4, 6], ![0, 1, 5, 4, 3, 6], ![0, 5, 1, 4, 2, 6], ![0, 5, 1, 3, 2, 6], ![0, 4, 3, 1, 2, 6], ![0, 1, 2, 3, 4, 5]], proof := .tail 122 }

theorem namedLeaf031_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 159)) namedLeaf031 = true :=
  by decide +kernel

def namedLeaf032 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 2, 5, 3, 4, 6], ![0, 1, 5, 4, 6, 3], ![0, 5, 1, 4, 6, 2], ![0, 5, 1, 3, 2, 6], ![0, 4, 3, 1, 2, 6], ![0, 1, 3, 2, 4, 5]], proof := .tail 67 }

theorem namedLeaf032_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 160)) namedLeaf032 = true :=
  by decide +kernel

def namedLeaf033 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 2, 5, 3, 4, 6], ![0, 1, 5, 6, 4, 3], ![0, 5, 1, 4, 6, 2], ![0, 5, 1, 3, 6, 2], ![0, 4, 3, 1, 2, 6], ![0, 1, 3, 4, 2, 5]], proof := .tail 74 }

theorem namedLeaf033_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 161)) namedLeaf033 = true :=
  by decide +kernel

def namedLeaf034 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 2, 5, 3, 4, 6], ![0, 1, 5, 6, 4, 3], ![0, 5, 1, 6, 4, 2], ![0, 5, 1, 6, 3, 2], ![0, 4, 3, 1, 2, 6], ![0, 1, 4, 3, 2, 5]], proof := .tail 260 }

theorem namedLeaf034_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 162)) namedLeaf034 = true :=
  by decide +kernel

def namedLeaf035 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 2, 5, 3, 4, 6], ![0, 1, 6, 5, 4, 3], ![0, 5, 1, 4, 6, 2], ![0, 5, 1, 3, 6, 2], ![0, 4, 3, 1, 6, 2], ![0, 1, 3, 4, 5, 2]], proof := .tail 187 }

theorem namedLeaf035_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 163)) namedLeaf035 = true :=
  by decide +kernel

def namedLeaf036 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 2, 5, 3, 4, 6], ![0, 1, 6, 5, 4, 3], ![0, 5, 1, 6, 4, 2], ![0, 5, 1, 6, 3, 2], ![0, 4, 3, 1, 6, 2], ![0, 1, 4, 3, 5, 2]], proof := .tail 260 }

theorem namedLeaf036_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 164)) namedLeaf036 = true :=
  by decide +kernel

def namedLeaf037 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 2, 5, 3, 6, 4], ![0, 1, 5, 6, 4, 3], ![0, 5, 1, 6, 4, 2], ![0, 5, 6, 1, 3, 2], ![0, 4, 3, 1, 2, 6], ![0, 4, 1, 3, 2, 5]], proof := .tail 66 }

theorem namedLeaf037_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 165)) namedLeaf037 = true :=
  by decide +kernel

def namedLeaf038 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 2, 5, 3, 6, 4], ![0, 1, 6, 5, 4, 3], ![0, 5, 1, 6, 4, 2], ![0, 5, 6, 1, 3, 2], ![0, 4, 3, 1, 6, 2], ![0, 4, 1, 3, 5, 2]], proof := .tail 196 }

theorem namedLeaf038_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 166)) namedLeaf038 = true :=
  by decide +kernel

def namedLeaf039 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 2, 5, 6, 3, 4], ![0, 1, 5, 6, 4, 3], ![0, 5, 6, 1, 4, 2], ![0, 5, 6, 1, 3, 2], ![0, 4, 3, 1, 2, 6], ![0, 4, 3, 1, 2, 5]], proof := .tail 299 }

theorem namedLeaf039_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 167)) namedLeaf039 = true :=
  by decide +kernel

def namedLeaf040 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 2, 5, 6, 3, 4], ![0, 1, 6, 5, 4, 3], ![0, 5, 6, 1, 4, 2], ![0, 5, 6, 1, 3, 2], ![0, 4, 3, 1, 6, 2], ![0, 4, 3, 1, 5, 2]], proof := .tail 299 }

theorem namedLeaf040_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 168)) namedLeaf040 = true :=
  by decide +kernel

def namedLeaf041 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 2, 6, 5, 3, 4], ![0, 1, 6, 5, 4, 3], ![0, 5, 6, 1, 4, 2], ![0, 5, 6, 1, 3, 2], ![0, 4, 3, 6, 1, 2], ![0, 4, 3, 5, 1, 2]], proof := .tail 167 }

theorem namedLeaf041_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 169)) namedLeaf041 = true :=
  by decide +kernel

def namedLeaf042 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 2, 6, 5, 3, 4], ![0, 1, 6, 5, 4, 3], ![0, 6, 5, 1, 4, 2], ![0, 5, 6, 1, 3, 2], ![0, 4, 6, 3, 1, 2], ![0, 4, 5, 3, 1, 2]], proof := .tail 228 }

theorem namedLeaf042_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 170)) namedLeaf042 = true :=
  by decide +kernel

def namedLeaf043 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 2, 6, 5, 3, 4], ![0, 1, 6, 5, 4, 3], ![0, 6, 5, 1, 4, 2], ![0, 6, 5, 1, 3, 2], ![0, 6, 4, 3, 1, 2], ![0, 5, 4, 3, 1, 2]], proof := .tail 23 }

theorem namedLeaf043_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 171)) namedLeaf043 = true :=
  by decide +kernel

def namedLeaf044 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 2, 4, 3, 5, 6], ![0, 1, 4, 3, 5, 6], ![0, 4, 1, 2, 5, 6], ![0, 3, 1, 2, 5, 6], ![0, 1, 2, 3, 4, 6], ![0, 1, 2, 3, 4, 5]], proof := .tail 191 }

theorem namedLeaf044_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 172)) namedLeaf044 = true :=
  by decide +kernel

def namedLeaf045 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 2, 4, 3, 5, 6], ![0, 1, 4, 3, 5, 6], ![0, 4, 1, 2, 5, 6], ![0, 3, 1, 2, 6, 5], ![0, 1, 2, 3, 6, 4], ![0, 1, 2, 3, 5, 4]], proof := .tail 338 }

theorem namedLeaf045_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 173)) namedLeaf045 = true :=
  by decide +kernel

def namedLeaf046 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 2, 4, 3, 5, 6], ![0, 1, 4, 3, 5, 6], ![0, 4, 1, 2, 6, 5], ![0, 3, 1, 2, 6, 5], ![0, 1, 2, 6, 3, 4], ![0, 1, 2, 5, 3, 4]], proof := .tail 267 }

theorem namedLeaf046_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 174)) namedLeaf046 = true :=
  by decide +kernel

def namedLeaf047 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 2, 4, 3, 5, 6], ![0, 1, 4, 3, 6, 5], ![0, 4, 1, 2, 6, 5], ![0, 3, 1, 2, 6, 5], ![0, 1, 6, 2, 3, 4], ![0, 1, 5, 2, 3, 4]], proof := .tail 129 }

theorem namedLeaf047_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 175)) namedLeaf047 = true :=
  by decide +kernel

def namedLeaf048 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 2, 4, 3, 5, 6], ![0, 1, 4, 6, 3, 5], ![0, 4, 1, 6, 2, 5], ![0, 3, 1, 2, 6, 5], ![0, 1, 6, 2, 3, 4], ![0, 1, 5, 3, 2, 4]], proof := .tail 139 }

theorem namedLeaf048_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 176)) namedLeaf048 = true :=
  by decide +kernel

def namedLeaf049 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 2, 4, 3, 5, 6], ![0, 1, 6, 4, 3, 5], ![0, 4, 1, 6, 2, 5], ![0, 3, 1, 6, 2, 5], ![0, 1, 6, 2, 3, 4], ![0, 1, 5, 3, 4, 2]], proof := .tail 104 }

theorem namedLeaf049_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 177)) namedLeaf049 = true :=
  by decide +kernel

def namedLeaf050 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 2, 4, 3, 6, 5], ![0, 1, 4, 3, 6, 5], ![0, 4, 1, 2, 6, 5], ![0, 3, 1, 2, 6, 5], ![0, 6, 1, 2, 3, 4], ![0, 5, 1, 2, 3, 4]], proof := .low (![283, 204, 103, 56, 125, 148, 329, 27, 40, 15, 83, 35, 201, 287, 8, 301, 30, 276, 7, 282, 151, 69, 312, 247, 61, 108, 177, 183]) }

theorem namedLeaf050_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 178)) namedLeaf050 = true :=
  by decide +kernel

def namedLeaf051 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 2, 4, 3, 6, 5], ![0, 1, 4, 6, 3, 5], ![0, 4, 1, 6, 2, 5], ![0, 3, 1, 2, 6, 5], ![0, 6, 1, 2, 3, 4], ![0, 5, 1, 3, 2, 4]], proof := .tail 126 }

theorem namedLeaf051_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 179)) namedLeaf051 = true :=
  by decide +kernel

def namedLeaf052 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 2, 4, 3, 6, 5], ![0, 1, 6, 4, 3, 5], ![0, 4, 1, 6, 2, 5], ![0, 3, 1, 6, 2, 5], ![0, 6, 1, 2, 3, 4], ![0, 5, 1, 3, 4, 2]], proof := .tail 162 }

theorem namedLeaf052_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 180)) namedLeaf052 = true :=
  by decide +kernel

def namedLeaf053 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 2, 4, 6, 3, 5], ![0, 1, 4, 6, 3, 5], ![0, 4, 6, 1, 2, 5], ![0, 3, 1, 2, 6, 5], ![0, 6, 1, 2, 3, 4], ![0, 5, 3, 1, 2, 4]], proof := .low (![280, 309, 103, 209, 172, 16, 195, 160, 319, 302, 189, 141, 206, 192, 111, 138, 141, 221, 102, 119, 141, 218, 285, 141, 62, 141, 315, 141]) }

theorem namedLeaf053_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 181)) namedLeaf053 = true :=
  by decide +kernel

def namedLeaf054 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 2, 4, 6, 3, 5], ![0, 1, 6, 4, 3, 5], ![0, 4, 6, 1, 2, 5], ![0, 3, 1, 6, 2, 5], ![0, 6, 1, 2, 3, 4], ![0, 5, 3, 1, 4, 2]], proof := .tail 268 }

theorem namedLeaf054_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 182)) namedLeaf054 = true :=
  by decide +kernel

def namedLeaf055 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 2, 6, 4, 3, 5], ![0, 1, 6, 4, 3, 5], ![0, 4, 6, 1, 2, 5], ![0, 3, 6, 1, 2, 5], ![0, 6, 1, 2, 3, 4], ![0, 5, 3, 4, 1, 2]], proof := .tail 216 }

theorem namedLeaf055_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 183)) namedLeaf055 = true :=
  by decide +kernel

def namedLeaf056 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 2, 6, 4, 3, 5], ![0, 1, 6, 4, 3, 5], ![0, 6, 4, 1, 2, 5], ![0, 6, 3, 1, 2, 5], ![0, 6, 1, 2, 3, 4], ![0, 5, 4, 3, 1, 2]], proof := .tail 271 }

theorem namedLeaf056_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 184)) namedLeaf056 = true :=
  by decide +kernel

def namedLeaf057 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 2, 4, 3, 5, 6], ![0, 1, 4, 5, 3, 6], ![0, 4, 1, 5, 2, 6], ![0, 3, 1, 2, 5, 6], ![0, 1, 3, 2, 4, 6], ![0, 1, 2, 3, 4, 5]], proof := .tail 85 }

theorem namedLeaf057_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 185)) namedLeaf057 = true :=
  by decide +kernel

def namedLeaf058 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 2, 4, 3, 5, 6], ![0, 1, 4, 5, 3, 6], ![0, 4, 1, 5, 2, 6], ![0, 3, 1, 2, 6, 5], ![0, 1, 3, 2, 6, 4], ![0, 1, 2, 3, 5, 4]], proof := .tail 300 }

theorem namedLeaf058_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 186)) namedLeaf058 = true :=
  by decide +kernel

def namedLeaf059 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 2, 4, 3, 5, 6], ![0, 1, 4, 5, 6, 3], ![0, 4, 1, 5, 6, 2], ![0, 3, 1, 2, 5, 6], ![0, 1, 3, 2, 4, 6], ![0, 1, 3, 2, 4, 5]], proof := .tail 245 }

theorem namedLeaf059_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 187)) namedLeaf059 = true :=
  by decide +kernel

def namedLeaf060 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 2, 4, 3, 5, 6], ![0, 1, 4, 5, 6, 3], ![0, 4, 1, 5, 6, 2], ![0, 3, 1, 2, 6, 5], ![0, 1, 3, 2, 6, 4], ![0, 1, 3, 2, 5, 4]], proof := .tail 208 }

theorem namedLeaf060_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 188)) namedLeaf060 = true :=
  by decide +kernel

def namedLeaf061 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 2, 4, 3, 5, 6], ![0, 1, 4, 6, 5, 3], ![0, 4, 1, 5, 6, 2], ![0, 3, 1, 2, 6, 5], ![0, 1, 3, 6, 2, 4], ![0, 1, 3, 5, 2, 4]], proof := .tail 340 }

theorem namedLeaf061_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 189)) namedLeaf061 = true :=
  by decide +kernel

def namedLeaf062 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 2, 4, 3, 5, 6], ![0, 1, 4, 6, 5, 3], ![0, 4, 1, 6, 5, 2], ![0, 3, 1, 2, 6, 5], ![0, 1, 6, 3, 2, 4], ![0, 1, 5, 3, 2, 4]], proof := .tail 168 }

theorem namedLeaf062_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 190)) namedLeaf062 = true :=
  by decide +kernel

def namedLeaf063 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 2, 4, 3, 5, 6], ![0, 1, 6, 4, 5, 3], ![0, 4, 1, 5, 6, 2], ![0, 3, 1, 6, 2, 5], ![0, 1, 3, 6, 2, 4], ![0, 1, 3, 5, 4, 2]], proof := .tail 251 }

theorem namedLeaf063_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 191)) namedLeaf063 = true :=
  by decide +kernel

def namedLeaf064 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 2, 4, 3, 5, 6], ![0, 1, 6, 4, 5, 3], ![0, 4, 1, 6, 5, 2], ![0, 3, 1, 6, 2, 5], ![0, 1, 6, 3, 2, 4], ![0, 1, 5, 3, 4, 2]], proof := .tail 168 }

theorem namedLeaf064_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 192)) namedLeaf064 = true :=
  by decide +kernel

def namedLeaf065 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 2, 4, 3, 6, 5], ![0, 1, 4, 6, 5, 3], ![0, 4, 1, 6, 5, 2], ![0, 3, 1, 2, 6, 5], ![0, 6, 1, 3, 2, 4], ![0, 5, 1, 3, 2, 4]], proof := .tail 11 }

theorem namedLeaf065_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 193)) namedLeaf065 = true :=
  by decide +kernel

def namedLeaf066 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 2, 4, 3, 6, 5], ![0, 1, 6, 4, 5, 3], ![0, 4, 1, 6, 5, 2], ![0, 3, 1, 6, 2, 5], ![0, 6, 1, 3, 2, 4], ![0, 5, 1, 3, 4, 2]], proof := .tail 162 }

theorem namedLeaf066_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 194)) namedLeaf066 = true :=
  by decide +kernel

def namedLeaf067 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 2, 4, 6, 3, 5], ![0, 1, 4, 6, 5, 3], ![0, 4, 6, 1, 5, 2], ![0, 3, 1, 2, 6, 5], ![0, 6, 1, 3, 2, 4], ![0, 5, 3, 1, 2, 4]], proof := .tail 175 }

theorem namedLeaf067_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 195)) namedLeaf067 = true :=
  by decide +kernel

def namedLeaf068 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 2, 4, 6, 3, 5], ![0, 1, 6, 4, 5, 3], ![0, 4, 6, 1, 5, 2], ![0, 3, 1, 6, 2, 5], ![0, 6, 1, 3, 2, 4], ![0, 5, 3, 1, 4, 2]], proof := .tail 121 }

theorem namedLeaf068_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 196)) namedLeaf068 = true :=
  by decide +kernel

def namedLeaf069 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 2, 6, 4, 3, 5], ![0, 1, 6, 4, 5, 3], ![0, 4, 6, 1, 5, 2], ![0, 3, 6, 1, 2, 5], ![0, 6, 1, 3, 2, 4], ![0, 5, 3, 4, 1, 2]], proof := .tail 320 }

theorem namedLeaf069_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 197)) namedLeaf069 = true :=
  by decide +kernel

def namedLeaf070 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 2, 6, 4, 3, 5], ![0, 1, 6, 4, 5, 3], ![0, 6, 4, 1, 5, 2], ![0, 6, 3, 1, 2, 5], ![0, 6, 1, 3, 2, 4], ![0, 5, 4, 3, 1, 2]], proof := .tail 131 }

theorem namedLeaf070_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 198)) namedLeaf070 = true :=
  by decide +kernel

def namedLeaf071 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 2, 4, 3, 5, 6], ![0, 1, 5, 4, 3, 6], ![0, 4, 1, 5, 2, 6], ![0, 3, 1, 5, 2, 6], ![0, 1, 3, 4, 2, 6], ![0, 1, 2, 3, 4, 5]], proof := .tail 41 }

theorem namedLeaf071_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 199)) namedLeaf071 = true :=
  by decide +kernel

def namedLeaf072 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 2, 4, 3, 5, 6], ![0, 1, 5, 4, 6, 3], ![0, 4, 1, 5, 6, 2], ![0, 3, 1, 5, 2, 6], ![0, 1, 3, 4, 2, 6], ![0, 1, 3, 2, 4, 5]], proof := .tail 52 }

theorem namedLeaf072_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 200)) namedLeaf072 = true :=
  by decide +kernel

def namedLeaf073 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 2, 4, 3, 5, 6], ![0, 1, 5, 6, 4, 3], ![0, 4, 1, 5, 6, 2], ![0, 3, 1, 5, 6, 2], ![0, 1, 3, 4, 2, 6], ![0, 1, 3, 4, 2, 5]], proof := .tail 10 }

theorem namedLeaf073_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 201)) namedLeaf073 = true :=
  by decide +kernel

def namedLeaf074 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 2, 4, 3, 5, 6], ![0, 1, 6, 5, 4, 3], ![0, 4, 1, 5, 6, 2], ![0, 3, 1, 5, 6, 2], ![0, 1, 3, 4, 6, 2], ![0, 1, 3, 4, 5, 2]], proof := .tail 288 }

theorem namedLeaf074_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 202)) namedLeaf074 = true :=
  by decide +kernel

def namedLeaf075 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 2, 4, 3, 5, 6], ![0, 1, 6, 5, 4, 3], ![0, 4, 1, 5, 6, 2], ![0, 3, 1, 6, 5, 2], ![0, 1, 3, 6, 4, 2], ![0, 1, 3, 5, 4, 2]], proof := .tail 169 }

theorem namedLeaf075_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 203)) namedLeaf075 = true :=
  by decide +kernel

def namedLeaf076 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 2, 4, 3, 5, 6], ![0, 1, 6, 5, 4, 3], ![0, 4, 1, 6, 5, 2], ![0, 3, 1, 6, 5, 2], ![0, 1, 6, 3, 4, 2], ![0, 1, 5, 3, 4, 2]], proof := .tail 153 }

theorem namedLeaf076_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 204)) namedLeaf076 = true :=
  by decide +kernel

def namedLeaf077 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 2, 4, 3, 6, 5], ![0, 1, 6, 5, 4, 3], ![0, 4, 1, 6, 5, 2], ![0, 3, 1, 6, 5, 2], ![0, 6, 1, 3, 4, 2], ![0, 5, 1, 3, 4, 2]], proof := .tail 4 }

theorem namedLeaf077_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 205)) namedLeaf077 = true :=
  by decide +kernel

def namedLeaf078 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 2, 4, 6, 3, 5], ![0, 1, 6, 5, 4, 3], ![0, 4, 6, 1, 5, 2], ![0, 3, 1, 6, 5, 2], ![0, 6, 1, 3, 4, 2], ![0, 5, 3, 1, 4, 2]], proof := .tail 235 }

theorem namedLeaf078_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 206)) namedLeaf078 = true :=
  by decide +kernel

def namedLeaf079 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 2, 6, 4, 3, 5], ![0, 1, 6, 5, 4, 3], ![0, 4, 6, 1, 5, 2], ![0, 3, 6, 1, 5, 2], ![0, 6, 1, 3, 4, 2], ![0, 5, 3, 4, 1, 2]], proof := .tail 342 }

theorem namedLeaf079_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 207)) namedLeaf079 = true :=
  by decide +kernel

def namedLeaf080 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 2, 6, 4, 3, 5], ![0, 1, 6, 5, 4, 3], ![0, 6, 4, 1, 5, 2], ![0, 6, 3, 1, 5, 2], ![0, 6, 1, 3, 4, 2], ![0, 5, 4, 3, 1, 2]], proof := .tail 232 }

theorem namedLeaf080_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 208)) namedLeaf080 = true :=
  by decide +kernel

def namedLeaf081 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 2, 4, 5, 3, 6], ![0, 1, 4, 5, 3, 6], ![0, 4, 5, 1, 2, 6], ![0, 3, 1, 2, 5, 6], ![0, 3, 1, 2, 4, 6], ![0, 1, 2, 3, 4, 5]], proof := .tail 89 }

theorem namedLeaf081_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 209)) namedLeaf081 = true :=
  by decide +kernel

def namedLeaf082 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 2, 4, 5, 3, 6], ![0, 1, 4, 5, 3, 6], ![0, 4, 5, 1, 2, 6], ![0, 3, 1, 2, 6, 5], ![0, 3, 1, 2, 6, 4], ![0, 1, 2, 3, 5, 4]], proof := .tail 231 }

theorem namedLeaf082_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 210)) namedLeaf082 = true :=
  by decide +kernel

def namedLeaf083 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 2, 4, 5, 3, 6], ![0, 1, 5, 4, 3, 6], ![0, 4, 5, 1, 2, 6], ![0, 3, 1, 5, 2, 6], ![0, 3, 1, 4, 2, 6], ![0, 1, 2, 3, 4, 5]], proof := .tail 81 }

theorem namedLeaf083_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 211)) namedLeaf083 = true :=
  by decide +kernel

def namedLeaf084 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 2, 5, 4, 3, 6], ![0, 1, 5, 4, 3, 6], ![0, 4, 5, 1, 2, 6], ![0, 3, 5, 1, 2, 6], ![0, 3, 4, 1, 2, 6], ![0, 1, 2, 3, 4, 5]], proof := .tail 70 }

theorem namedLeaf084_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 212)) namedLeaf084 = true :=
  by decide +kernel

def namedLeaf085 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 2, 5, 4, 3, 6], ![0, 1, 5, 4, 3, 6], ![0, 5, 4, 1, 2, 6], ![0, 5, 3, 1, 2, 6], ![0, 4, 3, 1, 2, 6], ![0, 1, 2, 3, 4, 5]], proof := .tail 92 }

theorem namedLeaf085_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 213)) namedLeaf085 = true :=
  by decide +kernel

def namedLeaf086 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 2, 4, 5, 3, 6], ![0, 1, 4, 5, 6, 3], ![0, 4, 5, 1, 6, 2], ![0, 3, 1, 2, 5, 6], ![0, 3, 1, 2, 4, 6], ![0, 1, 3, 2, 4, 5]], proof := .tail 333 }

theorem namedLeaf086_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 214)) namedLeaf086 = true :=
  by decide +kernel

def namedLeaf087 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 2, 4, 5, 3, 6], ![0, 1, 4, 5, 6, 3], ![0, 4, 5, 1, 6, 2], ![0, 3, 1, 2, 6, 5], ![0, 3, 1, 2, 6, 4], ![0, 1, 3, 2, 5, 4]], proof := .tail 333 }

theorem namedLeaf087_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 215)) namedLeaf087 = true :=
  by decide +kernel

def namedLeaf088 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 2, 4, 5, 3, 6], ![0, 1, 4, 6, 5, 3], ![0, 4, 5, 1, 6, 2], ![0, 3, 1, 2, 6, 5], ![0, 3, 1, 6, 2, 4], ![0, 1, 3, 5, 2, 4]], proof := .tail 87 }

theorem namedLeaf088_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 216)) namedLeaf088 = true :=
  by decide +kernel

def namedLeaf089 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 2, 4, 5, 3, 6], ![0, 1, 6, 4, 5, 3], ![0, 4, 5, 1, 6, 2], ![0, 3, 1, 6, 2, 5], ![0, 3, 1, 6, 2, 4], ![0, 1, 3, 5, 4, 2]], proof := .tail 185 }

theorem namedLeaf089_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 217)) namedLeaf089 = true :=
  by decide +kernel

def namedLeaf090 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 2, 4, 5, 3, 6], ![0, 1, 5, 4, 6, 3], ![0, 4, 5, 1, 6, 2], ![0, 3, 1, 5, 2, 6], ![0, 3, 1, 4, 2, 6], ![0, 1, 3, 2, 4, 5]], proof := .tail 81 }

theorem namedLeaf090_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 218)) namedLeaf090 = true :=
  by decide +kernel

def namedLeaf091 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 2, 4, 5, 3, 6], ![0, 1, 5, 6, 4, 3], ![0, 4, 5, 1, 6, 2], ![0, 3, 1, 5, 6, 2], ![0, 3, 1, 4, 2, 6], ![0, 1, 3, 4, 2, 5]], proof := .tail 224 }

theorem namedLeaf091_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 219)) namedLeaf091 = true :=
  by decide +kernel

def namedLeaf092 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 2, 4, 5, 3, 6], ![0, 1, 6, 5, 4, 3], ![0, 4, 5, 1, 6, 2], ![0, 3, 1, 5, 6, 2], ![0, 3, 1, 4, 6, 2], ![0, 1, 3, 4, 5, 2]], proof := .tail 36 }

theorem namedLeaf092_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 220)) namedLeaf092 = true :=
  by decide +kernel

def namedLeaf093 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 2, 4, 5, 3, 6], ![0, 1, 6, 5, 4, 3], ![0, 4, 5, 1, 6, 2], ![0, 3, 1, 6, 5, 2], ![0, 3, 1, 6, 4, 2], ![0, 1, 3, 5, 4, 2]], proof := .tail 60 }

theorem namedLeaf093_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 221)) namedLeaf093 = true :=
  by decide +kernel

def namedLeaf094 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 2, 5, 4, 3, 6], ![0, 1, 5, 4, 6, 3], ![0, 4, 5, 1, 6, 2], ![0, 3, 5, 1, 2, 6], ![0, 3, 4, 1, 2, 6], ![0, 1, 3, 2, 4, 5]], proof := .tail 198 }

theorem namedLeaf094_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 222)) namedLeaf094 = true :=
  by decide +kernel

def namedLeaf095 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 2, 5, 4, 3, 6], ![0, 1, 5, 6, 4, 3], ![0, 4, 5, 1, 6, 2], ![0, 3, 5, 1, 6, 2], ![0, 3, 4, 1, 2, 6], ![0, 1, 3, 4, 2, 5]], proof := .tail 336 }

theorem namedLeaf095_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 223)) namedLeaf095 = true :=
  by decide +kernel

def namedLeaf096 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 2, 5, 4, 3, 6], ![0, 1, 6, 5, 4, 3], ![0, 4, 5, 1, 6, 2], ![0, 3, 5, 1, 6, 2], ![0, 3, 4, 1, 6, 2], ![0, 1, 3, 4, 5, 2]], proof := .tail 100 }

theorem namedLeaf096_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 224)) namedLeaf096 = true :=
  by decide +kernel

def namedLeaf097 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 2, 5, 4, 3, 6], ![0, 1, 5, 4, 6, 3], ![0, 5, 4, 1, 6, 2], ![0, 5, 3, 1, 2, 6], ![0, 4, 3, 1, 2, 6], ![0, 1, 3, 2, 4, 5]], proof := .tail 163 }

theorem namedLeaf097_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 225)) namedLeaf097 = true :=
  by decide +kernel

def namedLeaf098 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 2, 5, 4, 3, 6], ![0, 1, 5, 6, 4, 3], ![0, 5, 4, 1, 6, 2], ![0, 5, 3, 1, 6, 2], ![0, 4, 3, 1, 2, 6], ![0, 1, 3, 4, 2, 5]], proof := .tail 281 }

theorem namedLeaf098_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 226)) namedLeaf098 = true :=
  by decide +kernel

def namedLeaf099 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 2, 5, 4, 3, 6], ![0, 1, 6, 5, 4, 3], ![0, 5, 4, 1, 6, 2], ![0, 5, 3, 1, 6, 2], ![0, 4, 3, 1, 6, 2], ![0, 1, 3, 4, 5, 2]], proof := .tail 263 }

theorem namedLeaf099_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 227)) namedLeaf099 = true :=
  by decide +kernel

def namedLeaf100 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 2, 4, 5, 6, 3], ![0, 1, 4, 5, 6, 3], ![0, 4, 5, 6, 1, 2], ![0, 3, 1, 2, 5, 6], ![0, 3, 1, 2, 4, 6], ![0, 3, 1, 2, 4, 5]], proof := .tail 89 }

theorem namedLeaf100_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 228)) namedLeaf100 = true :=
  by decide +kernel

def namedLeaf101 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 2, 4, 5, 6, 3], ![0, 1, 4, 5, 6, 3], ![0, 4, 5, 6, 1, 2], ![0, 3, 1, 2, 6, 5], ![0, 3, 1, 2, 6, 4], ![0, 3, 1, 2, 5, 4]], proof := .tail 326 }

theorem namedLeaf101_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 229)) namedLeaf101 = true :=
  by decide +kernel

def namedLeaf102 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 2, 4, 5, 6, 3], ![0, 1, 4, 6, 5, 3], ![0, 4, 5, 6, 1, 2], ![0, 3, 1, 2, 6, 5], ![0, 3, 1, 6, 2, 4], ![0, 3, 1, 5, 2, 4]], proof := .low (![197, 184, 103, 46, 53, 292, 54, 17, 238, 113, 242, 107, 305, 5, 29, 317, 330, 264, 202, 328, 203, 57, 341, 114, 22, 123, 146, 90]) }

theorem namedLeaf102_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 230)) namedLeaf102 = true :=
  by decide +kernel

def namedLeaf103 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 2, 4, 6, 5, 3], ![0, 1, 4, 6, 5, 3], ![0, 4, 5, 6, 1, 2], ![0, 3, 1, 2, 6, 5], ![0, 3, 6, 1, 2, 4], ![0, 3, 5, 1, 2, 4]], proof := .low (![257, 184, 103, 322, 219, 101, 110, 88, 40, 194, 289, 43, 44, 173, 186, 166, 43, 264, 77, 193, 43, 161, 65, 43, 296, 43, 38, 43]) }

theorem namedLeaf103_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 231)) namedLeaf103 = true :=
  by decide +kernel

def namedLeaf104 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 2, 4, 6, 5, 3], ![0, 1, 4, 6, 5, 3], ![0, 4, 6, 5, 1, 2], ![0, 3, 1, 2, 6, 5], ![0, 6, 3, 1, 2, 4], ![0, 5, 3, 1, 2, 4]], proof := .low (![254, 184, 103, 322, 265, 272, 0, 88, 40, 194, 303, 295, 259, 173, 186, 290, 244, 264, 77, 193, 170, 161, 127, 31, 296, 156, 134, 314]) }

theorem namedLeaf104_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 232)) namedLeaf104 = true :=
  by decide +kernel

def namedLeaf105 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 2, 4, 5, 6, 3], ![0, 1, 6, 4, 5, 3], ![0, 4, 5, 6, 1, 2], ![0, 3, 1, 6, 2, 5], ![0, 3, 1, 6, 2, 4], ![0, 3, 1, 5, 4, 2]], proof := .tail 258 }

theorem namedLeaf105_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 233)) namedLeaf105 = true :=
  by decide +kernel

def namedLeaf106 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 2, 4, 6, 5, 3], ![0, 1, 6, 4, 5, 3], ![0, 4, 5, 6, 1, 2], ![0, 3, 1, 6, 2, 5], ![0, 3, 6, 1, 2, 4], ![0, 3, 5, 1, 4, 2]], proof := .tail 258 }

theorem namedLeaf106_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 234)) namedLeaf106 = true :=
  by decide +kernel

def namedLeaf107 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 2, 4, 6, 5, 3], ![0, 1, 6, 4, 5, 3], ![0, 4, 6, 5, 1, 2], ![0, 3, 1, 6, 2, 5], ![0, 6, 3, 1, 2, 4], ![0, 5, 3, 1, 4, 2]], proof := .tail 121 }

theorem namedLeaf107_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 235)) namedLeaf107 = true :=
  by decide +kernel

def namedLeaf108 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 2, 6, 4, 5, 3], ![0, 1, 6, 4, 5, 3], ![0, 4, 5, 6, 1, 2], ![0, 3, 6, 1, 2, 5], ![0, 3, 6, 1, 2, 4], ![0, 3, 5, 4, 1, 2]], proof := .tail 21 }

theorem namedLeaf108_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 236)) namedLeaf108 = true :=
  by decide +kernel

def namedLeaf109 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 2, 6, 4, 5, 3], ![0, 1, 6, 4, 5, 3], ![0, 4, 6, 5, 1, 2], ![0, 3, 6, 1, 2, 5], ![0, 6, 3, 1, 2, 4], ![0, 5, 3, 4, 1, 2]], proof := .tail 21 }

theorem namedLeaf109_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 237)) namedLeaf109 = true :=
  by decide +kernel

def namedLeaf110 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 2, 6, 4, 5, 3], ![0, 1, 6, 4, 5, 3], ![0, 6, 4, 5, 1, 2], ![0, 6, 3, 1, 2, 5], ![0, 6, 3, 1, 2, 4], ![0, 5, 4, 3, 1, 2]], proof := .tail 332 }

theorem namedLeaf110_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 238)) namedLeaf110 = true :=
  by decide +kernel

def namedLeaf111 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 2, 4, 5, 6, 3], ![0, 1, 5, 4, 6, 3], ![0, 4, 5, 6, 1, 2], ![0, 3, 1, 5, 2, 6], ![0, 3, 1, 4, 2, 6], ![0, 3, 1, 2, 4, 5]], proof := .tail 81 }

theorem namedLeaf111_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 239)) namedLeaf111 = true :=
  by decide +kernel

def namedLeaf112 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 2, 4, 5, 6, 3], ![0, 1, 5, 6, 4, 3], ![0, 4, 5, 6, 1, 2], ![0, 3, 1, 5, 6, 2], ![0, 3, 1, 4, 2, 6], ![0, 3, 1, 4, 2, 5]], proof := .low (![75, 80, 174, 18, 164, 292, 54, 205, 227, 236, 270, 107, 305, 82, 20, 278, 330, 120, 199, 32, 1, 1, 316, 114, 116, 123, 279, 90]) }

theorem namedLeaf112_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 240)) namedLeaf112 = true :=
  by decide +kernel

def namedLeaf113 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 2, 4, 5, 6, 3], ![0, 1, 6, 5, 4, 3], ![0, 4, 5, 6, 1, 2], ![0, 3, 1, 5, 6, 2], ![0, 3, 1, 4, 6, 2], ![0, 3, 1, 4, 5, 2]], proof := .tail 36 }

theorem namedLeaf113_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 241)) namedLeaf113 = true :=
  by decide +kernel

def namedLeaf114 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 2, 4, 5, 6, 3], ![0, 1, 6, 5, 4, 3], ![0, 4, 5, 6, 1, 2], ![0, 3, 1, 6, 5, 2], ![0, 3, 1, 6, 4, 2], ![0, 3, 1, 5, 4, 2]], proof := .tail 78 }

theorem namedLeaf114_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 242)) namedLeaf114 = true :=
  by decide +kernel

def namedLeaf115 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 2, 4, 6, 5, 3], ![0, 1, 6, 5, 4, 3], ![0, 4, 5, 6, 1, 2], ![0, 3, 1, 6, 5, 2], ![0, 3, 6, 1, 4, 2], ![0, 3, 5, 1, 4, 2]], proof := .tail 118 }

theorem namedLeaf115_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 243)) namedLeaf115 = true :=
  by decide +kernel

def namedLeaf116 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 2, 4, 6, 5, 3], ![0, 1, 6, 5, 4, 3], ![0, 4, 6, 5, 1, 2], ![0, 3, 1, 6, 5, 2], ![0, 6, 3, 1, 4, 2], ![0, 5, 3, 1, 4, 2]], proof := .low (![97, 234, 318, 222, 239, 272, 0, 304, 210, 274, 98, 295, 259, 275, 24, 252, 244, 230, 50, 217, 262, 262, 331, 31, 2, 156, 106, 314]) }

theorem namedLeaf116_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 244)) namedLeaf116 = true :=
  by decide +kernel

def namedLeaf117 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 2, 6, 4, 5, 3], ![0, 1, 6, 5, 4, 3], ![0, 4, 5, 6, 1, 2], ![0, 3, 6, 1, 5, 2], ![0, 3, 6, 1, 4, 2], ![0, 3, 5, 4, 1, 2]], proof := .tail 313 }

theorem namedLeaf117_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 245)) namedLeaf117 = true :=
  by decide +kernel

def namedLeaf118 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 2, 6, 4, 5, 3], ![0, 1, 6, 5, 4, 3], ![0, 4, 6, 5, 1, 2], ![0, 3, 6, 1, 5, 2], ![0, 6, 3, 1, 4, 2], ![0, 5, 3, 4, 1, 2]], proof := .tail 313 }

theorem namedLeaf118_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 246)) namedLeaf118 = true :=
  by decide +kernel

def namedLeaf119 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 2, 6, 4, 5, 3], ![0, 1, 6, 5, 4, 3], ![0, 6, 4, 5, 1, 2], ![0, 6, 3, 1, 5, 2], ![0, 6, 3, 1, 4, 2], ![0, 5, 4, 3, 1, 2]], proof := .tail 84 }

theorem namedLeaf119_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 247)) namedLeaf119 = true :=
  by decide +kernel

def namedLeaf120 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 2, 5, 4, 6, 3], ![0, 1, 5, 4, 6, 3], ![0, 4, 5, 6, 1, 2], ![0, 3, 5, 1, 2, 6], ![0, 3, 4, 1, 2, 6], ![0, 3, 1, 2, 4, 5]], proof := .tail 70 }

theorem namedLeaf120_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 248)) namedLeaf120 = true :=
  by decide +kernel

def namedLeaf121 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 2, 5, 4, 6, 3], ![0, 1, 5, 6, 4, 3], ![0, 4, 5, 6, 1, 2], ![0, 3, 5, 1, 6, 2], ![0, 3, 4, 1, 2, 6], ![0, 3, 1, 4, 2, 5]], proof := .tail 133 }

theorem namedLeaf121_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 249)) namedLeaf121 = true :=
  by decide +kernel

def namedLeaf122 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 2, 5, 4, 6, 3], ![0, 1, 6, 5, 4, 3], ![0, 4, 5, 6, 1, 2], ![0, 3, 5, 1, 6, 2], ![0, 3, 4, 1, 6, 2], ![0, 3, 1, 4, 5, 2]], proof := .tail 100 }

theorem namedLeaf122_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 250)) namedLeaf122 = true :=
  by decide +kernel

def namedLeaf123 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 2, 5, 6, 4, 3], ![0, 1, 5, 6, 4, 3], ![0, 4, 5, 6, 1, 2], ![0, 3, 5, 6, 1, 2], ![0, 3, 4, 1, 2, 6], ![0, 3, 4, 1, 2, 5]], proof := .low (![261, 109, 135, 248, 143, 286, 339, 229, 250, 63, 124, 136, 42, 99, 178, 291, 136, 171, 165, 256, 136, 226, 223, 136, 144, 136, 26, 136]) }

theorem namedLeaf123_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 251)) namedLeaf123 = true :=
  by decide +kernel

def namedLeaf124 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 2, 5, 6, 4, 3], ![0, 1, 6, 5, 4, 3], ![0, 4, 5, 6, 1, 2], ![0, 3, 5, 6, 1, 2], ![0, 3, 4, 1, 6, 2], ![0, 3, 4, 1, 5, 2]], proof := .tail 71 }

theorem namedLeaf124_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 252)) namedLeaf124 = true :=
  by decide +kernel

def namedLeaf125 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 2, 6, 5, 4, 3], ![0, 1, 6, 5, 4, 3], ![0, 4, 5, 6, 1, 2], ![0, 3, 5, 6, 1, 2], ![0, 3, 4, 6, 1, 2], ![0, 3, 4, 5, 1, 2]], proof := .tail 334 }

theorem namedLeaf125_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 253)) namedLeaf125 = true :=
  by decide +kernel

def namedLeaf126 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 2, 6, 5, 4, 3], ![0, 1, 6, 5, 4, 3], ![0, 4, 5, 6, 1, 2], ![0, 3, 6, 5, 1, 2], ![0, 3, 6, 4, 1, 2], ![0, 3, 5, 4, 1, 2]], proof := .tail 93 }

theorem namedLeaf126_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 254)) namedLeaf126 = true :=
  by decide +kernel

def namedLeaf127 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 2, 6, 5, 4, 3], ![0, 1, 6, 5, 4, 3], ![0, 4, 6, 5, 1, 2], ![0, 3, 6, 5, 1, 2], ![0, 6, 3, 4, 1, 2], ![0, 5, 3, 4, 1, 2]], proof := .low (![240, 176, 112, 158, 273, 39, 154, 25, 96, 150, 76, 68, 293, 190, 51, 94, 68, 241, 337, 13, 68, 179, 307, 68, 64, 68, 325, 68]) }

theorem namedLeaf127_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 255)) namedLeaf127 = true :=
  by decide +kernel

def fallback : LeafData := { rows := fun _ _ => 0, proof := .tail 0 }
def lookup (offset : ℕ) : LeafData :=
  if offset < 128 then (if offset < 64 then (if offset < 32 then (if offset < 16 then (if offset < 8 then (if offset < 4 then (if offset < 2 then (if offset < 1 then (namedLeaf000) else (namedLeaf001)) else (if offset < 3 then (namedLeaf002) else (namedLeaf003))) else (if offset < 6 then (if offset < 5 then (namedLeaf004) else (namedLeaf005)) else (if offset < 7 then (namedLeaf006) else (namedLeaf007)))) else (if offset < 12 then (if offset < 10 then (if offset < 9 then (namedLeaf008) else (namedLeaf009)) else (if offset < 11 then (namedLeaf010) else (namedLeaf011))) else (if offset < 14 then (if offset < 13 then (namedLeaf012) else (namedLeaf013)) else (if offset < 15 then (namedLeaf014) else (namedLeaf015))))) else (if offset < 24 then (if offset < 20 then (if offset < 18 then (if offset < 17 then (namedLeaf016) else (namedLeaf017)) else (if offset < 19 then (namedLeaf018) else (namedLeaf019))) else (if offset < 22 then (if offset < 21 then (namedLeaf020) else (namedLeaf021)) else (if offset < 23 then (namedLeaf022) else (namedLeaf023)))) else (if offset < 28 then (if offset < 26 then (if offset < 25 then (namedLeaf024) else (namedLeaf025)) else (if offset < 27 then (namedLeaf026) else (namedLeaf027))) else (if offset < 30 then (if offset < 29 then (namedLeaf028) else (namedLeaf029)) else (if offset < 31 then (namedLeaf030) else (namedLeaf031)))))) else (if offset < 48 then (if offset < 40 then (if offset < 36 then (if offset < 34 then (if offset < 33 then (namedLeaf032) else (namedLeaf033)) else (if offset < 35 then (namedLeaf034) else (namedLeaf035))) else (if offset < 38 then (if offset < 37 then (namedLeaf036) else (namedLeaf037)) else (if offset < 39 then (namedLeaf038) else (namedLeaf039)))) else (if offset < 44 then (if offset < 42 then (if offset < 41 then (namedLeaf040) else (namedLeaf041)) else (if offset < 43 then (namedLeaf042) else (namedLeaf043))) else (if offset < 46 then (if offset < 45 then (namedLeaf044) else (namedLeaf045)) else (if offset < 47 then (namedLeaf046) else (namedLeaf047))))) else (if offset < 56 then (if offset < 52 then (if offset < 50 then (if offset < 49 then (namedLeaf048) else (namedLeaf049)) else (if offset < 51 then (namedLeaf050) else (namedLeaf051))) else (if offset < 54 then (if offset < 53 then (namedLeaf052) else (namedLeaf053)) else (if offset < 55 then (namedLeaf054) else (namedLeaf055)))) else (if offset < 60 then (if offset < 58 then (if offset < 57 then (namedLeaf056) else (namedLeaf057)) else (if offset < 59 then (namedLeaf058) else (namedLeaf059))) else (if offset < 62 then (if offset < 61 then (namedLeaf060) else (namedLeaf061)) else (if offset < 63 then (namedLeaf062) else (namedLeaf063))))))) else (if offset < 96 then (if offset < 80 then (if offset < 72 then (if offset < 68 then (if offset < 66 then (if offset < 65 then (namedLeaf064) else (namedLeaf065)) else (if offset < 67 then (namedLeaf066) else (namedLeaf067))) else (if offset < 70 then (if offset < 69 then (namedLeaf068) else (namedLeaf069)) else (if offset < 71 then (namedLeaf070) else (namedLeaf071)))) else (if offset < 76 then (if offset < 74 then (if offset < 73 then (namedLeaf072) else (namedLeaf073)) else (if offset < 75 then (namedLeaf074) else (namedLeaf075))) else (if offset < 78 then (if offset < 77 then (namedLeaf076) else (namedLeaf077)) else (if offset < 79 then (namedLeaf078) else (namedLeaf079))))) else (if offset < 88 then (if offset < 84 then (if offset < 82 then (if offset < 81 then (namedLeaf080) else (namedLeaf081)) else (if offset < 83 then (namedLeaf082) else (namedLeaf083))) else (if offset < 86 then (if offset < 85 then (namedLeaf084) else (namedLeaf085)) else (if offset < 87 then (namedLeaf086) else (namedLeaf087)))) else (if offset < 92 then (if offset < 90 then (if offset < 89 then (namedLeaf088) else (namedLeaf089)) else (if offset < 91 then (namedLeaf090) else (namedLeaf091))) else (if offset < 94 then (if offset < 93 then (namedLeaf092) else (namedLeaf093)) else (if offset < 95 then (namedLeaf094) else (namedLeaf095)))))) else (if offset < 112 then (if offset < 104 then (if offset < 100 then (if offset < 98 then (if offset < 97 then (namedLeaf096) else (namedLeaf097)) else (if offset < 99 then (namedLeaf098) else (namedLeaf099))) else (if offset < 102 then (if offset < 101 then (namedLeaf100) else (namedLeaf101)) else (if offset < 103 then (namedLeaf102) else (namedLeaf103)))) else (if offset < 108 then (if offset < 106 then (if offset < 105 then (namedLeaf104) else (namedLeaf105)) else (if offset < 107 then (namedLeaf106) else (namedLeaf107))) else (if offset < 110 then (if offset < 109 then (namedLeaf108) else (namedLeaf109)) else (if offset < 111 then (namedLeaf110) else (namedLeaf111))))) else (if offset < 120 then (if offset < 116 then (if offset < 114 then (if offset < 113 then (namedLeaf112) else (namedLeaf113)) else (if offset < 115 then (namedLeaf114) else (namedLeaf115))) else (if offset < 118 then (if offset < 117 then (namedLeaf116) else (namedLeaf117)) else (if offset < 119 then (namedLeaf118) else (namedLeaf119)))) else (if offset < 124 then (if offset < 122 then (if offset < 121 then (namedLeaf120) else (namedLeaf121)) else (if offset < 123 then (namedLeaf122) else (namedLeaf123))) else (if offset < 126 then (if offset < 125 then (namedLeaf124) else (namedLeaf125)) else (if offset < 127 then (namedLeaf126) else (namedLeaf127)))))))) else fallback

theorem point_checked (j : Fin 128) :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 (128 + j.val))) (lookup j.val) = true := by
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

theorem correct (id : Fin 24698) (hlow : 128 ≤ id.val) (hhigh : id.val < 256) :
    leafCheck library (N4R2WordTree.catalog id) (lookup (id.val - 128)) = true := by
  let j : Fin 128 := ⟨id.val - 128, by omega⟩
  have hsum : 128 + j.val = id.val := by dsimp [j]; omega
  have hindex : Fin.ofNat 24698 (128 + j.val) = id := by
    apply Fin.ext
    simp only [Fin.ofNat, hsum, Nat.mod_eq_of_lt id.isLt]
  have hh := point_checked j
  rw [hindex] at hh
  exact hh

#print axioms point_checked
#print axioms correct
end Jsp404.N4R2OuterLeftData.LeafShard001
