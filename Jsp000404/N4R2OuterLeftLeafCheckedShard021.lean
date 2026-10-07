import Jsp000404.N4R2OuterLeftReplay
import Jsp000404.N4R2WordCatalog

set_option autoImplicit false
set_option pp.fullNames true
set_option maxRecDepth 8192
set_option maxHeartbeats 0
set_option Elab.async false

namespace Jsp404.N4R2OuterLeftData.LeafShard021
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

-- Cycle fingerprint 00cbb9363763c5b6ad0429e7e3b14849f96f8ed98856dd482d6e09ee2efda898.
def localCycle00001 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 2, .distance 2 6, .distance 4 6, .distance 3 4, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, -1, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, true] }
  origin := ![.corridorUpper 2 3, .triangle 15 0, .triangle 18 0, .triangle 29 1, .triangle 32 0, .triangle 31 0, .corridorLower 4 5, .thetaNext 3]

-- Cycle fingerprint 00dc0ef5f71549f6d6fb3b3c7eeb25ea484acf0e8ba621ee802ce0ab3c11c5da.
def localCycle00002 : Cycle where
  length := 4
  data := {
    node := ![.distance 4 5, .distance 1 4, .distance 1 2, .distance 2 5, .distance 4 5]
    constant := ![-1, -2, 2, 0]
    coefficient := ![0, 0, 0, 0]
    strict := ![false, false, true, false] }
  origin := ![.triangle 22 0, .gapLower 1 2, .gapUpper 2 2, .gapLower 5 4]

-- Cycle fingerprint 06081cbf301c44810aa99f4f89652439ee62a3aca0dfd1fdfbf3a1849631dbf6.
def localCycle00003 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 4, .distance 1 2, .distance 0 1, .theta 0, .zero, .theta 5, .distance 4 5, .distance 1 4]
    constant := ![-2, -2, -1, 0, 0, 3, -1]
    coefficient := ![0, 0, 0, 0, 1, 1, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 1 2, .gapLower 1 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 5, .corridorUpper 4 5, .triangle 22 0]

-- Cycle fingerprint 095395eb08c1f1382fc76411211003c7ace3cfbaba47a8611a11284c217ffdba.
def localCycle00004 : Cycle where
  length := 9
  data := {
    node := ![.distance 4 6, .distance 3 6, .distance 0 3, .distance 0 4, .distance 4 5, .distance 3 4, .theta 3, .distance 2 3, .distance 2 4, .distance 4 6]
    constant := ![0, -1, 0, -1, -1, -1, 3, 0, -1]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 0, 0]
    strict := ![true, false, false, false, false, false, false, true, false] }
  origin := ![.triangle 32 2, .triangle 11 0, .gapLower 0 4, .triangle 12 0, .triangle 31 0, .corridorLower 3 4, .corridorUpper 2 3, .triangle 25 2, .triangle 29 0]

-- Cycle fingerprint 0b41132e20b44dd78ba4220d3d9138d1ebcc935bbd2a4b2e98e907723e88c725.
def localCycle00005 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 5 6, .distance 2 5, .distance 1 2, .distance 2 4, .distance 0 2, .theta 0, .zero]
    constant := ![0, 3, -1, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 34 0, .triangle 30 0, .triangle 17 0, .triangle 16 0, .triangle 6 0, .corridorLower 0 2, .thetaLower 0]

-- Cycle fingerprint 0ccecf61284b253e811696ffd5d5a9ba593b420a5d9b13a3870f0f5bf7ea584b.
def localCycle00006 : Cycle where
  length := 3
  data := {
    node := ![.distance 0 1, .theta 1, .distance 1 3, .distance 0 1]
    constant := ![-2, 2, -1]
    coefficient := ![0, 1, 0]
    strict := ![false, false, false] }
  origin := ![.gapLower 1 0, .gapLower 1 6, .triangle 1 0]

-- Cycle fingerprint 0ce5feb5c446fe0d3c34079bd2c8dcf76cb6751142d4f12593a2906da1f53281.
def localCycle00007 : Cycle where
  length := 8
  data := {
    node := ![.distance 4 5, .theta 4, .theta 3, .zero, .theta 6, .distance 0 6, .distance 0 3, .distance 3 4, .distance 4 5]
    constant := ![-1, 0, 0, 0, 2, 0, -1, -1]
    coefficient := ![0, 0, 0, 1, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, true, false, false] }
  origin := ![.corridorLower 4 5, .thetaNext 3, .thetaLower 3, .thetaUpper 6, .gapUpper 6 0, .triangle 11 1, .triangle 9 0, .triangle 31 0]

-- Cycle fingerprint 0f1e82ca273e6cf1e4bdc1731734a72f0699ecea73cfc7de4f96b5254f06e631.
def localCycle00008 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 3, .distance 1 4, .distance 4 5, .distance 5 6, .distance 3 5, .distance 3 4, .theta 3]
    constant := ![3, 0, 0, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 2, .triangle 19 2, .triangle 22 0, .triangle 34 0, .triangle 33 0, .gapLower 3 1, .corridorLower 3 4]

-- Cycle fingerprint 1156018f6fdcdf511eccb1b8394c3068efb646236ac57986cbd793f4b2cd48ef.
def localCycle00009 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 2, .distance 0 1, .theta 1, .zero, .theta 5, .distance 4 5, .distance 2 4, .distance 1 2]
    constant := ![-2, -2, 0, 0, 3, -1, -1]
    coefficient := ![0, 0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 1 1, .gapLower 1 0, .thetaLower 1, .thetaUpper 5, .corridorUpper 4 5, .triangle 28 0, .triangle 16 0]

-- Cycle fingerprint 117a799ca9b580d21116cd4780d28b450d1b20c165beef9ae9ee443bdfda944e.
def localCycle00010 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 2, .distance 1 4, .distance 4 6, .distance 2 6, .distance 5 6, .distance 3 5, .distance 3 4, .theta 3]
    constant := ![3, -1, 0, -1, 0, 0, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, true, false, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 0, .triangle 16 2, .triangle 23 0, .triangle 29 2, .triangle 30 1, .triangle 33 0, .triangle 31 1, .corridorLower 3 4]

-- Cycle fingerprint 13e7b5ced78fd0e840d20a53a9fe69c9a062d4700c94298d20eeb4046ff7b89d.
def localCycle00011 : Cycle where
  length := 10
  data := {
    node := ![.theta 3, .distance 2 3, .distance 2 4, .distance 4 5, .distance 1 4, .distance 4 6, .distance 3 6, .distance 0 3, .distance 3 5, .distance 3 4, .theta 3]
    constant := ![3, 0, -1, -1, -1, 0, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, true, false, false, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 25 2, .triangle 28 0, .triangle 22 0, .triangle 23 0, .triangle 32 2, .triangle 11 0, .triangle 10 0, .triangle 31 1, .corridorLower 3 4]

-- Cycle fingerprint 1474485da1777db18e9d0593ae2e570b7b1f2d872cd0b32893f5af36a8c52c61.
def localCycle00012 : Cycle where
  length := 5
  data := {
    node := ![.distance 1 2, .distance 2 5, .distance 4 5, .distance 1 5, .distance 1 4, .distance 1 2]
    constant := ![2, 0, 0, -3, 0]
    coefficient := ![0, 0, 0, 0, 0]
    strict := ![true, false, false, false, true] }
  origin := ![.gapUpper 2 2, .gapLower 5 4, .gapLower 5 3, .gapLower 1 3, .triangle 16 1]

-- Cycle fingerprint 162013ce996f1ce680754e2067b9d0f1d36bd6a1c8bd2ea1849e70640327905a.
def localCycle00013 : Cycle where
  length := 5
  data := {
    node := ![.distance 1 2, .distance 2 5, .distance 4 5, .distance 1 5, .distance 1 4, .distance 1 2]
    constant := ![2, 0, 0, -2, 0]
    coefficient := ![0, 0, 0, 0, 0]
    strict := ![true, false, true, false, true] }
  origin := ![.gapUpper 2 2, .gapLower 5 4, .triangle 22 2, .gapLower 1 3, .triangle 16 1]

-- Cycle fingerprint 173f38c38c0c2da8bc000c884e8d290812e71342177261809a2027476d9d4c92.
def localCycle00014 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 2 4, .distance 4 5, .distance 1 4, .distance 1 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, -1, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, true, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 29 0, .triangle 28 0, .triangle 22 0, .triangle 16 1, .triangle 0 0, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint 175df82c3590dac8e7202648df5029824cf8b34a84ec28528ab0caa4b7af51e3.
def localCycle00015 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 4, .distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 2 5, .distance 5 6, .distance 1 5, .distance 1 4]
    constant := ![-1, -1, 0, 0, 3, 0, -1, -1, -2]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, false, false] }
  origin := ![.triangle 2 0, .corridorLower 0 1, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 26 2, .triangle 30 0, .triangle 24 0, .gapLower 1 3]

-- Cycle fingerprint 181eb11416e1fe676ad3f8b0bc69a2350be83200726d60e90158de3ba7235a65.
def localCycle00016 : Cycle where
  length := 8
  data := {
    node := ![.distance 5 6, .distance 4 6, .distance 2 4, .distance 1 2, .distance 0 1, .theta 1, .zero, .theta 6, .distance 5 6]
    constant := ![0, -1, -1, -1, -3, 0, 0, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 1]
    strict := ![true, false, false, false, false, false, false, false] }
  origin := ![.triangle 34 2, .triangle 29 0, .triangle 16 0, .triangle 0 0, .gapLower 1 0, .thetaLower 1, .thetaUpper 6, .corridorUpper 5 6]

-- Cycle fingerprint 192c4ed744780eac1a2f3e2f604422466f3d05ac78dd9ca71db9ae9201fd4450.
def localCycle00017 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 2 4, .distance 4 5, .distance 1 5, .distance 5 6, .distance 3 5, .distance 3 4, .theta 3]
    constant := ![3, 0, -1, 0, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 25 2, .triangle 28 0, .triangle 22 2, .triangle 24 0, .triangle 33 0, .gapLower 3 1, .corridorLower 3 4]

-- Cycle fingerprint 1c8c5d5c007056d6695139dd87f6e85116542d338fa226c79f943340b3fbe923.
def localCycle00018 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 3, .distance 1 5, .distance 5 6, .distance 3 5, .distance 3 4, .theta 3, .distance 2 3, .distance 1 3]
    constant := ![-3, -1, -1, 0, -1, 3, 0]
    coefficient := ![0, 0, 0, 0, 0, 1, 0]
    strict := ![false, false, false, false, false, false, true] }
  origin := ![.gapLower 1 5, .triangle 24 0, .triangle 33 0, .gapLower 3 1, .corridorLower 3 4, .corridorUpper 2 3, .triangle 15 2]

-- Cycle fingerprint 1d2938958239ccdc44a2b9513f673f5f08934b578c4af0f138bf2ec252b17a83.
def localCycle00019 : Cycle where
  length := 8
  data := {
    node := ![.distance 1 2, .distance 0 1, .theta 0, .zero, .theta 6, .distance 5 6, .distance 4 6, .distance 2 4, .distance 1 2]
    constant := ![-2, -1, 0, 0, 3, 0, -1, -1]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, false] }
  origin := ![.gapLower 1 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 29 0, .triangle 16 0]

-- Cycle fingerprint 1db1e1ad103a857db2d6d6142ac00ba79a87a0de866ddf6b96a98ce54174c628.
def localCycle00020 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 2, .distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 2 5, .distance 5 6, .distance 1 5, .distance 1 4, .distance 1 2]
    constant := ![-2, -1, 0, 0, 3, 0, -1, -1, -2, 0]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, false, false, true] }
  origin := ![.gapLower 1 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 26 2, .triangle 30 0, .triangle 24 0, .gapLower 1 3, .triangle 16 1]

-- Cycle fingerprint 1ee5c5d88ca8fcf261644710c37e94e1b4e41d455115ae77457e6e9ddf81e3ed.
def localCycle00021 : Cycle where
  length := 11
  data := {
    node := ![.theta 0, .zero, .theta 3, .distance 2 3, .distance 2 4, .distance 4 6, .distance 1 6, .distance 1 5, .distance 1 4, .distance 1 2, .distance 0 1, .theta 0]
    constant := ![0, 0, 3, 0, -1, 0, -2, 0, -2, -1, -1]
    coefficient := ![0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, true, false, false, false] }
  origin := ![.thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 25 2, .triangle 29 0, .gapLower 6 3, .gapLower 1 4, .triangle 22 1, .gapLower 1 2, .triangle 0 0, .corridorLower 0 1]

-- Cycle fingerprint 1fcb8758a6300ddb6f252b2b6256c3c24b333f7a61d3a9f2482271bd90c93505.
def localCycle00022 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 3, .distance 2 3, .distance 2 4, .distance 2 5, .distance 5 6, .distance 4 5, .distance 1 4, .distance 1 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, 0, -1, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 3, .corridorUpper 2 3, .triangle 25 2, .triangle 28 2, .triangle 30 0, .triangle 34 0, .triangle 22 0, .gapLower 1 2, .triangle 0 0, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint 22404b30b56843c0c4dfac7cfae7a9bc13ffd9bcfcd80ca1bb12d9645ac74bc9.
def localCycle00023 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 4, .distance 1 2, .distance 0 1, .theta 1, .zero, .theta 5, .distance 4 5, .distance 1 4]
    constant := ![-2, -1, -2, 0, 0, 3, -1]
    coefficient := ![0, 0, 0, 0, 1, 1, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 1 2, .triangle 0 0, .gapLower 1 0, .thetaLower 1, .thetaUpper 5, .corridorUpper 4 5, .triangle 22 0]

-- Cycle fingerprint 238d200ffe99e679d3cb48086f3ca05d9a5f7269fd24a0bcdcccb6d450de67e7.
def localCycle00024 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 2 4, .distance 2 5, .distance 5 6, .distance 4 6, .distance 3 4, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, 0, 0, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, false, false, true] }
  origin := ![.corridorUpper 2 3, .triangle 25 2, .triangle 28 2, .triangle 30 0, .triangle 34 2, .triangle 32 0, .triangle 31 0, .corridorLower 4 5, .thetaNext 3]

-- Cycle fingerprint 248034175f2b19e3989cd9a3e3ec4ab318483fb5fbdf33ff04803a88d0ebfb9b.
def localCycle00025 : Cycle where
  length := 10
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 3, .distance 1 4, .distance 4 5, .distance 5 6, .distance 3 6, .distance 0 3, .distance 3 5, .distance 3 4, .theta 3]
    constant := ![3, 0, 0, -1, -1, 0, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, true, false, false, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 2, .triangle 19 2, .triangle 22 0, .triangle 34 0, .triangle 33 2, .triangle 11 0, .triangle 10 0, .triangle 31 1, .corridorLower 3 4]

-- Cycle fingerprint 249e085f20922f98dd145e767f8f3785edec72c792482fa5fdea8aaf85ab0118.
def localCycle00026 : Cycle where
  length := 8
  data := {
    node := ![.distance 4 5, .distance 3 4, .theta 3, .distance 2 3, .distance 1 3, .distance 1 4, .distance 1 6, .distance 1 5, .distance 4 5]
    constant := ![-1, -1, 3, 0, -2, 0, -2, 0]
    coefficient := ![0, 0, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true, false, true] }
  origin := ![.triangle 31 0, .corridorLower 3 4, .corridorUpper 2 3, .triangle 15 2, .gapLower 1 5, .triangle 23 2, .gapLower 1 3, .triangle 22 1]

-- Cycle fingerprint 2773ed9635319496ce825ea275eb8e8bec2838ca1f447ad764e5bb52979bcd0d.
def localCycle00027 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 3, .distance 1 6, .distance 1 4, .distance 4 5, .distance 3 4, .theta 3, .distance 2 3, .distance 1 3]
    constant := ![-2, -2, -1, -1, -1, 3, 0]
    coefficient := ![0, 0, 0, 0, 0, 1, 0]
    strict := ![false, false, false, false, false, false, true] }
  origin := ![.gapLower 1 5, .gapLower 1 4, .triangle 22 0, .triangle 31 0, .corridorLower 3 4, .corridorUpper 2 3, .triangle 15 2]

-- Cycle fingerprint 27e37d7f52a55231af57a8dcd7afcc11c2b23f66972f6a82b84cbafb7c488574.
def localCycle00028 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 2, .distance 2 6, .distance 4 6, .distance 3 6, .distance 0 3, .distance 3 5, .distance 3 4, .theta 3]
    constant := ![3, -1, -1, 0, 0, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false, false, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 0, .triangle 18 0, .triangle 29 1, .triangle 32 2, .triangle 11 0, .triangle 10 0, .triangle 31 1, .corridorLower 3 4]

-- Cycle fingerprint 2802e02ed0cffa3beb1d769325aeaa3148f62418dd40d7c795883700c0b94a36.
def localCycle00029 : Cycle where
  length := 8
  data := {
    node := ![.distance 4 5, .distance 0 4, .distance 0 2, .distance 0 1, .theta 1, .distance 1 3, .distance 1 6, .distance 1 4, .distance 4 5]
    constant := ![-1, 0, 0, -2, 2, 0, 0, -1]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![false, false, true, false, false, true, true, false] }
  origin := ![.triangle 12 0, .gapLower 0 2, .triangle 0 1, .gapLower 1 0, .gapLower 1 6, .triangle 21 2, .triangle 23 1, .triangle 22 0]

-- Cycle fingerprint 29117a0ef66f2b0b6e6ddbd8712148df6d53031280e3107e54b9743b00bb42de.
def localCycle00030 : Cycle where
  length := 9
  data := {
    node := ![.distance 5 6, .distance 1 5, .distance 1 4, .distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 2 5, .distance 5 6]
    constant := ![-1, -3, -1, -1, 0, 0, 3, 0, -1]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, false, false, false, false, true, false] }
  origin := ![.triangle 24 0, .gapLower 1 3, .triangle 2 0, .corridorLower 0 1, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 26 2, .triangle 30 0]

-- Cycle fingerprint 2981ab2275c699ac69cc37d2c09c1a96b7f13026de7920db46d1aaa210c48586.
def localCycle00031 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 2, .distance 2 4, .distance 4 6, .distance 0 4, .distance 4 5, .distance 3 4, .theta 3]
    constant := ![3, -1, -1, -1, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 0, .triangle 16 0, .triangle 29 0, .triangle 13 0, .triangle 12 0, .triangle 31 0, .corridorLower 3 4]

-- Cycle fingerprint 2a7341e42bfaa7b486b88b9eecaf9eb27eacb4bf0e95efe865f8bfcc4e0a27c0.
def localCycle00032 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 3, .distance 1 4, .distance 4 6, .distance 3 6, .distance 0 3, .distance 3 5, .distance 3 4, .theta 3]
    constant := ![3, 0, 0, -1, 0, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, false, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 2, .triangle 19 2, .triangle 23 0, .triangle 32 2, .triangle 11 0, .triangle 10 0, .triangle 31 1, .corridorLower 3 4]

-- Cycle fingerprint 2e0e8c8d38814d1a0d11fd33863a0b53a9edbc0a76868f3e02fd56fcfb87587a.
def localCycle00033 : Cycle where
  length := 3
  data := {
    node := ![.distance 5 6, .distance 1 6, .distance 1 5, .distance 5 6]
    constant := ![0, -3, 2]
    coefficient := ![0, 0, 0]
    strict := ![false, false, true] }
  origin := ![.gapLower 6 3, .gapLower 1 4, .gapUpper 5 3]

-- Cycle fingerprint 2edc48a4357e3a5ff0aa1c91d872e420a796484e2408a4bfc5cbb623165c5ade.
def localCycle00034 : Cycle where
  length := 8
  data := {
    node := ![.distance 4 5, .distance 3 4, .theta 3, .theta 2, .theta 1, .distance 1 3, .distance 1 6, .distance 1 4, .distance 4 5]
    constant := ![-1, -1, 0, 0, 2, 0, -2, -1]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![false, false, true, true, false, true, false, false] }
  origin := ![.triangle 31 0, .corridorLower 3 4, .thetaNext 2, .thetaNext 1, .gapLower 1 6, .triangle 21 2, .gapLower 1 4, .triangle 22 0]

-- Cycle fingerprint 2eeb717854d5534f136cafd416abc919a61db05b565fc8290a620ce26497f572.
def localCycle00035 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 1 4, .distance 1 5, .distance 0 1, .theta 1, .zero]
    constant := ![0, 3, 0, -1, -2, -1, -2, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 23 0, .gapLower 1 3, .triangle 3 0, .gapLower 1 0, .thetaLower 1]

-- Cycle fingerprint 31271dcf2c599d96a6f58c2f10cf7d4e65529e765fde75450b6c62ea34c77f84.
def localCycle00036 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 2, .distance 1 5, .distance 5 6, .distance 4 6, .distance 3 4, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, -1, 0, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false, false, true] }
  origin := ![.corridorUpper 2 3, .triangle 15 0, .triangle 17 2, .triangle 24 0, .triangle 34 2, .triangle 32 0, .triangle 31 0, .corridorLower 4 5, .thetaNext 3]

-- Cycle fingerprint 317c0d6fd70879b3aac3881c967a6aa2667d292c0f76d758e96b0a4d6ccdaf66.
def localCycle00037 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 3, .distance 2 3, .distance 2 5, .distance 5 6, .distance 1 5, .distance 1 4, .distance 1 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, -1, -1, 0, -2, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 3, .corridorUpper 2 3, .triangle 26 2, .triangle 30 0, .triangle 24 0, .gapLower 1 3, .gapLower 1 2, .triangle 0 0, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint 34364e4ba94950a7972409379e7046a5157dd4fd063b51fa161c084eddfda54e.
def localCycle00038 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 2, .distance 1 4, .distance 4 6, .distance 3 4, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, -1, 0, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, true] }
  origin := ![.corridorUpper 2 3, .triangle 15 0, .triangle 16 2, .triangle 23 0, .triangle 32 0, .triangle 31 0, .corridorLower 4 5, .thetaNext 3]

-- Cycle fingerprint 349c8ebd262bab22065838587466fa9b7a1765a383b0ead08762cb083e3b8c0b.
def localCycle00039 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 2, .distance 2 4, .distance 2 5, .distance 5 6, .distance 3 5, .theta 3]
    constant := ![3, -1, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 0, .triangle 16 0, .triangle 28 2, .triangle 30 0, .triangle 33 0, .corridorLower 3 5]

-- Cycle fingerprint 34b89bd70f187ab925b8ccf3584cd5b9c4fc4cffeaf3a4656122aad707b210e2.
def localCycle00040 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 3, .distance 2 3, .distance 1 3, .distance 1 4, .distance 1 6, .distance 0 1, .theta 1, .zero]
    constant := ![0, 3, 0, 0, -2, -1, -2, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, false] }
  origin := ![.thetaUpper 3, .corridorUpper 2 3, .triangle 15 2, .triangle 19 2, .gapLower 1 4, .triangle 4 0, .gapLower 1 0, .thetaLower 1]

-- Cycle fingerprint 3600fbde3158584c6067c07ab1376dbfe2829ac2fa040d9f0a4325e1d7918ce7.
def localCycle00041 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 2 3, .distance 2 4, .distance 4 6, .distance 0 4, .distance 4 5, .distance 3 4, .theta 3]
    constant := ![3, 0, -1, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 25 2, .triangle 29 0, .triangle 13 0, .triangle 12 0, .triangle 31 0, .corridorLower 3 4]

-- Cycle fingerprint 3678b1864356315f827eb246c2c6ad571f156f862dcb9e262e92e7b42146a802.
def localCycle00042 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 3, .distance 1 5, .distance 1 6, .distance 1 4, .distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 1 3]
    constant := ![0, -2, -2, -1, -1, 0, 0, 3, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![true, false, false, false, false, false, false, false, true] }
  origin := ![.triangle 20 2, .gapLower 1 4, .gapLower 1 3, .triangle 2 0, .corridorLower 0 1, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 15 2]

-- Cycle fingerprint 382be7c2862699b4466a51eaf44f596802386b10da64da92ee94e3d73a812252.
def localCycle00043 : Cycle where
  length := 10
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 2, .distance 1 4, .distance 1 5, .distance 5 6, .distance 4 6, .distance 2 4, .distance 4 5, .distance 3 4, .theta 3]
    constant := ![3, -1, 0, 0, -1, 0, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, true, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 0, .triangle 16 2, .triangle 22 2, .triangle 24 0, .triangle 34 2, .triangle 29 0, .triangle 28 0, .triangle 31 0, .corridorLower 3 4]

-- Cycle fingerprint 39966a7431844e21297b590634b941ccf0732fe0dc47a18800366a4e09f410a7.
def localCycle00044 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 2 4, .distance 4 6, .distance 5 6, .distance 1 5, .distance 1 4, .distance 1 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, -1, -1, 0, -1, 0, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, true, true, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 28 0, .triangle 29 0, .triangle 34 1, .triangle 24 0, .triangle 22 1, .triangle 16 1, .triangle 0 0, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint 3bdb2d339558ba52902d4e4916654fc9e3370fc341b1326bf3eb6f9d3555f1f5.
def localCycle00045 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 2, .distance 2 6, .distance 4 6, .distance 0 4, .distance 4 5, .distance 3 4, .theta 3]
    constant := ![3, -1, -1, 0, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 0, .triangle 18 0, .triangle 29 1, .triangle 13 0, .triangle 12 0, .triangle 31 0, .corridorLower 3 4]

-- Cycle fingerprint 3dbe551122f8947322f827df98068866c44f1067cdba1c21cf383ef2ed742ac8.
def localCycle00046 : Cycle where
  length := 9
  data := {
    node := ![.distance 2 4, .distance 1 2, .distance 0 1, .theta 1, .theta 0, .zero, .theta 6, .distance 5 6, .distance 4 6, .distance 2 4]
    constant := ![-1, -2, -2, 0, 0, 0, 3, 0, -1]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, true, false, false, false, true, false] }
  origin := ![.triangle 16 0, .gapLower 1 1, .gapLower 1 0, .thetaNext 0, .thetaLower 0, .thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 29 0]

-- Cycle fingerprint 3e28aaf952864c95b314c4518e0020d555de7e51041b7098911ae5ecf662ed11.
def localCycle00047 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 2, .distance 2 5, .distance 5 6, .distance 3 5, .distance 3 4, .theta 3]
    constant := ![3, -1, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 0, .triangle 17 0, .triangle 30 0, .triangle 33 0, .gapLower 3 1, .corridorLower 3 4]

-- Cycle fingerprint 3f35071fcff8f20a13a70171281920e220a3e3d2d7e44085e84915efae703c52.
def localCycle00048 : Cycle where
  length := 8
  data := {
    node := ![.distance 3 5, .distance 3 4, .theta 3, .distance 2 3, .distance 1 3, .distance 1 5, .distance 1 6, .distance 5 6, .distance 3 5]
    constant := ![0, -1, 3, 0, -2, -2, 0, -1]
    coefficient := ![0, 0, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, true, false] }
  origin := ![.gapLower 3 1, .corridorLower 3 4, .corridorUpper 2 3, .triangle 15 2, .gapLower 1 5, .gapLower 1 4, .triangle 24 1, .triangle 33 0]

-- Cycle fingerprint 3f645229545b535da44110af80b4a256a6c85c94b1752210bf1c082f69cb5bdd.
def localCycle00049 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 2 4, .distance 2 5, .distance 5 6, .distance 4 5, .distance 0 4, .distance 3 4, .theta 3]
    constant := ![3, 0, 0, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, false, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 25 2, .triangle 28 2, .triangle 30 0, .triangle 34 0, .triangle 12 0, .triangle 9 1, .corridorLower 3 4]

-- Cycle fingerprint 3fce33f0a4ef6d2ed42b85353910300024b71bce38fe09901120ece5ccf5628b.
def localCycle00050 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 2, .distance 2 4, .distance 4 5, .distance 5 6, .distance 3 5, .distance 3 4, .theta 3]
    constant := ![3, -1, -1, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 0, .triangle 16 0, .triangle 28 0, .triangle 34 0, .triangle 33 0, .gapLower 3 1, .corridorLower 3 4]

-- Cycle fingerprint 404de070340ec40b7a4cd37f78e8f0f1836e33523357d30c8c9ba1606882d740.
def localCycle00051 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 3, .distance 1 5, .distance 5 6, .distance 3 6, .distance 0 3, .distance 3 5, .distance 3 4, .theta 3]
    constant := ![3, 0, 0, -1, 0, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, false, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 2, .triangle 20 2, .triangle 24 0, .triangle 33 2, .triangle 11 0, .triangle 10 0, .triangle 31 1, .corridorLower 3 4]

-- Cycle fingerprint 411bb848c1571330bbc646902b448a1104ce9740c0f10f6f800b41893d7e5309.
def localCycle00052 : Cycle where
  length := 11
  data := {
    node := ![.distance 2 3, .distance 2 4, .distance 4 6, .distance 4 5, .distance 1 4, .distance 1 2, .distance 0 1, .theta 1, .theta 0, .zero, .theta 3, .distance 2 3]
    constant := ![0, -1, 0, -1, 0, -1, -3, 0, 0, 0, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1]
    strict := ![true, false, true, false, false, false, false, true, false, false, false] }
  origin := ![.triangle 25 2, .triangle 29 0, .triangle 34 1, .triangle 22 0, .gapLower 1 2, .triangle 0 0, .gapLower 1 0, .thetaNext 0, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3]

-- Cycle fingerprint 4219a05814635ce89b578de91f2aa1774cf5e20f83fbe3ce05e9b33ec356378d.
def localCycle00053 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 2, .distance 2 4, .distance 3 4, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, true] }
  origin := ![.corridorUpper 2 3, .triangle 15 0, .triangle 16 0, .triangle 25 1, .triangle 31 0, .corridorLower 4 5, .thetaNext 3]

-- Cycle fingerprint 4242f0c32e621a8022bf520efd336dcb0063ebfbecd3283f09a05db97c956177.
def localCycle00054 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 2, .distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 1 3, .distance 1 5, .distance 1 6, .distance 1 4, .distance 1 2]
    constant := ![-1, -1, 0, 0, 3, 0, 0, 0, -2, -2]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, true, false, false] }
  origin := ![.triangle 0 0, .corridorLower 0 1, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 15 2, .triangle 20 2, .triangle 24 2, .gapLower 1 3, .gapLower 1 2]

-- Cycle fingerprint 43f41b60f071f25d4e66ab50d22544c3aeeeb989f02e5e2acec438f1edd59c1b.
def localCycle00055 : Cycle where
  length := 10
  data := {
    node := ![.theta 0, .zero, .theta 3, .distance 2 3, .distance 2 4, .distance 4 6, .distance 4 5, .distance 1 4, .distance 1 2, .distance 0 1, .theta 0]
    constant := ![0, 0, 3, 0, -1, 0, -1, 0, -3, -1]
    coefficient := ![0, 1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true, false, false, false, false] }
  origin := ![.thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 25 2, .triangle 29 0, .triangle 34 1, .triangle 22 0, .gapLower 1 2, .gapLower 1 1, .corridorLower 0 1]

-- Cycle fingerprint 463200040bd54650e4b399dfece2397dbe8ae999f30c35b2dcd443fe9cc7f846.
def localCycle00056 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 2 4, .distance 4 6, .distance 4 5, .distance 1 4, .distance 1 2, .distance 0 1]
    constant := ![-1, 0, 0, 3, 0, -1, 0, -1, -2, -2]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, true, false, false, false] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 25 2, .triangle 29 0, .triangle 34 1, .triangle 22 0, .gapLower 1 2, .gapLower 1 1]

-- Cycle fingerprint 48cb26c1e574bdacc6618f9fbeef48cf9523825f9a45966c74e78bd252554d01.
def localCycle00057 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 2 4, .distance 1 2, .distance 0 1, .theta 1, .theta 0, .zero]
    constant := ![0, 3, -1, -1, -2, -2, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 28 0, .triangle 16 0, .gapLower 1 1, .gapLower 1 0, .thetaNext 0, .thetaLower 0]

-- Cycle fingerprint 4b5dd22ad1b5c11f1669ccc483c98535c32d44ca4e183bd1ca6b50737df98e56.
def localCycle00058 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 2, .distance 2 4, .distance 4 6, .distance 4 5, .distance 3 4, .theta 3]
    constant := ![3, -1, -1, -1, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 0, .triangle 16 0, .triangle 29 0, .triangle 34 1, .triangle 31 0, .corridorLower 3 4]

-- Cycle fingerprint 4b829822598ea7d6413eb2eee505522387e7571441516d554de07fb8f4b73e31.
def localCycle00059 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 2, .distance 1 4, .distance 4 5, .distance 2 4, .distance 4 6, .distance 3 4, .theta 3]
    constant := ![4, -1, 0, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false] }
  origin := ![.gapLower 3 6, .triangle 15 0, .triangle 16 2, .triangle 22 0, .triangle 28 0, .triangle 29 0, .triangle 32 0, .gapLower 3 0]

-- Cycle fingerprint 4b9a3f191ce618cb30a6a7870e3dcb2f9f57576a3c1902a3c0bd43fe919a3cc0.
def localCycle00060 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 5, .distance 2 4, .distance 1 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 0, .triangle 28 0, .triangle 16 0, .triangle 0 0, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint 4c3a4f8f1142b0282d9f13984be4a5807475b3d3a5d73376461b9d37f12b8c57.
def localCycle00061 : Cycle where
  length := 5
  data := {
    node := ![.distance 1 2, .distance 1 5, .distance 5 6, .distance 4 6, .distance 2 4, .distance 1 2]
    constant := ![0, 2, 0, -1, -1]
    coefficient := ![0, 0, 0, 0, 0]
    strict := ![true, true, true, false, false] }
  origin := ![.triangle 17 2, .gapUpper 5 5, .triangle 34 2, .triangle 29 0, .triangle 16 0]

-- Cycle fingerprint 4fd67bd43b2ec81d1d0b81a30851f61fc7a6b6242498198449bc4f6d9860fd89.
def localCycle00062 : Cycle where
  length := 10
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 2, .distance 1 5, .distance 1 4, .distance 4 6, .distance 3 6, .distance 0 3, .distance 3 5, .distance 3 4, .theta 3]
    constant := ![3, -1, 0, 0, -1, 0, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, true, false, false, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 0, .triangle 17 2, .triangle 22 1, .triangle 23 0, .triangle 32 2, .triangle 11 0, .triangle 10 0, .triangle 31 1, .corridorLower 3 4]

-- Cycle fingerprint 50049a39a11dc73249b0d67c763ee42fbdd4a4059b5b4943143ea16e0550609d.
def localCycle00063 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 2 5, .distance 1 5, .distance 1 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, -1, 0, -2, -2, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 30 0, .triangle 17 2, .gapLower 1 2, .gapLower 1 1, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint 50868a204e56eb51ce3b0d4f6c92cd2b5f5c49daefe7cf23fbe61293465ec561.
def localCycle00064 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 2, .distance 2 5, .distance 2 4, .distance 4 6, .distance 3 4, .theta 3]
    constant := ![3, -1, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 0, .triangle 17 0, .triangle 28 1, .triangle 29 0, .triangle 32 0, .corridorLower 3 4]

-- Cycle fingerprint 51a840e6711260f4d07bb221acba27c68d815316b774b95ec8ee3bbb2517df2f.
def localCycle00065 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 2, .distance 2 6, .distance 5 6, .distance 4 5, .distance 3 4, .theta 3]
    constant := ![3, -1, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 0, .triangle 18 0, .triangle 30 1, .triangle 34 0, .triangle 31 0, .corridorLower 3 4]

-- Cycle fingerprint 53025ec84d13af688cacc24536731a8140acd17911f12c724efecadaa8b79a1c.
def localCycle00066 : Cycle where
  length := 3
  data := {
    node := ![.distance 2 4, .distance 1 4, .distance 1 2, .distance 2 4]
    constant := ![0, -3, 2]
    coefficient := ![0, 0, 0]
    strict := ![false, false, true] }
  origin := ![.gapLower 4 3, .gapLower 1 2, .gapUpper 2 2]

-- Cycle fingerprint 54ca3878f49c2bd843547607fa2cb44ba4a02d6a7a200b2f34d8fdb8385c02ca.
def localCycle00067 : Cycle where
  length := 9
  data := {
    node := ![.distance 2 3, .distance 1 3, .distance 1 6, .distance 1 5, .distance 1 2, .distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3]
    constant := ![0, -2, 0, -2, -1, -1, 0, 0, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1, 1]
    strict := ![true, false, true, false, false, false, false, false, false] }
  origin := ![.triangle 15 2, .gapLower 1 5, .triangle 24 1, .gapLower 1 2, .triangle 0 0, .corridorLower 0 1, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3]

-- Cycle fingerprint 5665f0680b4c18da8e8e80fb05905da9c237343259a8371ef17c7db361a6e497.
def localCycle00068 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 2, .distance 0 1, .theta 0, .zero, .theta 6, .distance 5 6, .distance 2 5, .distance 1 2]
    constant := ![-3, -1, 0, 0, 3, -1, -1]
    coefficient := ![0, 0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 1 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 6, .corridorUpper 5 6, .triangle 30 0, .triangle 17 0]

-- Cycle fingerprint 59ef1363cb88e534cac0e8717614233a8facba2850064af0f29822c6cf8f9e76.
def localCycle00069 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 3, .distance 1 4, .distance 4 6, .distance 4 5, .distance 3 4, .theta 3, .distance 2 3, .distance 1 3]
    constant := ![-3, -1, 0, -1, -1, 3, 0]
    coefficient := ![0, 0, 0, 0, 0, 1, 0]
    strict := ![false, false, true, false, false, false, true] }
  origin := ![.gapLower 1 5, .triangle 23 0, .triangle 34 1, .triangle 31 0, .corridorLower 3 4, .corridorUpper 2 3, .triangle 15 2]

-- Cycle fingerprint 5b628ac9fbdb5c5ad14bfc6d8de2e50ae381072ef29b66c9a90ad7f96780ceee.
def localCycle00070 : Cycle where
  length := 9
  data := {
    node := ![.distance 5 6, .distance 1 5, .distance 1 4, .distance 0 1, .theta 1, .zero, .theta 3, .distance 2 3, .distance 2 5, .distance 5 6]
    constant := ![-1, -2, -1, -2, 0, 0, 3, 0, -1]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, false, false, false, false, true, false] }
  origin := ![.triangle 24 0, .gapLower 1 3, .triangle 2 0, .gapLower 1 0, .thetaLower 1, .thetaUpper 3, .corridorUpper 2 3, .triangle 26 2, .triangle 30 0]

-- Cycle fingerprint 5b80780e43bb33a5d2934883fcb9e215b4faf3846b2c7c67f4a1c2ab2151a779.
def localCycle00071 : Cycle where
  length := 10
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 2, .distance 1 4, .distance 1 5, .distance 5 6, .distance 4 6, .distance 3 4, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, -1, 0, 0, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, true, false, false, false, true] }
  origin := ![.corridorUpper 2 3, .triangle 15 0, .triangle 16 2, .triangle 22 2, .triangle 24 0, .triangle 34 2, .triangle 32 0, .triangle 31 0, .corridorLower 4 5, .thetaNext 3]

-- Cycle fingerprint 5c5367aaaf1419471bec796187428314b600a8a384eb125ae1de49b97e815142.
def localCycle00072 : Cycle where
  length := 9
  data := {
    node := ![.distance 2 3, .distance 1 3, .distance 1 6, .distance 1 5, .distance 1 4, .distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3]
    constant := ![0, -2, 0, -2, -1, -1, 0, 0, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1, 1]
    strict := ![true, false, true, false, false, false, false, false, false] }
  origin := ![.triangle 15 2, .gapLower 1 5, .triangle 24 1, .gapLower 1 3, .triangle 2 0, .corridorLower 0 1, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3]

-- Cycle fingerprint 5cebe3085ab102e307fb7056b87a87ead10716ce946ce0cb771bdb63f7b3e3ba.
def localCycle00073 : Cycle where
  length := 9
  data := {
    node := ![.distance 4 6, .distance 1 6, .distance 1 5, .distance 0 5, .distance 3 5, .distance 3 4, .theta 3, .distance 2 3, .distance 2 4, .distance 4 6]
    constant := ![0, -3, 0, 0, 0, -1, 3, 0, -1]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 0, 0]
    strict := ![true, false, true, true, true, false, false, true, false] }
  origin := ![.triangle 23 2, .gapLower 1 4, .triangle 3 2, .triangle 10 1, .triangle 31 1, .corridorLower 3 4, .corridorUpper 2 3, .triangle 25 2, .triangle 29 0]

-- Cycle fingerprint 5d2ed30427ede6e467b8913650b597f558782b5a058c84265a3d587a88f1a692.
def localCycle00074 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .theta 1, .distance 1 3, .distance 1 4, .distance 1 6, .distance 1 5, .distance 4 5, .distance 3 4, .theta 3, .theta 2]
    constant := ![0, 2, 0, 0, -2, 0, -1, -1, 0]
    coefficient := ![0, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![true, false, true, true, false, true, false, false, true] }
  origin := ![.thetaNext 1, .gapLower 1 6, .triangle 19 2, .triangle 23 2, .gapLower 1 3, .triangle 22 1, .triangle 31 0, .corridorLower 3 4, .thetaNext 2]

-- Cycle fingerprint 5d7f4e756e9fd7859a54bd06455bef218d84c94aabfa0718092ece6c4ae36417.
def localCycle00075 : Cycle where
  length := 5
  data := {
    node := ![.distance 1 6, .distance 1 5, .distance 1 4, .theta 1, .distance 1 3, .distance 1 6]
    constant := ![0, -2, -1, 2, 0]
    coefficient := ![0, 0, 0, 1, 0]
    strict := ![true, false, false, false, true] }
  origin := ![.triangle 24 1, .gapLower 1 3, .corridorLower 1 4, .gapLower 1 6, .triangle 21 2]

-- Cycle fingerprint 5d92d0c872c85b5f1d9f7b8f22cb84616a5034a416db0829118489a91053ceb1.
def localCycle00076 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 3, .distance 1 6, .distance 1 4, .distance 4 5, .distance 3 4, .theta 3, .distance 2 3, .distance 1 3]
    constant := ![-2, 0, -1, -1, -1, 3, 0]
    coefficient := ![0, 0, 0, 0, 0, 1, 0]
    strict := ![false, true, false, false, false, false, true] }
  origin := ![.gapLower 1 5, .triangle 23 1, .triangle 22 0, .triangle 31 0, .corridorLower 3 4, .corridorUpper 2 3, .triangle 15 2]

-- Cycle fingerprint 5ef8715d8ad860a65347baa69f2d44fbfa21cf76eefeec486638694418cf72b7.
def localCycle00077 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 5 6, .distance 2 6, .distance 1 2, .distance 2 5, .distance 2 4, .distance 0 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, -1, 0, -1, -1, 0, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, true, false, true, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 34 0, .triangle 30 2, .triangle 18 0, .triangle 17 0, .triangle 28 1, .triangle 6 0, .triangle 0 1, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint 6051babad9d38b4b3686ca4d09b4a7b68e6895f016c93f851517e794a85a6d04.
def localCycle00078 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 3 6, .distance 2 3, .distance 1 2, .distance 2 4, .distance 4 5, .distance 3 4, .theta 3]
    constant := ![4, -1, -1, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 3 6, .triangle 27 0, .triangle 15 0, .triangle 16 0, .triangle 28 0, .triangle 31 0, .corridorLower 3 4]

-- Cycle fingerprint 6094f8fe029613e367e61206372f3d5afd207f912556146ecc155e9fc2701946.
def localCycle00079 : Cycle where
  length := 10
  data := {
    node := ![.distance 2 4, .distance 4 6, .distance 4 5, .distance 1 4, .distance 1 2, .distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 2 4]
    constant := ![-1, 0, -1, 0, -2, -1, 0, 0, 3, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![false, true, false, false, false, false, false, false, false, true] }
  origin := ![.triangle 29 0, .triangle 34 1, .triangle 22 0, .gapLower 1 2, .gapLower 1 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 25 2]

-- Cycle fingerprint 61c85fba578da37f371886f318bb87800286060c3edeaeb47871cdef18ac9ce7.
def localCycle00080 : Cycle where
  length := 8
  data := {
    node := ![.theta 0, .zero, .theta 3, .distance 2 3, .distance 1 3, .distance 1 6, .distance 1 5, .distance 0 1, .theta 0]
    constant := ![0, 0, 3, 0, -2, -2, -1, -1]
    coefficient := ![0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, false] }
  origin := ![.thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 15 2, .gapLower 1 5, .gapLower 1 4, .triangle 3 0, .corridorLower 0 1]

-- Cycle fingerprint 63f39235b039b48e87fa20faba49ef8f165f29390be48767c6a34286a0a2cae6.
def localCycle00081 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 2 3, .distance 1 2, .distance 2 4, .distance 3 4, .distance 4 5, .theta 4, .zero]
    constant := ![0, 3, 0, 0, -1, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, true, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 27 0, .triangle 15 0, .triangle 16 0, .triangle 25 1, .triangle 31 0, .corridorLower 4 5, .thetaLower 4]

-- Cycle fingerprint 649edb8d9f099b186c54547312900a32b758ac9dd3e76ec11f5a2ca245d58084.
def localCycle00082 : Cycle where
  length := 11
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 2, .distance 1 4, .distance 1 5, .distance 5 6, .distance 4 6, .distance 2 4, .distance 0 4, .distance 4 5, .distance 3 4, .theta 3]
    constant := ![3, -1, 0, 0, -1, 0, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, true, false, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 0, .triangle 16 2, .triangle 22 2, .triangle 24 0, .triangle 34 2, .triangle 29 0, .gapLower 4 3, .triangle 12 0, .triangle 31 0, .corridorLower 3 4]

-- Cycle fingerprint 680c2751dd2fe91a73b09949334e398a1671f14aa2fb33d069de1e363d106990.
def localCycle00083 : Cycle where
  length := 3
  data := {
    node := ![.distance 2 5, .distance 1 5, .distance 1 2, .distance 2 5]
    constant := ![0, -3, 2]
    coefficient := ![0, 0, 0]
    strict := ![false, false, true] }
  origin := ![.gapLower 5 4, .gapLower 1 2, .gapUpper 2 2]

-- Cycle fingerprint 689933f21650a3279be051b93984332da361b639393c381a8c917b254d52dcf8.
def localCycle00084 : Cycle where
  length := 8
  data := {
    node := ![.distance 3 4, .theta 3, .distance 2 3, .distance 1 3, .distance 1 6, .distance 1 4, .distance 1 5, .distance 4 5, .distance 3 4]
    constant := ![-1, 3, 0, 0, -2, -2, 0, -1]
    coefficient := ![0, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, true, false] }
  origin := ![.corridorLower 3 4, .corridorUpper 2 3, .triangle 15 2, .triangle 21 2, .gapLower 1 4, .gapLower 1 3, .triangle 22 1, .triangle 31 0]

-- Cycle fingerprint 6a1864bef040aee89c04787d7bb11d74c68e37fd3016cf98a071d9f28af07a1c.
def localCycle00085 : Cycle where
  length := 8
  data := {
    node := ![.theta 6, .distance 5 6, .distance 4 6, .distance 2 4, .distance 1 2, .distance 0 1, .theta 0, .zero, .theta 6]
    constant := ![3, 0, -1, -1, -3, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, false, false, false, false, false, false] }
  origin := ![.corridorUpper 5 6, .triangle 34 2, .triangle 29 0, .triangle 16 0, .gapLower 1 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 6]

-- Cycle fingerprint 6b2840d655a81fed5add690a5352fc6083acad6a368d58b263fccd5a1362ee02.
def localCycle00086 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 3, .distance 2 3, .distance 1 3, .distance 1 5, .distance 1 6, .distance 0 1, .theta 1, .zero]
    constant := ![0, 3, 0, 0, -2, -1, -2, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, false] }
  origin := ![.thetaUpper 3, .corridorUpper 2 3, .triangle 15 2, .triangle 20 2, .gapLower 1 4, .triangle 4 0, .gapLower 1 0, .thetaLower 1]

-- Cycle fingerprint 6b7e3d0ca0709f0da62fac9d4f618ed40608f4ea63cd5e8cf24eb3249d936bf6.
def localCycle00087 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 6, .distance 0 3, .distance 3 4, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true] }
  origin := ![.corridorUpper 2 3, .triangle 27 0, .triangle 11 0, .triangle 9 0, .triangle 31 0, .corridorLower 4 5, .thetaNext 3]

-- Cycle fingerprint 6bfa210fd0d2ed852094251aac41b23d392f42768ede3c16c849cc99ba86003c.
def localCycle00088 : Cycle where
  length := 8
  data := {
    node := ![.distance 4 6, .distance 3 4, .theta 3, .theta 2, .theta 1, .distance 1 3, .distance 1 4, .distance 1 6, .distance 4 6]
    constant := ![-1, -1, 0, 0, 2, 0, -2, 0]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![false, false, true, true, false, true, false, true] }
  origin := ![.triangle 32 0, .corridorLower 3 4, .thetaNext 2, .thetaNext 1, .gapLower 1 6, .triangle 19 2, .gapLower 1 4, .triangle 23 1]

-- Cycle fingerprint 6d04c4ea559581ae30b8c363a1b8887db00a3ecea9969084565430a5b9599da1.
def localCycle00089 : Cycle where
  length := 8
  data := {
    node := ![.distance 3 5, .distance 3 4, .theta 3, .theta 2, .theta 1, .distance 1 3, .distance 1 5, .distance 5 6, .distance 3 5]
    constant := ![0, -1, 0, 0, 2, -2, -1, -1]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, false] }
  origin := ![.gapLower 3 1, .corridorLower 3 4, .thetaNext 2, .thetaNext 1, .gapLower 1 6, .gapLower 1 5, .triangle 24 0, .triangle 33 0]

-- Cycle fingerprint 6d83ccabe2fc2b444e831be17fa95ef31ce72a091c580abf41e0232afff12732.
def localCycle00090 : Cycle where
  length := 3
  data := {
    node := ![.distance 4 6, .distance 1 4, .distance 1 6, .distance 4 6]
    constant := ![2, -3, 0]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.gapUpper 4 4, .gapLower 1 4, .triangle 23 1]

-- Cycle fingerprint 6da671d9086a82c813da16a4650b4a1c9d7f8700a6525e5e6c250831d58cbe60.
def localCycle00091 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 2, .distance 2 6, .distance 2 4, .distance 4 5, .distance 3 4, .theta 3]
    constant := ![3, -1, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 0, .triangle 18 0, .triangle 29 1, .triangle 28 0, .triangle 31 0, .corridorLower 3 4]

-- Cycle fingerprint 6f66c6a8f9db808833f0754ae93cfa2861703f14fef2942057cae961f6ec3e42.
def localCycle00092 : Cycle where
  length := 8
  data := {
    node := ![.distance 4 5, .distance 3 4, .theta 3, .theta 2, .theta 1, .distance 1 3, .distance 1 4, .distance 4 6, .distance 4 5]
    constant := ![-1, -1, 0, 0, 1, 0, -1, 0]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![false, false, true, true, false, true, false, true] }
  origin := ![.triangle 31 0, .corridorLower 3 4, .thetaNext 2, .thetaNext 1, .gapLower 1 6, .triangle 19 2, .triangle 23 0, .triangle 34 1]

-- Cycle fingerprint 7151450f4eac738b8fbd7281813599e5dc7d2923b2d8d365ca2e27ec84129e75.
def localCycle00093 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 2, .distance 2 6, .distance 5 6, .distance 3 5, .distance 3 4, .theta 3]
    constant := ![3, -1, -1, 0, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 0, .triangle 18 0, .triangle 30 1, .triangle 33 0, .triangle 31 1, .corridorLower 3 4]

-- Cycle fingerprint 720b7293df6542c5ce01e995317d8ea59d8e96c64df34e81da474a7eb39e6bd3.
def localCycle00094 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 3, .distance 3 6, .distance 0 3, .distance 3 4, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, 0, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false, true] }
  origin := ![.corridorUpper 2 3, .triangle 15 2, .triangle 21 0, .triangle 11 0, .triangle 9 0, .triangle 31 0, .corridorLower 4 5, .thetaNext 3]

-- Cycle fingerprint 732be887b54820cd414fe70975a0b4894ce975bc003cba0bb17ec170d9b8c155.
def localCycle00095 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 2, .distance 2 5, .distance 5 6, .distance 4 5, .distance 3 4, .theta 3]
    constant := ![3, -1, -1, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 0, .triangle 17 0, .triangle 30 0, .triangle 34 0, .triangle 31 0, .corridorLower 3 4]

-- Cycle fingerprint 73bc42003671aa0d62bb754e765911b34899ee2c8035d4cad1cfb77408148e68.
def localCycle00096 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 2 5, .distance 5 6, .distance 3 6, .distance 0 3, .distance 3 5, .distance 3 4, .theta 3]
    constant := ![3, 0, -1, 0, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 26 2, .triangle 30 0, .triangle 33 2, .triangle 11 0, .triangle 10 0, .triangle 31 1, .corridorLower 3 4]

-- Cycle fingerprint 73cfbf3ada2b5b66080d536bd53096c394ab535db9702606aa0601c906bf152c.
def localCycle00097 : Cycle where
  length := 4
  data := {
    node := ![.theta 1, .distance 1 3, .distance 1 6, .distance 1 5, .theta 1]
    constant := ![2, 0, -2, -1]
    coefficient := ![1, 0, 0, 0]
    strict := ![false, true, false, false] }
  origin := ![.gapLower 1 6, .triangle 21 2, .gapLower 1 4, .corridorLower 1 5]

-- Cycle fingerprint 7f43ef3f1fef2424ba7eaa1b70500360a408de4b4c8b1dff869e4b27b02527d6.
def localCycle00098 : Cycle where
  length := 3
  data := {
    node := ![.distance 4 5, .distance 1 4, .distance 1 5, .distance 4 5]
    constant := ![2, -3, 0]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.gapUpper 4 3, .gapLower 1 3, .triangle 22 1]

-- Cycle fingerprint 8030155a32f6a919eeca98d59cfa75ef631ef344c0e5f7c1bcf9a3321320eff3.
def localCycle00099 : Cycle where
  length := 6
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 2, .distance 2 5, .distance 4 5, .distance 3 4, .theta 3]
    constant := ![3, -1, -1, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 0, .triangle 17 0, .triangle 28 1, .triangle 31 0, .corridorLower 3 4]

-- Cycle fingerprint 82c356938f38be75652a4625c1c373b80efafcacd6ea871422597613875e5ae4.
def localCycle00100 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 5, .distance 4 5, .distance 1 4, .distance 1 2, .distance 0 1]
    constant := ![-1, 0, 0, 3, -1, -2, -1]
    coefficient := ![0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 5, .corridorUpper 4 5, .triangle 22 0, .gapLower 1 2, .triangle 0 0]

-- Cycle fingerprint 83a1b812e8b59fb7b282eafdfa8a5f7fbeeeccf25a2597f00e5542056c84c252.
def localCycle00101 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .theta 1, .distance 1 3, .distance 1 5, .distance 1 6, .distance 5 6, .distance 3 5, .distance 3 4, .theta 3, .theta 2]
    constant := ![0, 2, 0, -2, 0, -1, 0, -1, 0]
    coefficient := ![0, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![true, false, true, false, true, false, false, false, true] }
  origin := ![.thetaNext 1, .gapLower 1 6, .triangle 20 2, .gapLower 1 4, .triangle 24 1, .triangle 33 0, .gapLower 3 1, .corridorLower 3 4, .thetaNext 2]

-- Cycle fingerprint 83d3184bd2dff112cb402d98372e1b533ca9661d877963c4825ca62ae46823cd.
def localCycle00102 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 2, .distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 1 3, .distance 1 4, .distance 1 6, .distance 1 5, .distance 1 2]
    constant := ![-1, -1, 0, 0, 3, 0, 0, 0, -2, -2]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, true, false, false] }
  origin := ![.triangle 0 0, .corridorLower 0 1, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 15 2, .triangle 19 2, .triangle 23 2, .gapLower 1 3, .gapLower 1 2]

-- Cycle fingerprint 84dbd38d61fc03413c7160d159f37e8710f21e5f47cdb1de76142dbd91d4d8cd.
def localCycle00103 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 3, .distance 1 4, .distance 1 6, .distance 1 2, .distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 1 3]
    constant := ![0, -2, 0, -2, -1, 0, 0, 3, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![true, false, true, false, false, false, false, false, true] }
  origin := ![.triangle 19 2, .gapLower 1 4, .triangle 18 1, .gapLower 1 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 15 2]

-- Cycle fingerprint 84f2a295c0ea2586747b54bcf7f2fb732be7421bedff4a978b861b4a6e4e244e.
def localCycle00104 : Cycle where
  length := 8
  data := {
    node := ![.distance 4 5, .distance 3 4, .theta 3, .distance 2 3, .distance 1 3, .distance 1 6, .distance 1 4, .distance 1 5, .distance 4 5]
    constant := ![-1, -1, 3, 0, -2, 0, -2, 0]
    coefficient := ![0, 0, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true, false, true] }
  origin := ![.triangle 31 0, .corridorLower 3 4, .corridorUpper 2 3, .triangle 15 2, .gapLower 1 5, .triangle 23 1, .gapLower 1 3, .triangle 22 1]

-- Cycle fingerprint 85e2fede2d4f310a29ac80cbbe1623691bf41df62cad7a0b8e8e67021b5cb630.
def localCycle00105 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 2 3, .distance 2 4, .distance 2 5, .distance 5 6, .distance 4 5, .distance 3 4, .theta 3]
    constant := ![3, 0, 0, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 25 2, .triangle 28 2, .triangle 30 0, .triangle 34 0, .triangle 31 0, .corridorLower 3 4]

-- Cycle fingerprint 86687ee51148f06cf2b189637bcc9b48aee9aa8299cff8456ea783e1980c9a8a.
def localCycle00106 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 3, .distance 1 4, .distance 4 6, .distance 0 4, .distance 4 5, .distance 3 4, .theta 3]
    constant := ![3, 0, 0, -1, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 2, .triangle 19 2, .triangle 23 0, .triangle 13 0, .triangle 12 0, .triangle 31 0, .corridorLower 3 4]

-- Cycle fingerprint 8671a6d07e97431c718efee40d5b8202b7f977b9ab9dea5bb44e424b54456331.
def localCycle00107 : Cycle where
  length := 7
  data := {
    node := ![.theta 6, .distance 5 6, .distance 2 5, .distance 1 2, .distance 0 1, .theta 0, .zero, .theta 6]
    constant := ![3, -1, -1, -2, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 1]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.corridorUpper 5 6, .triangle 30 0, .triangle 17 0, .gapLower 1 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 6]

-- Cycle fingerprint 8829fdecf88db7c5dc4c27fb1fe6776282d2bb0d1b46af7276c2b80a755d0036.
def localCycle00108 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 2, .distance 1 4, .distance 4 6, .distance 2 4, .distance 4 5, .distance 3 4, .theta 3]
    constant := ![3, -1, 0, -1, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 0, .triangle 16 2, .triangle 23 0, .triangle 29 0, .triangle 28 0, .triangle 31 0, .corridorLower 3 4]

-- Cycle fingerprint 887a48e65db2e281349c6b209cc4c6078692857d4a92ea80775004063c940a4c.
def localCycle00109 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 2 4, .distance 1 4, .distance 1 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, -1, 0, -2, -2, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 28 0, .triangle 16 2, .gapLower 1 2, .gapLower 1 1, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint 88871acb6cc7e7a331edce28d4c10dc1e71a16f9f7694c6e5cb8dc5f0e63f15a.
def localCycle00110 : Cycle where
  length := 4
  data := {
    node := ![.distance 1 4, .distance 1 2, .distance 2 5, .distance 4 5, .distance 1 4]
    constant := ![-3, 2, 0, -1]
    coefficient := ![0, 0, 0, 0]
    strict := ![false, true, false, false] }
  origin := ![.gapLower 1 2, .gapUpper 2 2, .gapLower 5 4, .triangle 22 0]

-- Cycle fingerprint 8962e20ae0f3c15bc2e8f27bd3a3e38769967af5c5676573f493b3f5cd3e650d.
def localCycle00111 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 3, .distance 1 6, .distance 1 4, .distance 4 5, .distance 3 4, .theta 3, .distance 2 3, .distance 1 3]
    constant := ![-3, 0, -1, -1, -1, 3, 0]
    coefficient := ![0, 0, 0, 0, 0, 1, 0]
    strict := ![false, true, false, false, false, false, true] }
  origin := ![.gapLower 1 5, .triangle 23 1, .triangle 22 0, .triangle 31 0, .corridorLower 3 4, .corridorUpper 2 3, .triangle 15 2]

-- Cycle fingerprint 8a9443c84a483e7c500b4f1a6ff385d909ab77b6bf7dbd6857919a731d630fe0.
def localCycle00112 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 5, .distance 1 4, .distance 1 2, .distance 0 1, .theta 1, .zero, .theta 3, .distance 2 3, .distance 1 3, .distance 1 6, .distance 1 5]
    constant := ![0, 0, -1, -2, 0, 0, 3, 0, -2, 0]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![true, true, false, false, false, false, false, true, false, true] }
  origin := ![.triangle 22 1, .triangle 16 1, .triangle 0 0, .gapLower 1 0, .thetaLower 1, .thetaUpper 3, .corridorUpper 2 3, .triangle 15 2, .gapLower 1 5, .triangle 24 1]

-- Cycle fingerprint 8b81a1f8a5ac33de67657f2a3c9b2df6e61cc9b3ca5a2bf9a771587733baf0d2.
def localCycle00113 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 2, .distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 1 3, .distance 1 4, .distance 1 6, .distance 1 5, .distance 1 2]
    constant := ![-2, -1, 0, 0, 3, 0, 0, 0, -2, 0]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, true, false, true] }
  origin := ![.gapLower 1 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 15 2, .triangle 19 2, .triangle 23 2, .gapLower 1 3, .triangle 17 1]

-- Cycle fingerprint 8e99ddb6947d25b9043012d5fee6a82e73cdf585c3063b30739900261bfdd335.
def localCycle00114 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 2, .distance 2 5, .distance 4 5, .distance 5 6, .distance 3 5, .distance 3 4, .theta 3]
    constant := ![3, -1, -1, 0, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 0, .triangle 17 0, .triangle 28 1, .triangle 34 0, .triangle 33 0, .gapLower 3 1, .corridorLower 3 4]

-- Cycle fingerprint 8f2067d9da76bbcf422e60e09159afbdcc06d088a7634e0bbdb8f4dc76a900b0.
def localCycle00115 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 6, .distance 1 4, .distance 4 5, .distance 3 4, .theta 3, .distance 2 3, .distance 1 3, .distance 1 6]
    constant := ![-2, -1, -1, -1, 3, 0, 0]
    coefficient := ![0, 0, 0, 0, 1, 0, 0]
    strict := ![false, false, false, false, false, true, true] }
  origin := ![.gapLower 1 4, .triangle 22 0, .triangle 31 0, .corridorLower 3 4, .corridorUpper 2 3, .triangle 15 2, .triangle 21 2]

-- Cycle fingerprint 8f8e5a49f9e55ab9fe46d240c9d9fa36ee467d8d91de34eeaf910c30d33b41be.
def localCycle00116 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 2, .distance 1 4, .distance 4 6, .distance 2 4, .distance 0 4, .distance 4 5, .distance 3 4, .theta 3]
    constant := ![3, -1, 0, -1, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 0, .triangle 16 2, .triangle 23 0, .triangle 29 0, .gapLower 4 3, .triangle 12 0, .triangle 31 0, .corridorLower 3 4]

-- Cycle fingerprint 9168961527df126c219b37eb540464e4c243a958cf00dae3df67d6c16f27b334.
def localCycle00117 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 2, .distance 0 1, .theta 0, .zero, .theta 5, .distance 4 5, .distance 2 4, .distance 1 2]
    constant := ![-3, -1, 0, 0, 3, -1, -1]
    coefficient := ![0, 0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 1 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 5, .corridorUpper 4 5, .triangle 28 0, .triangle 16 0]

-- Cycle fingerprint 93afe1df27f763bd780b8b6c5580f2b6abb2fbfa9b3d08b162856047a924fccd.
def localCycle00118 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 2, .distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 1 3, .distance 1 5, .distance 1 6, .distance 1 4, .distance 1 2]
    constant := ![-2, -1, 0, 0, 3, 0, 0, 0, -2, 0]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, true, false, true] }
  origin := ![.gapLower 1 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 15 2, .triangle 20 2, .triangle 24 2, .gapLower 1 3, .triangle 16 1]

-- Cycle fingerprint 9449d5624757fbb836dc121971b8c03c9b3cd8eb7ea5d54d6e439c489c0a44d3.
def localCycle00119 : Cycle where
  length := 8
  data := {
    node := ![.theta 6, .distance 5 6, .distance 2 5, .distance 1 2, .distance 0 1, .theta 1, .theta 0, .zero, .theta 6]
    constant := ![3, -1, -1, -1, -3, 0, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 1]
    strict := ![false, false, false, false, false, true, false, false] }
  origin := ![.corridorUpper 5 6, .triangle 30 0, .triangle 17 0, .triangle 0 0, .gapLower 1 0, .thetaNext 0, .thetaLower 0, .thetaUpper 6]

-- Cycle fingerprint 95d67239f08f5b0659a31cb606e706d941926e9537c12b18b471a55ba3d8b1bc.
def localCycle00120 : Cycle where
  length := 6
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 2, .distance 2 5, .distance 5 6, .distance 3 5, .theta 3]
    constant := ![3, -1, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 0, .triangle 17 0, .triangle 30 0, .triangle 33 0, .corridorLower 3 5]

-- Cycle fingerprint 97961427ba0737f2cc5c6c2420785c1e60e7ed185f59a1a5c1506d6e1ac7bffe.
def localCycle00121 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 6, .distance 1 4, .distance 4 5, .distance 3 4, .theta 3, .distance 2 3, .distance 1 3, .distance 1 6]
    constant := ![-3, -1, -1, -1, 3, 0, 0]
    coefficient := ![0, 0, 0, 0, 1, 0, 0]
    strict := ![false, false, false, false, false, true, true] }
  origin := ![.gapLower 1 4, .triangle 22 0, .triangle 31 0, .corridorLower 3 4, .corridorUpper 2 3, .triangle 15 2, .triangle 21 2]

-- Cycle fingerprint 97a97a494518cf00afc68ab675d0ef61978b7a75bdfea85fbdef98baba6c2f09.
def localCycle00122 : Cycle where
  length := 9
  data := {
    node := ![.distance 4 6, .distance 1 4, .distance 1 5, .distance 1 2, .distance 0 1, .theta 0, .zero, .theta 6, .distance 5 6, .distance 4 6]
    constant := ![-1, -2, -2, -1, -1, 0, 0, 3, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![false, false, false, false, false, false, false, false, true] }
  origin := ![.triangle 23 0, .gapLower 1 3, .gapLower 1 2, .triangle 0 0, .corridorLower 0 1, .thetaLower 0, .thetaUpper 6, .corridorUpper 5 6, .triangle 34 2]

-- Cycle fingerprint 99347d05d579e6944d25f48e9323bb979ba69b9c00e65259541cce9117ab1661.
def localCycle00123 : Cycle where
  length := 10
  data := {
    node := ![.theta 0, .zero, .theta 3, .distance 2 3, .distance 2 5, .distance 5 6, .distance 1 5, .distance 1 4, .distance 0 1, .theta 1, .theta 0]
    constant := ![0, 0, 3, 0, -1, -1, 0, -1, -3, 0]
    coefficient := ![0, 1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, false, false, true] }
  origin := ![.thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 26 2, .triangle 30 0, .triangle 24 0, .gapLower 1 3, .triangle 2 0, .gapLower 1 0, .thetaNext 0]

-- Cycle fingerprint 994a7646d6a1be00b8f14a3b925b5f879986060143a1308160a8d37ff52d961c.
def localCycle00124 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 2, .distance 2 6, .distance 3 6, .distance 3 4, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, -1, -1, 0, 0, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false, false, true] }
  origin := ![.corridorUpper 2 3, .triangle 15 0, .triangle 18 0, .triangle 27 1, .triangle 32 1, .triangle 31 0, .corridorLower 4 5, .thetaNext 3]

-- Cycle fingerprint 99bb15ef2ecaaff7f11e0b452a2905c69964907899e6de06ad602041e152bcd5.
def localCycle00125 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 4, .distance 1 2, .distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 1 3, .distance 1 5, .distance 1 6, .distance 1 4]
    constant := ![-2, -1, -1, 0, 0, 3, 0, 0, -2, 0]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, true, false, true] }
  origin := ![.gapLower 1 2, .triangle 0 0, .corridorLower 0 1, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 15 2, .triangle 20 2, .gapLower 1 4, .triangle 23 1]

-- Cycle fingerprint 9ab97debb8933da9eee8498c85e61b46c7fc1fc2632c5cc7dc8b6ded9377c73d.
def localCycle00126 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 2, .distance 0 1, .theta 1, .zero, .theta 3, .distance 2 3, .distance 1 3, .distance 1 5, .distance 1 6, .distance 1 4, .distance 1 2]
    constant := ![-1, -2, 0, 0, 3, 0, 0, 0, -2, 0]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, true, false, true] }
  origin := ![.triangle 0 0, .gapLower 1 0, .thetaLower 1, .thetaUpper 3, .corridorUpper 2 3, .triangle 15 2, .triangle 20 2, .triangle 24 2, .gapLower 1 3, .triangle 16 1]

-- Cycle fingerprint 9b68899fd6d83e1a8a3aa51a7cbf28c6f1e8fcab1f05cfaae04ab5d6aae87b59.
def localCycle00127 : Cycle where
  length := 8
  data := {
    node := ![.theta 5, .distance 4 5, .distance 2 4, .distance 1 2, .distance 0 1, .theta 1, .theta 0, .zero, .theta 5]
    constant := ![3, -1, -1, -1, -3, 0, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 1]
    strict := ![false, false, false, false, false, true, false, false] }
  origin := ![.corridorUpper 4 5, .triangle 28 0, .triangle 16 0, .triangle 0 0, .gapLower 1 0, .thetaNext 0, .thetaLower 0, .thetaUpper 5]

-- Cycle fingerprint 9c9cf7b56012bf0f338aeb954602ff5e2aa5024a62d6cd178a5a02cc5b1e0f78.
def localCycle00128 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 2, .distance 1 4, .distance 1 5, .distance 5 6, .distance 4 5, .distance 3 4, .theta 3]
    constant := ![3, -1, 0, 0, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 0, .triangle 16 2, .triangle 22 2, .triangle 24 0, .triangle 34 0, .triangle 31 0, .corridorLower 3 4]

-- Cycle fingerprint 9cf73b6b1ff487ef9b6c1756b14f1f3863bfcf8463087fc6bddaaf2bc7f44162.
def localCycle00129 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 2, .distance 1 5, .distance 5 6, .distance 4 5, .distance 3 4, .theta 3]
    constant := ![3, -1, 0, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 0, .triangle 17 2, .triangle 24 0, .triangle 34 0, .triangle 31 0, .corridorLower 3 4]

-- Cycle fingerprint 9de49c41d9a4fd16242a2e6699a36b8dd77f00504b4e067ac1a80b49217f1165.
def localCycle00130 : Cycle where
  length := 4
  data := {
    node := ![.distance 1 5, .distance 1 4, .distance 1 2, .distance 2 5, .distance 1 5]
    constant := ![-2, -2, 2, 0]
    coefficient := ![0, 0, 0, 0]
    strict := ![false, false, true, true] }
  origin := ![.gapLower 1 3, .gapLower 1 2, .gapUpper 2 2, .triangle 17 2]

-- Cycle fingerprint a0f65ed1bd4fa92ac25e8963c6bb40861e28c44b8bf22c22844906932ab10330.
def localCycle00131 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 2, .distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 2 5, .distance 5 6, .distance 1 5, .distance 1 4, .distance 1 2]
    constant := ![-1, -1, 0, 0, 3, 0, -1, -1, -2, -2]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, false, false, false] }
  origin := ![.triangle 0 0, .corridorLower 0 1, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 26 2, .triangle 30 0, .triangle 24 0, .gapLower 1 3, .gapLower 1 2]

-- Cycle fingerprint a18d3e52b9966216309e19a014a486343d9b119fb7e04b1843d18436f094da2d.
def localCycle00132 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 2, .distance 2 4, .distance 2 5, .distance 5 6, .distance 4 5, .distance 3 4, .theta 3]
    constant := ![3, -1, -1, 0, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 0, .triangle 16 0, .triangle 28 2, .triangle 30 0, .triangle 34 0, .triangle 31 0, .corridorLower 3 4]

-- Cycle fingerprint a3ae5da2cf3666138dd047034e238addf15353aaab9be4be4cd3b9af6e9222de.
def localCycle00133 : Cycle where
  length := 9
  data := {
    node := ![.distance 2 3, .distance 1 3, .distance 1 6, .distance 1 4, .distance 1 2, .distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3]
    constant := ![0, -2, 0, -2, -1, -1, 0, 0, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1, 1]
    strict := ![true, false, true, false, false, false, false, false, false] }
  origin := ![.triangle 15 2, .gapLower 1 5, .triangle 23 1, .gapLower 1 2, .triangle 0 0, .corridorLower 0 1, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3]

-- Cycle fingerprint a5e56bbbad1f20f16506ec73d4492d2568582c5faa3543360c955653e2e6b16e.
def localCycle00134 : Cycle where
  length := 11
  data := {
    node := ![.theta 3, .distance 2 3, .distance 2 4, .distance 4 6, .distance 4 5, .distance 1 4, .distance 1 2, .distance 0 1, .theta 1, .theta 0, .zero, .theta 3]
    constant := ![3, 0, -1, 0, -1, 0, -2, -2, 0, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, false, true, false, false, false, false, true, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 25 2, .triangle 29 0, .triangle 34 1, .triangle 22 0, .gapLower 1 2, .gapLower 1 1, .gapLower 1 0, .thetaNext 0, .thetaLower 0, .thetaUpper 3]

-- Cycle fingerprint a79a1fa115c1dc917a782376f15956c6907e08032796746678f057814a618acc.
def localCycle00135 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 3, .distance 3 6, .distance 0 3, .distance 3 5, .distance 3 4, .theta 3]
    constant := ![3, 0, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 2, .triangle 21 0, .triangle 11 0, .triangle 10 0, .triangle 31 1, .corridorLower 3 4]

-- Cycle fingerprint a9181db7b3c154cfb246cf74f3b0ddc8991c42e11920e155b70b4d1779f27547.
def localCycle00136 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 2 4, .distance 4 6, .distance 1 4, .distance 4 5, .distance 0 4, .distance 3 4, .theta 3]
    constant := ![3, 0, -1, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 25 2, .triangle 29 0, .triangle 23 0, .triangle 22 0, .triangle 12 0, .triangle 9 1, .corridorLower 3 4]

-- Cycle fingerprint aa5d8fc73799c4f6f43937a126a31f7ed78df362071661fecbbc35838eb60c34.
def localCycle00137 : Cycle where
  length := 3
  data := {
    node := ![.distance 5 6, .distance 1 5, .distance 1 6, .distance 5 6]
    constant := ![2, -3, 0]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.gapUpper 5 3, .gapLower 1 4, .triangle 24 1]

-- Cycle fingerprint ad2f76d02617eadb6fc5ae9b1ecc129ecee73c14b94bfa26dd0b50762b098b04.
def localCycle00138 : Cycle where
  length := 6
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 2, .distance 2 4, .distance 4 6, .distance 3 4, .theta 3]
    constant := ![3, -1, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 0, .triangle 16 0, .triangle 29 0, .triangle 32 0, .corridorLower 3 4]

-- Cycle fingerprint ae2d9a52d96f13d3414877440874384eb621030bd184d3437c25e972f0c1ce5b.
def localCycle00139 : Cycle where
  length := 8
  data := {
    node := ![.distance 3 4, .theta 3, .distance 2 3, .distance 1 3, .distance 1 4, .distance 1 6, .distance 1 5, .distance 4 5, .distance 3 4]
    constant := ![-1, 3, 0, 0, -2, -2, 0, -1]
    coefficient := ![0, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, true, false] }
  origin := ![.corridorLower 3 4, .corridorUpper 2 3, .triangle 15 2, .triangle 19 2, .gapLower 1 4, .gapLower 1 3, .triangle 22 1, .triangle 31 0]

-- Cycle fingerprint b04e2abc511bef3ae694e624a96275ce62c0bd092f7d3276ec253052b1e215f9.
def localCycle00140 : Cycle where
  length := 8
  data := {
    node := ![.distance 3 4, .theta 3, .theta 2, .zero, .theta 6, .distance 0 6, .distance 0 4, .distance 4 5, .distance 3 4]
    constant := ![-1, 0, 0, 0, 2, 0, -1, -1]
    coefficient := ![0, 0, 0, 1, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, true, false, false] }
  origin := ![.corridorLower 3 4, .thetaNext 2, .thetaLower 2, .thetaUpper 6, .gapUpper 6 0, .triangle 13 1, .triangle 12 0, .triangle 31 0]

-- Cycle fingerprint b04f30e924796800b762ca0f6ef99f8445917e0b8da037e22c23345cc52cdc3b.
def localCycle00141 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 6, .distance 5 6, .distance 1 5, .distance 1 2, .distance 0 1]
    constant := ![-1, 0, 0, 3, -1, -2, -1]
    coefficient := ![0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 6, .corridorUpper 5 6, .triangle 24 0, .gapLower 1 2, .triangle 0 0]

-- Cycle fingerprint b108706efa022c33903484001395cb74950235563e052808166b4b18facabde9.
def localCycle00142 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 3, .distance 1 4, .distance 4 6, .distance 4 5, .distance 3 4, .theta 3, .distance 2 3, .distance 1 3]
    constant := ![-2, -1, 0, -1, -1, 3, 0]
    coefficient := ![0, 0, 0, 0, 0, 1, 0]
    strict := ![false, false, true, false, false, false, true] }
  origin := ![.gapLower 1 5, .triangle 23 0, .triangle 34 1, .triangle 31 0, .corridorLower 3 4, .corridorUpper 2 3, .triangle 15 2]

-- Cycle fingerprint b15226449ed40915b351205fd82b029b8221ec92a35b3ec1a5274e7e55b3dfbf.
def localCycle00143 : Cycle where
  length := 10
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 2, .distance 1 4, .distance 4 5, .distance 5 6, .distance 3 6, .distance 0 3, .distance 3 5, .distance 3 4, .theta 3]
    constant := ![3, -1, 0, -1, -1, 0, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, false, false, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 0, .triangle 16 2, .triangle 22 0, .triangle 34 0, .triangle 33 2, .triangle 11 0, .triangle 10 0, .triangle 31 1, .corridorLower 3 4]

-- Cycle fingerprint b2128e5d9c01329560fc0e02a5e9a2654f36e6c1770b307ac65a7fccd6dcb3e2.
def localCycle00144 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .theta 1, .zero, .theta 3, .distance 2 3, .distance 2 4, .distance 4 6, .distance 4 5, .distance 1 4, .distance 1 2, .distance 0 1]
    constant := ![-2, 0, 0, 3, 0, -1, 0, -1, -2, -1]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, true, false, false, false] }
  origin := ![.gapLower 1 0, .thetaLower 1, .thetaUpper 3, .corridorUpper 2 3, .triangle 25 2, .triangle 29 0, .triangle 34 1, .triangle 22 0, .gapLower 1 2, .triangle 0 0]

-- Cycle fingerprint b296906f5e4273d2835b3d50f5c47a35782bfdd1b7c0ace9f8a0de6c1684a1da.
def localCycle00145 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 2 5, .distance 1 2, .distance 0 1, .theta 1, .theta 0, .zero]
    constant := ![0, 3, -1, -1, -2, -2, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 30 0, .triangle 17 0, .gapLower 1 1, .gapLower 1 0, .thetaNext 0, .thetaLower 0]

-- Cycle fingerprint b464592f2c9f6688abde1e561f15edac777317bcd9f37e3dbcc6f457e615a1a9.
def localCycle00146 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 2, .distance 0 1, .theta 0, .zero, .theta 6, .distance 5 6, .distance 4 6, .distance 1 4, .distance 1 5, .distance 1 2]
    constant := ![-1, -1, 0, 0, 3, 0, -1, 0, -2]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, true, false] }
  origin := ![.triangle 0 0, .corridorLower 0 1, .thetaLower 0, .thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 23 0, .triangle 22 2, .gapLower 1 2]

-- Cycle fingerprint b51dbce36569a23eca0ba81650f4e680b4c6c690b53bd7c94d5cde0efec9d190.
def localCycle00147 : Cycle where
  length := 8
  data := {
    node := ![.distance 3 5, .distance 3 4, .theta 3, .theta 2, .theta 1, .distance 1 3, .distance 0 3, .distance 3 6, .distance 3 5]
    constant := ![0, -1, 0, 0, 1, 0, -1, 0]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![true, false, true, true, false, true, false, true] }
  origin := ![.triangle 31 1, .corridorLower 3 4, .thetaNext 2, .thetaNext 1, .gapLower 1 6, .triangle 1 2, .triangle 11 0, .triangle 33 1]

-- Cycle fingerprint b5b8340cb3b8b1d5fd803c5962298a10ec2e4b0b1fcf2f4c9afafada6d06a57f.
def localCycle00148 : Cycle where
  length := 8
  data := {
    node := ![.theta 5, .distance 4 5, .distance 2 4, .distance 1 2, .distance 2 6, .distance 4 6, .distance 5 6, .distance 3 5, .theta 5]
    constant := ![3, -1, -1, -1, 0, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, false, false] }
  origin := ![.corridorUpper 4 5, .triangle 28 0, .triangle 16 0, .triangle 18 0, .triangle 29 1, .triangle 34 1, .triangle 33 0, .gapLower 5 0]

-- Cycle fingerprint b6885cb1a6df5428b88598e3de28a0ecc65a180922e6d40b0cfcee3b3da9948d.
def localCycle00149 : Cycle where
  length := 8
  data := {
    node := ![.distance 4 5, .distance 3 4, .theta 3, .theta 2, .theta 1, .distance 1 3, .distance 1 6, .distance 1 4, .distance 4 5]
    constant := ![-1, -1, 0, 0, 1, 0, 0, -1]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![false, false, true, true, false, true, true, false] }
  origin := ![.triangle 31 0, .corridorLower 3 4, .thetaNext 2, .thetaNext 1, .gapLower 1 6, .triangle 21 2, .triangle 23 1, .triangle 22 0]

-- Cycle fingerprint b6cce6e749537325f22ba75b5efe78b717b5fb096dc8da4b47088fdc2c28b8be.
def localCycle00150 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 3, .distance 1 6, .distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 1 3]
    constant := ![-3, -1, -1, 0, 0, 3, 0]
    coefficient := ![0, 0, 0, 0, 1, 1, 0]
    strict := ![false, false, false, false, false, false, true] }
  origin := ![.gapLower 1 5, .triangle 4 0, .corridorLower 0 1, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 15 2]

-- Cycle fingerprint b79991a0f6ecd08c1c9b7a42b43dedafe72ba4b2d467d327de713354468889bb.
def localCycle00151 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 1 4, .distance 1 5, .distance 4 5, .distance 3 4, .theta 3, .zero]
    constant := ![0, 3, 0, -1, -2, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 23 0, .gapLower 1 3, .triangle 22 1, .triangle 31 0, .corridorLower 3 4, .thetaLower 3]

-- Cycle fingerprint b8a2afb31e3d5bdd2c81362f2ae718cfc844e285f3418ae430485f27de9490ea.
def localCycle00152 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 2, .distance 1 4, .distance 4 5, .distance 2 5, .distance 5 6, .distance 3 5, .distance 3 4, .theta 3]
    constant := ![3, -1, 0, -1, 0, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 0, .triangle 16 2, .triangle 22 0, .triangle 28 2, .triangle 30 0, .triangle 33 0, .gapLower 3 1, .corridorLower 3 4]

-- Cycle fingerprint ba75633932944189c64274d3eba812f581ea5dee5bb4bf7a1a3f906cf12a2f48.
def localCycle00153 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 3, .distance 2 3, .distance 2 4, .distance 4 6, .distance 4 5, .distance 1 5, .distance 1 4, .distance 1 2, .distance 0 1, .theta 1, .zero]
    constant := ![0, 3, 0, -1, 0, 0, -2, 0, -1, -2, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false, true, false, false, false] }
  origin := ![.thetaUpper 3, .corridorUpper 2 3, .triangle 25 2, .triangle 29 0, .triangle 34 1, .gapLower 5 3, .gapLower 1 3, .triangle 16 1, .triangle 0 0, .gapLower 1 0, .thetaLower 1]

-- Cycle fingerprint bb2ced09b4e83112e64ad673464ad22d2576f2297e2d2197eacc63f41a64b9a3.
def localCycle00154 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .theta 1, .zero, .theta 3, .distance 2 3, .distance 2 5, .distance 5 6, .distance 1 5, .distance 1 4, .distance 1 2, .distance 0 1]
    constant := ![-2, 0, 0, 3, 0, -1, -1, 0, -2, -1]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, false, false, false] }
  origin := ![.gapLower 1 0, .thetaLower 1, .thetaUpper 3, .corridorUpper 2 3, .triangle 26 2, .triangle 30 0, .triangle 24 0, .gapLower 1 3, .gapLower 1 2, .triangle 0 0]

-- Cycle fingerprint bc4ce61628607b953dc3fc7671d80050093d89607d0809d6d4121c37a7d1a8af.
def localCycle00155 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 4, .distance 1 5, .distance 1 2, .distance 0 1, .theta 0, .zero, .theta 6, .distance 5 6, .distance 4 6, .distance 1 4]
    constant := ![0, -2, -2, -1, 0, 0, 3, 0, -1]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![true, false, false, false, false, false, false, true, false] }
  origin := ![.triangle 22 2, .gapLower 1 2, .gapLower 1 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 23 0]

-- Cycle fingerprint bc78ffa9a9fc7a24fa6874d43cce95653ebd2e3e823aaacbf26f42611c54c18f.
def localCycle00156 : Cycle where
  length := 7
  data := {
    node := ![.distance 3 6, .distance 0 3, .distance 0 4, .distance 4 5, .distance 3 4, .theta 3, .distance 2 3, .distance 3 6]
    constant := ![-1, 0, -1, -1, -1, 3, -1]
    coefficient := ![0, 0, 0, 0, 0, 1, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.triangle 11 0, .gapLower 0 4, .triangle 12 0, .triangle 31 0, .corridorLower 3 4, .corridorUpper 2 3, .triangle 27 0]

-- Cycle fingerprint bca4f62b8c3cb949c32ee8ca9890f53691df767f39569fd5dd023c0aa19aacb2.
def localCycle00157 : Cycle where
  length := 11
  data := {
    node := ![.theta 1, .zero, .theta 3, .distance 2 3, .distance 2 5, .distance 5 6, .distance 1 6, .distance 1 5, .distance 1 4, .distance 1 2, .distance 0 1, .theta 1]
    constant := ![0, 0, 3, 0, -1, 0, -2, 0, 0, -1, -2]
    coefficient := ![0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, true, true, false, false] }
  origin := ![.thetaLower 1, .thetaUpper 3, .corridorUpper 2 3, .triangle 26 2, .triangle 30 0, .gapLower 6 3, .gapLower 1 4, .triangle 22 1, .triangle 16 1, .triangle 0 0, .gapLower 1 0]

-- Cycle fingerprint bca9d1e28fac4e25009ab7eb2a0f76675b0fd7fed0de3e9dbbf9874b8eb33b76.
def localCycle00158 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 2, .distance 2 6, .distance 5 6, .distance 4 6, .distance 3 4, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, -1, -1, 0, 0, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false, false, false, true] }
  origin := ![.corridorUpper 2 3, .triangle 15 0, .triangle 18 0, .triangle 30 1, .triangle 34 2, .triangle 32 0, .triangle 31 0, .corridorLower 4 5, .thetaNext 3]

-- Cycle fingerprint bdf38f79810554690caa66d4516c96cf3e3c3f40070e62037aa8e80a05963f1f.
def localCycle00159 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 2 3, .distance 1 2, .distance 2 5, .distance 0 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, 0, -1, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, false, true, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 27 0, .triangle 15 0, .triangle 17 0, .triangle 7 0, .triangle 0 1, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint bfefb617506baafceb576026eafe17f592309dce89b44fb3eed34abe05a9578f.
def localCycle00160 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 3, .distance 1 4, .distance 1 6, .distance 1 5, .distance 4 5, .distance 3 4, .theta 3]
    constant := ![3, 0, 0, 0, -3, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, true, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 2, .triangle 19 2, .triangle 23 2, .gapLower 1 3, .triangle 22 1, .triangle 31 0, .corridorLower 3 4]

-- Cycle fingerprint c01afb07aa35b287026f5a3945cf6a1f785165c4886127aff655c2900dc5efdb.
def localCycle00161 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 5, .distance 1 2, .distance 0 1, .theta 1, .zero, .theta 6, .distance 5 6, .distance 1 5]
    constant := ![-2, -1, -2, 0, 0, 3, -1]
    coefficient := ![0, 0, 0, 0, 1, 1, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 1 2, .triangle 0 0, .gapLower 1 0, .thetaLower 1, .thetaUpper 6, .corridorUpper 5 6, .triangle 24 0]

-- Cycle fingerprint c1d11933d58717884129b847007cc8ce1555ef4a46ee9e2b2b019c2e72e550e6.
def localCycle00162 : Cycle where
  length := 8
  data := {
    node := ![.distance 4 5, .distance 3 4, .theta 3, .theta 2, .theta 1, .distance 1 3, .distance 1 4, .distance 4 6, .distance 4 5]
    constant := ![-1, -1, 0, 0, 2, -2, -1, 0]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, true] }
  origin := ![.triangle 31 0, .corridorLower 3 4, .thetaNext 2, .thetaNext 1, .gapLower 1 6, .gapLower 1 5, .triangle 23 0, .triangle 34 1]

-- Cycle fingerprint c31b04b1749358938eab7dc80924e7cde96afeb3956ea5fd136d45d06b1e5424.
def localCycle00163 : Cycle where
  length := 9
  data := {
    node := ![.distance 4 6, .distance 1 4, .distance 1 5, .distance 1 2, .distance 0 1, .theta 0, .zero, .theta 6, .distance 5 6, .distance 4 6]
    constant := ![-1, -2, 0, -2, -1, 0, 0, 3, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![false, false, true, false, false, false, false, false, true] }
  origin := ![.triangle 23 0, .gapLower 1 3, .triangle 17 1, .gapLower 1 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 6, .corridorUpper 5 6, .triangle 34 2]

-- Cycle fingerprint c38a1d6466e58dcc1dcee93b5ef3eda3646daeb180c124e49f356bcfc4bc6941.
def localCycle00164 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 3, .distance 1 4, .distance 1 5, .distance 5 6, .distance 4 5, .distance 3 4, .theta 3]
    constant := ![3, 0, 0, 0, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 2, .triangle 19 2, .triangle 22 2, .triangle 24 0, .triangle 34 0, .triangle 31 0, .corridorLower 3 4]

-- Cycle fingerprint c41a1f738bcf0b85a9b8f3cbe71f811bff5e5adca5d7a2d96d8a4445c766eb77.
def localCycle00165 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 1, .distance 1 3, .distance 1 6, .distance 1 5, .distance 1 4, .distance 1 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 2, -2, 0, 0, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, true, false, false, false] }
  origin := ![.thetaUpper 1, .gapLower 1 6, .gapLower 1 5, .triangle 24 1, .triangle 22 1, .triangle 16 1, .triangle 0 0, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint c4db3e0430c3bd7ecd52bcc5d0610f0aa21ac0930f8febc36a8ea47c42c6bdc6.
def localCycle00166 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 5, .distance 1 2, .distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 1 3, .distance 1 4, .distance 1 6, .distance 1 5]
    constant := ![-2, -1, -1, 0, 0, 3, 0, 0, -2, 0]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, true, false, true] }
  origin := ![.gapLower 1 2, .triangle 0 0, .corridorLower 0 1, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 15 2, .triangle 19 2, .gapLower 1 4, .triangle 24 1]

-- Cycle fingerprint c5a482e4037bd3889fe49954f1eaf81fa3a3cf86b637b188bbafad006d63666f.
def localCycle00167 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 2, .distance 1 5, .distance 5 6, .distance 3 5, .distance 3 4, .theta 3]
    constant := ![3, -1, 0, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 0, .triangle 17 2, .triangle 24 0, .triangle 33 0, .triangle 31 1, .corridorLower 3 4]

-- Cycle fingerprint c75e2a7321dbe260b751f6d6bd34b8263ef51ebbe0ac905a6d1aa665eb8f5dd8.
def localCycle00168 : Cycle where
  length := 8
  data := {
    node := ![.distance 4 5, .distance 3 4, .theta 3, .distance 2 3, .distance 3 6, .distance 1 3, .distance 1 2, .distance 2 4, .distance 4 5]
    constant := ![-1, -1, 3, -1, -1, 0, -1, -1]
    coefficient := ![0, 0, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.triangle 31 0, .corridorLower 3 4, .corridorUpper 2 3, .triangle 27 0, .triangle 21 0, .gapLower 1 4, .triangle 16 0, .triangle 28 0]

-- Cycle fingerprint c920072ec595f9f208e0af2153aa38bb05591c3f6032a4e9e44fc7e0b211aa69.
def localCycle00169 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 3, .distance 1 4, .distance 4 6, .distance 3 4, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, 0, 0, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, false, false, true] }
  origin := ![.corridorUpper 2 3, .triangle 15 2, .triangle 19 2, .triangle 23 0, .triangle 32 0, .triangle 31 0, .corridorLower 4 5, .thetaNext 3]

-- Cycle fingerprint c9ddc208af3c5cfaa34c1b57aed353545b3e3d2a54e95c433406963aa93dc07f.
def localCycle00170 : Cycle where
  length := 7
  data := {
    node := ![.theta 5, .distance 4 5, .distance 2 4, .distance 1 2, .distance 0 1, .theta 0, .zero, .theta 5]
    constant := ![3, -1, -1, -2, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 1]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.corridorUpper 4 5, .triangle 28 0, .triangle 16 0, .gapLower 1 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 5]

-- Cycle fingerprint cb4a20e41896ac38bc7530538c88fd912d3474b17aaff2acb238ca68b2be72f5.
def localCycle00171 : Cycle where
  length := 6
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 2, .distance 2 4, .distance 4 5, .distance 3 4, .theta 3]
    constant := ![3, -1, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 0, .triangle 16 0, .triangle 28 0, .triangle 31 0, .corridorLower 3 4]

-- Cycle fingerprint cda4e3460f58a3e17bf8ed37995f1fc06808c34ea8c1ad888fd37d49aafb0560.
def localCycle00172 : Cycle where
  length := 12
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 2, .distance 2 6, .distance 4 6, .distance 3 6, .distance 1 3, .distance 1 4, .distance 4 5, .distance 5 6, .distance 3 5, .distance 3 4, .theta 3]
    constant := ![3, -1, -1, 0, 0, 2, 0, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, true, true, false, false, false, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 0, .triangle 18 0, .triangle 29 1, .triangle 32 2, .gapUpper 3 4, .triangle 19 2, .triangle 22 0, .triangle 34 0, .triangle 33 0, .triangle 31 1, .corridorLower 3 4]

-- Cycle fingerprint ce024a9941f279ec4075f02df571e043ac1aa70b7470f59b31a667eae5e879d4.
def localCycle00173 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 4, .distance 3 4, .theta 3, .distance 2 3, .distance 1 3, .distance 1 6, .distance 1 4, .distance 4 5, .distance 0 4]
    constant := ![0, -1, 3, 0, -2, 0, -1, -1]
    coefficient := ![0, 0, 1, 0, 0, 0, 0, 0]
    strict := ![true, false, false, true, false, true, false, false] }
  origin := ![.triangle 9 1, .corridorLower 3 4, .corridorUpper 2 3, .triangle 15 2, .gapLower 1 5, .triangle 23 1, .triangle 22 0, .triangle 12 0]

-- Cycle fingerprint cf46c508faee5a681a243ecd1263bb4816f42b0701e6cf3beb3839a3d8aec25e.
def localCycle00174 : Cycle where
  length := 8
  data := {
    node := ![.distance 4 5, .distance 3 4, .theta 3, .theta 2, .theta 1, .distance 1 3, .distance 1 6, .distance 1 4, .distance 4 5]
    constant := ![-1, -1, 0, 0, 2, -2, 0, -1]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![false, false, true, true, false, false, true, false] }
  origin := ![.triangle 31 0, .corridorLower 3 4, .thetaNext 2, .thetaNext 1, .gapLower 1 6, .gapLower 1 5, .triangle 23 1, .triangle 22 0]

-- Cycle fingerprint d060595365b030d0db2fab9f612e7c1e57ebef2a657e15e0a0531d555f9b5c25.
def localCycle00175 : Cycle where
  length := 11
  data := {
    node := ![.theta 1, .zero, .theta 3, .distance 2 3, .distance 2 4, .distance 4 6, .distance 1 6, .distance 1 5, .distance 1 4, .distance 1 2, .distance 0 1, .theta 1]
    constant := ![0, 0, 3, 0, -1, 0, -2, 0, 0, -1, -2]
    coefficient := ![0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, true, true, false, false] }
  origin := ![.thetaLower 1, .thetaUpper 3, .corridorUpper 2 3, .triangle 25 2, .triangle 29 0, .gapLower 6 3, .gapLower 1 4, .triangle 22 1, .triangle 16 1, .triangle 0 0, .gapLower 1 0]

-- Cycle fingerprint d1b19de2d2bf6ac58468aee1b4242853d32aa7ad7bccdd55e11d33a6278ccd57.
def localCycle00176 : Cycle where
  length := 8
  data := {
    node := ![.distance 3 5, .distance 3 4, .theta 3, .theta 2, .theta 1, .distance 1 3, .distance 1 5, .distance 5 6, .distance 3 5]
    constant := ![0, -1, 0, 0, 1, 0, -1, -1]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![false, false, true, true, false, true, false, false] }
  origin := ![.gapLower 3 1, .corridorLower 3 4, .thetaNext 2, .thetaNext 1, .gapLower 1 6, .triangle 20 2, .triangle 24 0, .triangle 33 0]

-- Cycle fingerprint d297af23b9c31b53664708f32449de11f2f2a8de2666d2f5963d2925eb95844e.
def localCycle00177 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 5, .distance 2 5, .distance 1 2, .distance 2 4, .distance 0 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, -1, 0, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, true, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 0, .triangle 28 2, .triangle 17 0, .triangle 16 0, .triangle 6 0, .triangle 0 1, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint d4d9727772551381b138fe0483b14b7b3d72af96192bb07cebc4ed24e742d97f.
def localCycle00178 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 2, .distance 0 1, .theta 1, .zero, .theta 3, .distance 2 3, .distance 1 3, .distance 1 4, .distance 1 6, .distance 1 5, .distance 1 2]
    constant := ![-1, -2, 0, 0, 3, 0, 0, 0, -2, 0]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, true, false, true] }
  origin := ![.triangle 0 0, .gapLower 1 0, .thetaLower 1, .thetaUpper 3, .corridorUpper 2 3, .triangle 15 2, .triangle 19 2, .triangle 23 2, .gapLower 1 3, .triangle 17 1]

-- Cycle fingerprint d6c1b6929e16d0e290bbbeacfc46005f5958de80a7790088f7a4ad77a4b54a78.
def localCycle00179 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 2, .distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 2 4, .distance 4 6, .distance 1 6, .distance 1 5, .distance 1 2]
    constant := ![-2, -1, 0, 0, 3, 0, -1, 0, -2, 0]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, true, false, true] }
  origin := ![.gapLower 1 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 25 2, .triangle 29 0, .triangle 23 2, .gapLower 1 4, .triangle 17 1]

-- Cycle fingerprint d78753c3a38b1fdc0896e2101f448551558a11809f498c46b7e91d1dcbe2ef55.
def localCycle00180 : Cycle where
  length := 11
  data := {
    node := ![.theta 0, .zero, .theta 3, .distance 2 3, .distance 2 4, .distance 4 5, .distance 5 6, .distance 1 5, .distance 1 4, .distance 1 2, .distance 0 1, .theta 0]
    constant := ![0, 0, 3, 0, -1, -1, -1, 0, 0, -1, -1]
    coefficient := ![0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, false, true, false, false] }
  origin := ![.thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 25 2, .triangle 28 0, .triangle 34 0, .triangle 24 0, .gapLower 1 3, .triangle 16 1, .triangle 0 0, .corridorLower 0 1]

-- Cycle fingerprint d83e9ce89d5b9eeea7a6b5d0eceb0bb4c1b108cdcc9549659e3d58dd5160b15a.
def localCycle00181 : Cycle where
  length := 10
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 3, .distance 1 4, .distance 1 5, .distance 5 6, .distance 4 6, .distance 3 4, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, 0, 0, 0, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, true, false, false, false, true] }
  origin := ![.corridorUpper 2 3, .triangle 15 2, .triangle 19 2, .triangle 22 2, .triangle 24 0, .triangle 34 2, .triangle 32 0, .triangle 31 0, .corridorLower 4 5, .thetaNext 3]

-- Cycle fingerprint db128e1b29ae93b53106f217d49392e31f79dec37d2a1a6718aed19df6da7e05.
def localCycle00182 : Cycle where
  length := 6
  data := {
    node := ![.distance 1 2, .distance 1 5, .distance 5 6, .distance 4 6, .distance 3 6, .distance 2 3, .distance 1 2]
    constant := ![0, 2, 0, 0, -1, -1]
    coefficient := ![0, 0, 0, 0, 0, 0]
    strict := ![true, true, true, true, false, false] }
  origin := ![.triangle 17 2, .gapUpper 5 5, .triangle 34 2, .triangle 32 2, .triangle 27 0, .triangle 15 0]

-- Cycle fingerprint dbde3065a8ff7a4f531371977eebeebdf89cc329d785488b0e27fbc609f31c63.
def localCycle00183 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 2 3, .distance 2 4, .distance 4 6, .distance 3 4, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, 0, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, true] }
  origin := ![.corridorUpper 2 3, .triangle 25 2, .triangle 29 0, .triangle 32 0, .triangle 31 0, .corridorLower 4 5, .thetaNext 3]

-- Cycle fingerprint dd05066571d17efc2588a65c19a35213fd1b443cff964507b9bc2275707419e4.
def localCycle00184 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 2, .distance 1 4, .distance 4 6, .distance 4 5, .distance 3 4, .theta 3]
    constant := ![3, -1, 0, -1, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 0, .triangle 16 2, .triangle 23 0, .triangle 34 1, .triangle 31 0, .corridorLower 3 4]

-- Cycle fingerprint ddedd9bf2d0babf7a115868b1cb0d51def2ed16005f3da434b16bd15d295f851.
def localCycle00185 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 2 4, .distance 4 6, .distance 1 4, .distance 1 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, -1, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 28 0, .triangle 29 0, .triangle 23 0, .triangle 16 1, .triangle 0 0, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint e068f7b9c206da40b80230e1a677c35a878f58e90c674bae924c20a6d691cbc2.
def localCycle00186 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 3, .distance 1 5, .distance 5 6, .distance 3 5, .distance 3 4, .theta 3, .distance 2 3, .distance 1 3]
    constant := ![-2, -1, -1, 0, -1, 3, 0]
    coefficient := ![0, 0, 0, 0, 0, 1, 0]
    strict := ![false, false, false, false, false, false, true] }
  origin := ![.gapLower 1 5, .triangle 24 0, .triangle 33 0, .gapLower 3 1, .corridorLower 3 4, .corridorUpper 2 3, .triangle 15 2]

-- Cycle fingerprint e22763b22e15d15084ab0d1cd4b585974ca137c2e78d0a0deeea7f47f294da2a.
def localCycle00187 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 3, .distance 1 5, .distance 1 6, .distance 1 2, .distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 1 3]
    constant := ![0, -2, 0, -2, -1, 0, 0, 3, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![true, false, true, false, false, false, false, false, true] }
  origin := ![.triangle 20 2, .gapLower 1 4, .triangle 18 1, .gapLower 1 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 15 2]

-- Cycle fingerprint e28abb363be99d95147e9fdfb77e05fb9daf7123928df4db50e84b74f5c4809f.
def localCycle00188 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 2, .distance 1 4, .distance 4 5, .distance 2 4, .distance 0 4, .distance 3 4, .theta 3]
    constant := ![3, -1, 0, -1, -1, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 0, .triangle 16 2, .triangle 22 0, .triangle 28 0, .triangle 6 2, .triangle 9 1, .corridorLower 3 4]

-- Cycle fingerprint e558512a0ba94bab17466d299760ce9d7dc9611720f268e01fc001938577418a.
def localCycle00189 : Cycle where
  length := 10
  data := {
    node := ![.distance 4 5, .distance 1 4, .distance 1 2, .distance 0 1, .theta 1, .zero, .theta 3, .distance 2 3, .distance 2 4, .distance 4 6, .distance 4 5]
    constant := ![-1, 0, -1, -2, 0, 0, 3, 0, -1, 0]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false, true, false, true] }
  origin := ![.triangle 22 0, .triangle 16 1, .triangle 0 0, .gapLower 1 0, .thetaLower 1, .thetaUpper 3, .corridorUpper 2 3, .triangle 25 2, .triangle 29 0, .triangle 34 1]

-- Cycle fingerprint e841e3efb2ae5eb1b8ee122ef6b051ffc4afbc2be739fef15a6d8fc8e2c67913.
def localCycle00190 : Cycle where
  length := 6
  data := {
    node := ![.distance 1 5, .distance 1 6, .distance 1 4, .distance 1 2, .theta 1, .distance 1 3, .distance 1 5]
    constant := ![0, -2, 0, -1, 2, 0]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![true, false, true, false, false, true] }
  origin := ![.triangle 24 2, .gapLower 1 3, .triangle 16 1, .corridorLower 1 2, .gapLower 1 6, .triangle 20 2]

-- Cycle fingerprint eb7391bdcd1fc4ad01c46036c14f3eef27bdbf53ca7a15db5a372e46cba5f4b5.
def localCycle00191 : Cycle where
  length := 9
  data := {
    node := ![.distance 2 4, .distance 4 6, .distance 1 4, .distance 1 2, .distance 2 5, .distance 4 5, .distance 3 4, .theta 3, .distance 2 3, .distance 2 4]
    constant := ![-1, -1, 0, -1, 0, -1, -1, 3, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1, 0]
    strict := ![false, false, false, false, true, false, false, false, true] }
  origin := ![.triangle 29 0, .triangle 23 0, .gapLower 1 3, .triangle 17 0, .triangle 28 1, .triangle 31 0, .corridorLower 3 4, .corridorUpper 2 3, .triangle 25 2]

-- Cycle fingerprint ecda36d9eeceec91d9dcd3bf751906a85b715a7c2dc5b4f3a7a853a010b1b748.
def localCycle00192 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 3, .distance 1 4, .distance 1 6, .distance 4 6, .distance 3 4, .theta 3, .distance 2 3, .distance 1 3]
    constant := ![-2, -2, 0, -1, -1, 3, 0]
    coefficient := ![0, 0, 0, 0, 0, 1, 0]
    strict := ![false, false, true, false, false, false, true] }
  origin := ![.gapLower 1 5, .gapLower 1 4, .triangle 23 1, .triangle 32 0, .corridorLower 3 4, .corridorUpper 2 3, .triangle 15 2]

-- Cycle fingerprint eda16fb73721251b2ed9c774cabf69d05d1832d622669ed27a3c229dd1fa8c02.
def localCycle00193 : Cycle where
  length := 8
  data := {
    node := ![.distance 4 5, .distance 0 4, .distance 0 2, .distance 0 1, .theta 1, .distance 1 3, .distance 1 4, .distance 4 6, .distance 4 5]
    constant := ![-1, 0, 0, -2, 2, 0, -1, 0]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![false, false, true, false, false, true, false, true] }
  origin := ![.triangle 12 0, .gapLower 0 2, .triangle 0 1, .gapLower 1 0, .gapLower 1 6, .triangle 19 2, .triangle 23 0, .triangle 34 1]

-- Cycle fingerprint f150b1fc1433ae759aae0332701eabecfcbc83a841a621cd4b309559c2429bd6.
def localCycle00194 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 2 3, .distance 2 4, .distance 4 5, .distance 1 4, .distance 4 6, .distance 3 4, .theta 3]
    constant := ![3, 0, -1, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 25 2, .triangle 28 0, .triangle 22 0, .triangle 23 0, .triangle 32 0, .corridorLower 3 4]

-- Cycle fingerprint f282f8004ba74d12946e273297ac2d80989f54ec4a27a7350c637632d983d815.
def localCycle00195 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 4, .distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 2 4, .distance 4 6, .distance 1 6, .distance 1 5, .distance 1 4]
    constant := ![-1, -1, 0, 0, 3, 0, -1, 0, -2, -2]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, false, false, false] }
  origin := ![.triangle 2 0, .corridorLower 0 1, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 25 2, .triangle 29 0, .gapLower 6 3, .gapLower 1 4, .gapLower 1 3]

-- Cycle fingerprint f2fd1d510c371647302fac5e3764e4a8cb5e97b5a580232b81dca9f76d74b64f.
def localCycle00196 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 2, .distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 2 5, .distance 5 6, .distance 1 6, .distance 1 5, .distance 1 2]
    constant := ![-2, -1, 0, 0, 3, 0, -1, 0, -2, 0]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, true, false, true] }
  origin := ![.gapLower 1 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 26 2, .triangle 30 0, .triangle 24 2, .gapLower 1 4, .triangle 17 1]

-- Cycle fingerprint f4d4f2bd49a24d1675d8a762bdb8d132d16550bc5dd8a84dc9d70cff0ec01a31.
def localCycle00197 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 5, .distance 1 6, .distance 1 4, .distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 1 3, .distance 1 5]
    constant := ![0, -3, -1, -1, 0, 0, 3, 0, 0]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![true, false, false, false, false, false, false, true, true] }
  origin := ![.triangle 24 2, .gapLower 1 3, .triangle 2 0, .corridorLower 0 1, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 15 2, .triangle 20 2]

-- Cycle fingerprint f54665948173455016aa0614f2e0ab34540deb98b080c03647b4438fe943f3b6.
def localCycle00198 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 3, .distance 3 6, .distance 0 3, .distance 0 4, .distance 4 5, .distance 3 4, .theta 3]
    constant := ![3, 0, -1, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 2, .triangle 21 0, .triangle 11 0, .triangle 9 2, .triangle 12 0, .triangle 31 0, .corridorLower 3 4]

-- Cycle fingerprint f575fb4e5d266d88f4ae596dcf5753ccafa1701f49ece61b0feba7ba9f6e3b9c.
def localCycle00199 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 2, .distance 1 6, .distance 1 4, .distance 4 5, .distance 3 4, .theta 3]
    constant := ![3, -1, 0, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 0, .triangle 18 2, .triangle 23 1, .triangle 22 0, .triangle 31 0, .corridorLower 3 4]

-- Cycle fingerprint f5d6955448581b6a63a0ff0d37d77152081efdb6a7e0f828a94ed5c23424b194.
def localCycle00200 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 2, .distance 2 6, .distance 3 6, .distance 0 3, .distance 3 5, .distance 3 4, .theta 3]
    constant := ![3, -1, -1, 0, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 0, .triangle 18 0, .triangle 27 1, .triangle 11 0, .triangle 10 0, .triangle 31 1, .corridorLower 3 4]

-- Cycle fingerprint f688318c554d03945d75815ae3886b40d74cc74c6eafec419ca82025e7b570f8.
def localCycle00201 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 5 6, .distance 2 5, .distance 2 4, .distance 1 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, -1, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 34 0, .triangle 30 0, .triangle 28 1, .triangle 16 0, .triangle 0 0, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint f70a988cd39aac02682326052dc2745574da9de6257931be83c17578e5fc5db4.
def localCycle00202 : Cycle where
  length := 11
  data := {
    node := ![.theta 0, .zero, .theta 3, .distance 2 3, .distance 2 5, .distance 5 6, .distance 1 6, .distance 1 5, .distance 1 4, .distance 1 2, .distance 0 1, .theta 0]
    constant := ![0, 0, 3, 0, -1, 0, -2, 0, -2, -1, -1]
    coefficient := ![0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, true, false, false, false] }
  origin := ![.thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 26 2, .triangle 30 0, .gapLower 6 3, .gapLower 1 4, .triangle 22 1, .gapLower 1 2, .triangle 0 0, .corridorLower 0 1]

-- Cycle fingerprint f7426e7ede10dc413047f0b35f4c49ecb00695e45beddd2750ad633b13642d8b.
def localCycle00203 : Cycle where
  length := 8
  data := {
    node := ![.theta 0, .zero, .theta 3, .distance 2 3, .distance 1 3, .distance 1 6, .distance 1 2, .distance 0 1, .theta 0]
    constant := ![0, 0, 3, 0, -2, 0, -2, -1]
    coefficient := ![0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true, false, false] }
  origin := ![.thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 15 2, .gapLower 1 5, .triangle 18 1, .gapLower 1 1, .corridorLower 0 1]

-- Cycle fingerprint f8956432bf5bb39f46ca001fc8d2ac149f57409128b6660f15c7c81325008600.
def localCycle00204 : Cycle where
  length := 5
  data := {
    node := ![.theta 5, .distance 4 5, .distance 2 4, .distance 2 6, .theta 6, .theta 5]
    constant := ![3, -1, 0, -2, 0]
    coefficient := ![1, 0, 0, -1, 0]
    strict := ![false, false, true, true, true] }
  origin := ![.corridorUpper 4 5, .triangle 28 0, .triangle 29 2, .gapUpper 6 6, .thetaNext 5]

-- Cycle fingerprint fce6a4ddc9a335d6fee031099c2eea2547a7ba98489e1e085bb4ec1dbe444794.
def localCycle00205 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 4, .distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 2 5, .distance 5 6, .distance 1 6, .distance 1 5, .distance 1 4]
    constant := ![-1, -1, 0, 0, 3, 0, -1, 0, -2, -2]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, false, false, false] }
  origin := ![.triangle 2 0, .corridorLower 0 1, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 26 2, .triangle 30 0, .gapLower 6 3, .gapLower 1 4, .gapLower 1 3]

def library : Library := fun id => if id < 103 then (if id < 51 then (if id < 25 then (if id < 12 then (if id < 6 then (if id < 3 then (if id < 1 then (if id = 0 then some localCycle00000 else none) else (if id < 2 then (if id = 1 then some localCycle00001 else none) else (if id = 2 then some localCycle00002 else none))) else (if id < 4 then (if id = 3 then some localCycle00003 else none) else (if id < 5 then (if id = 4 then some localCycle00004 else none) else (if id = 5 then some localCycle00005 else none)))) else (if id < 9 then (if id < 7 then (if id = 6 then some localCycle00006 else none) else (if id < 8 then (if id = 7 then some localCycle00007 else none) else (if id = 8 then some localCycle00008 else none))) else (if id < 10 then (if id = 9 then some localCycle00009 else none) else (if id < 11 then (if id = 10 then some localCycle00010 else none) else (if id = 11 then some localCycle00011 else none))))) else (if id < 18 then (if id < 15 then (if id < 13 then (if id = 12 then some localCycle00012 else none) else (if id < 14 then (if id = 13 then some localCycle00013 else none) else (if id = 14 then some localCycle00014 else none))) else (if id < 16 then (if id = 15 then some localCycle00015 else none) else (if id < 17 then (if id = 16 then some localCycle00016 else none) else (if id = 17 then some localCycle00017 else none)))) else (if id < 21 then (if id < 19 then (if id = 18 then some localCycle00018 else none) else (if id < 20 then (if id = 19 then some localCycle00019 else none) else (if id = 20 then some localCycle00020 else none))) else (if id < 23 then (if id < 22 then (if id = 21 then some localCycle00021 else none) else (if id = 22 then some localCycle00022 else none)) else (if id < 24 then (if id = 23 then some localCycle00023 else none) else (if id = 24 then some localCycle00024 else none)))))) else (if id < 38 then (if id < 31 then (if id < 28 then (if id < 26 then (if id = 25 then some localCycle00025 else none) else (if id < 27 then (if id = 26 then some localCycle00026 else none) else (if id = 27 then some localCycle00027 else none))) else (if id < 29 then (if id = 28 then some localCycle00028 else none) else (if id < 30 then (if id = 29 then some localCycle00029 else none) else (if id = 30 then some localCycle00030 else none)))) else (if id < 34 then (if id < 32 then (if id = 31 then some localCycle00031 else none) else (if id < 33 then (if id = 32 then some localCycle00032 else none) else (if id = 33 then some localCycle00033 else none))) else (if id < 36 then (if id < 35 then (if id = 34 then some localCycle00034 else none) else (if id = 35 then some localCycle00035 else none)) else (if id < 37 then (if id = 36 then some localCycle00036 else none) else (if id = 37 then some localCycle00037 else none))))) else (if id < 44 then (if id < 41 then (if id < 39 then (if id = 38 then some localCycle00038 else none) else (if id < 40 then (if id = 39 then some localCycle00039 else none) else (if id = 40 then some localCycle00040 else none))) else (if id < 42 then (if id = 41 then some localCycle00041 else none) else (if id < 43 then (if id = 42 then some localCycle00042 else none) else (if id = 43 then some localCycle00043 else none)))) else (if id < 47 then (if id < 45 then (if id = 44 then some localCycle00044 else none) else (if id < 46 then (if id = 45 then some localCycle00045 else none) else (if id = 46 then some localCycle00046 else none))) else (if id < 49 then (if id < 48 then (if id = 47 then some localCycle00047 else none) else (if id = 48 then some localCycle00048 else none)) else (if id < 50 then (if id = 49 then some localCycle00049 else none) else (if id = 50 then some localCycle00050 else none))))))) else (if id < 77 then (if id < 64 then (if id < 57 then (if id < 54 then (if id < 52 then (if id = 51 then some localCycle00051 else none) else (if id < 53 then (if id = 52 then some localCycle00052 else none) else (if id = 53 then some localCycle00053 else none))) else (if id < 55 then (if id = 54 then some localCycle00054 else none) else (if id < 56 then (if id = 55 then some localCycle00055 else none) else (if id = 56 then some localCycle00056 else none)))) else (if id < 60 then (if id < 58 then (if id = 57 then some localCycle00057 else none) else (if id < 59 then (if id = 58 then some localCycle00058 else none) else (if id = 59 then some localCycle00059 else none))) else (if id < 62 then (if id < 61 then (if id = 60 then some localCycle00060 else none) else (if id = 61 then some localCycle00061 else none)) else (if id < 63 then (if id = 62 then some localCycle00062 else none) else (if id = 63 then some localCycle00063 else none))))) else (if id < 70 then (if id < 67 then (if id < 65 then (if id = 64 then some localCycle00064 else none) else (if id < 66 then (if id = 65 then some localCycle00065 else none) else (if id = 66 then some localCycle00066 else none))) else (if id < 68 then (if id = 67 then some localCycle00067 else none) else (if id < 69 then (if id = 68 then some localCycle00068 else none) else (if id = 69 then some localCycle00069 else none)))) else (if id < 73 then (if id < 71 then (if id = 70 then some localCycle00070 else none) else (if id < 72 then (if id = 71 then some localCycle00071 else none) else (if id = 72 then some localCycle00072 else none))) else (if id < 75 then (if id < 74 then (if id = 73 then some localCycle00073 else none) else (if id = 74 then some localCycle00074 else none)) else (if id < 76 then (if id = 75 then some localCycle00075 else none) else (if id = 76 then some localCycle00076 else none)))))) else (if id < 90 then (if id < 83 then (if id < 80 then (if id < 78 then (if id = 77 then some localCycle00077 else none) else (if id < 79 then (if id = 78 then some localCycle00078 else none) else (if id = 79 then some localCycle00079 else none))) else (if id < 81 then (if id = 80 then some localCycle00080 else none) else (if id < 82 then (if id = 81 then some localCycle00081 else none) else (if id = 82 then some localCycle00082 else none)))) else (if id < 86 then (if id < 84 then (if id = 83 then some localCycle00083 else none) else (if id < 85 then (if id = 84 then some localCycle00084 else none) else (if id = 85 then some localCycle00085 else none))) else (if id < 88 then (if id < 87 then (if id = 86 then some localCycle00086 else none) else (if id = 87 then some localCycle00087 else none)) else (if id < 89 then (if id = 88 then some localCycle00088 else none) else (if id = 89 then some localCycle00089 else none))))) else (if id < 96 then (if id < 93 then (if id < 91 then (if id = 90 then some localCycle00090 else none) else (if id < 92 then (if id = 91 then some localCycle00091 else none) else (if id = 92 then some localCycle00092 else none))) else (if id < 94 then (if id = 93 then some localCycle00093 else none) else (if id < 95 then (if id = 94 then some localCycle00094 else none) else (if id = 95 then some localCycle00095 else none)))) else (if id < 99 then (if id < 97 then (if id = 96 then some localCycle00096 else none) else (if id < 98 then (if id = 97 then some localCycle00097 else none) else (if id = 98 then some localCycle00098 else none))) else (if id < 101 then (if id < 100 then (if id = 99 then some localCycle00099 else none) else (if id = 100 then some localCycle00100 else none)) else (if id < 102 then (if id = 101 then some localCycle00101 else none) else (if id = 102 then some localCycle00102 else none)))))))) else (if id < 154 then (if id < 128 then (if id < 115 then (if id < 109 then (if id < 106 then (if id < 104 then (if id = 103 then some localCycle00103 else none) else (if id < 105 then (if id = 104 then some localCycle00104 else none) else (if id = 105 then some localCycle00105 else none))) else (if id < 107 then (if id = 106 then some localCycle00106 else none) else (if id < 108 then (if id = 107 then some localCycle00107 else none) else (if id = 108 then some localCycle00108 else none)))) else (if id < 112 then (if id < 110 then (if id = 109 then some localCycle00109 else none) else (if id < 111 then (if id = 110 then some localCycle00110 else none) else (if id = 111 then some localCycle00111 else none))) else (if id < 113 then (if id = 112 then some localCycle00112 else none) else (if id < 114 then (if id = 113 then some localCycle00113 else none) else (if id = 114 then some localCycle00114 else none))))) else (if id < 121 then (if id < 118 then (if id < 116 then (if id = 115 then some localCycle00115 else none) else (if id < 117 then (if id = 116 then some localCycle00116 else none) else (if id = 117 then some localCycle00117 else none))) else (if id < 119 then (if id = 118 then some localCycle00118 else none) else (if id < 120 then (if id = 119 then some localCycle00119 else none) else (if id = 120 then some localCycle00120 else none)))) else (if id < 124 then (if id < 122 then (if id = 121 then some localCycle00121 else none) else (if id < 123 then (if id = 122 then some localCycle00122 else none) else (if id = 123 then some localCycle00123 else none))) else (if id < 126 then (if id < 125 then (if id = 124 then some localCycle00124 else none) else (if id = 125 then some localCycle00125 else none)) else (if id < 127 then (if id = 126 then some localCycle00126 else none) else (if id = 127 then some localCycle00127 else none)))))) else (if id < 141 then (if id < 134 then (if id < 131 then (if id < 129 then (if id = 128 then some localCycle00128 else none) else (if id < 130 then (if id = 129 then some localCycle00129 else none) else (if id = 130 then some localCycle00130 else none))) else (if id < 132 then (if id = 131 then some localCycle00131 else none) else (if id < 133 then (if id = 132 then some localCycle00132 else none) else (if id = 133 then some localCycle00133 else none)))) else (if id < 137 then (if id < 135 then (if id = 134 then some localCycle00134 else none) else (if id < 136 then (if id = 135 then some localCycle00135 else none) else (if id = 136 then some localCycle00136 else none))) else (if id < 139 then (if id < 138 then (if id = 137 then some localCycle00137 else none) else (if id = 138 then some localCycle00138 else none)) else (if id < 140 then (if id = 139 then some localCycle00139 else none) else (if id = 140 then some localCycle00140 else none))))) else (if id < 147 then (if id < 144 then (if id < 142 then (if id = 141 then some localCycle00141 else none) else (if id < 143 then (if id = 142 then some localCycle00142 else none) else (if id = 143 then some localCycle00143 else none))) else (if id < 145 then (if id = 144 then some localCycle00144 else none) else (if id < 146 then (if id = 145 then some localCycle00145 else none) else (if id = 146 then some localCycle00146 else none)))) else (if id < 150 then (if id < 148 then (if id = 147 then some localCycle00147 else none) else (if id < 149 then (if id = 148 then some localCycle00148 else none) else (if id = 149 then some localCycle00149 else none))) else (if id < 152 then (if id < 151 then (if id = 150 then some localCycle00150 else none) else (if id = 151 then some localCycle00151 else none)) else (if id < 153 then (if id = 152 then some localCycle00152 else none) else (if id = 153 then some localCycle00153 else none))))))) else (if id < 180 then (if id < 167 then (if id < 160 then (if id < 157 then (if id < 155 then (if id = 154 then some localCycle00154 else none) else (if id < 156 then (if id = 155 then some localCycle00155 else none) else (if id = 156 then some localCycle00156 else none))) else (if id < 158 then (if id = 157 then some localCycle00157 else none) else (if id < 159 then (if id = 158 then some localCycle00158 else none) else (if id = 159 then some localCycle00159 else none)))) else (if id < 163 then (if id < 161 then (if id = 160 then some localCycle00160 else none) else (if id < 162 then (if id = 161 then some localCycle00161 else none) else (if id = 162 then some localCycle00162 else none))) else (if id < 165 then (if id < 164 then (if id = 163 then some localCycle00163 else none) else (if id = 164 then some localCycle00164 else none)) else (if id < 166 then (if id = 165 then some localCycle00165 else none) else (if id = 166 then some localCycle00166 else none))))) else (if id < 173 then (if id < 170 then (if id < 168 then (if id = 167 then some localCycle00167 else none) else (if id < 169 then (if id = 168 then some localCycle00168 else none) else (if id = 169 then some localCycle00169 else none))) else (if id < 171 then (if id = 170 then some localCycle00170 else none) else (if id < 172 then (if id = 171 then some localCycle00171 else none) else (if id = 172 then some localCycle00172 else none)))) else (if id < 176 then (if id < 174 then (if id = 173 then some localCycle00173 else none) else (if id < 175 then (if id = 174 then some localCycle00174 else none) else (if id = 175 then some localCycle00175 else none))) else (if id < 178 then (if id < 177 then (if id = 176 then some localCycle00176 else none) else (if id = 177 then some localCycle00177 else none)) else (if id < 179 then (if id = 178 then some localCycle00178 else none) else (if id = 179 then some localCycle00179 else none)))))) else (if id < 193 then (if id < 186 then (if id < 183 then (if id < 181 then (if id = 180 then some localCycle00180 else none) else (if id < 182 then (if id = 181 then some localCycle00181 else none) else (if id = 182 then some localCycle00182 else none))) else (if id < 184 then (if id = 183 then some localCycle00183 else none) else (if id < 185 then (if id = 184 then some localCycle00184 else none) else (if id = 185 then some localCycle00185 else none)))) else (if id < 189 then (if id < 187 then (if id = 186 then some localCycle00186 else none) else (if id < 188 then (if id = 187 then some localCycle00187 else none) else (if id = 188 then some localCycle00188 else none))) else (if id < 191 then (if id < 190 then (if id = 189 then some localCycle00189 else none) else (if id = 190 then some localCycle00190 else none)) else (if id < 192 then (if id = 191 then some localCycle00191 else none) else (if id = 192 then some localCycle00192 else none))))) else (if id < 199 then (if id < 196 then (if id < 194 then (if id = 193 then some localCycle00193 else none) else (if id < 195 then (if id = 194 then some localCycle00194 else none) else (if id = 195 then some localCycle00195 else none))) else (if id < 197 then (if id = 196 then some localCycle00196 else none) else (if id < 198 then (if id = 197 then some localCycle00197 else none) else (if id = 198 then some localCycle00198 else none)))) else (if id < 202 then (if id < 200 then (if id = 199 then some localCycle00199 else none) else (if id < 201 then (if id = 200 then some localCycle00200 else none) else (if id = 201 then some localCycle00201 else none))) else (if id < 204 then (if id < 203 then (if id = 202 then some localCycle00202 else none) else (if id = 203 then some localCycle00203 else none)) else (if id < 205 then (if id = 204 then some localCycle00204 else none) else (if id = 205 then some localCycle00205 else none))))))))

def namedLeaf000 : LeafData := { rows := ![![1, 2, 4, 5, 3, 6], ![0, 2, 5, 4, 6, 3], ![0, 1, 6, 5, 4, 3], ![4, 5, 0, 6, 1, 2], ![3, 0, 5, 1, 6, 2], ![3, 0, 4, 1, 6, 2], ![0, 3, 1, 4, 5, 2]], proof := .tail 49 }

theorem namedLeaf000_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2688)) namedLeaf000 = true :=
  by decide +kernel

def namedLeaf001 : LeafData := { rows := ![![1, 2, 4, 5, 3, 6], ![0, 2, 5, 6, 4, 3], ![0, 1, 5, 6, 4, 3], ![4, 5, 0, 6, 1, 2], ![3, 0, 5, 6, 1, 2], ![3, 0, 4, 1, 2, 6], ![0, 3, 4, 1, 2, 5]], proof := .tail 32 }

theorem namedLeaf001_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2689)) namedLeaf001 = true :=
  by decide +kernel

def namedLeaf002 : LeafData := { rows := ![![1, 2, 4, 5, 3, 6], ![0, 2, 5, 6, 4, 3], ![0, 1, 6, 5, 4, 3], ![4, 5, 0, 6, 1, 2], ![3, 0, 5, 6, 1, 2], ![3, 0, 4, 1, 6, 2], ![0, 3, 4, 1, 5, 2]], proof := .tail 105 }

theorem namedLeaf002_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2690)) namedLeaf002 = true :=
  by decide +kernel

def namedLeaf003 : LeafData := { rows := ![![1, 2, 4, 5, 3, 6], ![0, 2, 6, 5, 4, 3], ![0, 1, 6, 5, 4, 3], ![4, 5, 0, 6, 1, 2], ![3, 0, 5, 6, 1, 2], ![3, 0, 4, 6, 1, 2], ![0, 3, 4, 5, 1, 2]], proof := .tail 164 }

theorem namedLeaf003_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2691)) namedLeaf003 = true :=
  by decide +kernel

def namedLeaf004 : LeafData := { rows := ![![1, 2, 4, 5, 3, 6], ![0, 2, 6, 5, 4, 3], ![0, 1, 6, 5, 4, 3], ![4, 5, 0, 6, 1, 2], ![3, 0, 6, 5, 1, 2], ![3, 0, 6, 4, 1, 2], ![0, 3, 5, 4, 1, 2]], proof := .tail 25 }

theorem namedLeaf004_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2692)) namedLeaf004 = true :=
  by decide +kernel

def namedLeaf005 : LeafData := { rows := ![![1, 2, 4, 5, 3, 6], ![0, 6, 2, 4, 5, 3], ![0, 6, 1, 4, 5, 3], ![4, 5, 0, 6, 1, 2], ![3, 0, 6, 1, 2, 5], ![3, 0, 6, 1, 2, 4], ![0, 3, 5, 4, 2, 1]], proof := .tail 28 }

theorem namedLeaf005_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2693)) namedLeaf005 = true :=
  by decide +kernel

def namedLeaf006 : LeafData := { rows := ![![1, 2, 4, 5, 3, 6], ![0, 6, 2, 4, 5, 3], ![0, 6, 1, 5, 4, 3], ![4, 5, 0, 6, 1, 2], ![3, 0, 6, 1, 5, 2], ![3, 0, 6, 1, 4, 2], ![0, 3, 5, 4, 2, 1]], proof := .tail 11 }

theorem namedLeaf006_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2694)) namedLeaf006 = true :=
  by decide +kernel

def namedLeaf007 : LeafData := { rows := ![![1, 2, 4, 5, 3, 6], ![0, 6, 2, 5, 4, 3], ![0, 6, 1, 5, 4, 3], ![4, 5, 0, 6, 1, 2], ![3, 0, 5, 6, 1, 2], ![3, 0, 4, 6, 1, 2], ![0, 3, 4, 5, 2, 1]], proof := .tail 65 }

theorem namedLeaf007_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2695)) namedLeaf007 = true :=
  by decide +kernel

def namedLeaf008 : LeafData := { rows := ![![1, 2, 4, 5, 3, 6], ![0, 6, 2, 5, 4, 3], ![0, 6, 1, 5, 4, 3], ![4, 5, 0, 6, 1, 2], ![3, 0, 6, 5, 1, 2], ![3, 0, 6, 4, 1, 2], ![0, 3, 5, 4, 2, 1]], proof := .tail 172 }

theorem namedLeaf008_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2696)) namedLeaf008 = true :=
  by decide +kernel

def namedLeaf009 : LeafData := { rows := ![![1, 2, 4, 5, 3, 6], ![0, 5, 2, 4, 6, 3], ![0, 5, 1, 4, 6, 3], ![4, 5, 0, 6, 1, 2], ![3, 0, 5, 1, 2, 6], ![3, 0, 4, 2, 1, 6], ![0, 3, 1, 2, 4, 5]], proof := .tail 61 }

theorem namedLeaf009_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2697)) namedLeaf009 = true :=
  by decide +kernel

def namedLeaf010 : LeafData := { rows := ![![1, 2, 4, 5, 3, 6], ![0, 5, 2, 4, 6, 3], ![0, 5, 1, 6, 4, 3], ![4, 5, 0, 6, 1, 2], ![3, 0, 5, 1, 6, 2], ![3, 0, 4, 2, 1, 6], ![0, 3, 1, 4, 2, 5]], proof := .tail 191 }

theorem namedLeaf010_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2698)) namedLeaf010 = true :=
  by decide +kernel

def namedLeaf011 : LeafData := { rows := ![![1, 2, 4, 5, 3, 6], ![0, 5, 2, 6, 4, 3], ![0, 5, 1, 6, 4, 3], ![4, 5, 0, 6, 1, 2], ![3, 0, 5, 6, 1, 2], ![3, 0, 4, 2, 1, 6], ![0, 3, 4, 1, 2, 5]], proof := .tail 99 }

theorem namedLeaf011_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2699)) namedLeaf011 = true :=
  by decide +kernel

def namedLeaf012 : LeafData := { rows := ![![1, 2, 4, 5, 3, 6], ![0, 5, 6, 2, 4, 3], ![0, 5, 6, 1, 4, 3], ![4, 5, 0, 6, 1, 2], ![3, 0, 5, 6, 1, 2], ![3, 0, 4, 2, 1, 6], ![0, 3, 4, 2, 1, 5]], proof := .tail 0 }

theorem namedLeaf012_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2700)) namedLeaf012 = true :=
  by decide +kernel

def namedLeaf013 : LeafData := { rows := ![![1, 2, 4, 5, 3, 6], ![0, 6, 5, 2, 4, 3], ![0, 5, 6, 1, 4, 3], ![4, 5, 0, 6, 1, 2], ![3, 0, 5, 6, 1, 2], ![3, 0, 4, 2, 6, 1], ![0, 3, 4, 2, 5, 1]], proof := .tail 129 }

theorem namedLeaf013_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2701)) namedLeaf013 = true :=
  by decide +kernel

def namedLeaf014 : LeafData := { rows := ![![1, 2, 4, 5, 3, 6], ![0, 6, 5, 2, 4, 3], ![0, 6, 5, 1, 4, 3], ![4, 5, 0, 6, 1, 2], ![3, 0, 5, 6, 1, 2], ![3, 0, 4, 6, 2, 1], ![0, 3, 4, 5, 2, 1]], proof := .tail 95 }

theorem namedLeaf014_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2702)) namedLeaf014 = true :=
  by decide +kernel

def namedLeaf015 : LeafData := { rows := ![![1, 2, 4, 5, 3, 6], ![0, 6, 5, 2, 4, 3], ![0, 6, 5, 1, 4, 3], ![4, 5, 0, 6, 1, 2], ![3, 0, 6, 5, 1, 2], ![3, 0, 6, 4, 2, 1], ![0, 3, 5, 4, 2, 1]], proof := .tail 114 }

theorem namedLeaf015_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2703)) namedLeaf015 = true :=
  by decide +kernel

def namedLeaf016 : LeafData := { rows := ![![1, 2, 4, 5, 3, 6], ![0, 4, 2, 5, 6, 3], ![0, 4, 1, 5, 6, 3], ![4, 5, 0, 6, 1, 2], ![3, 0, 2, 1, 5, 6], ![3, 0, 1, 2, 4, 6], ![0, 3, 1, 2, 4, 5]], proof := .tail 177 }

theorem namedLeaf016_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2704)) namedLeaf016 = true :=
  by decide +kernel

def namedLeaf017 : LeafData := { rows := ![![1, 2, 4, 5, 3, 6], ![0, 4, 2, 5, 6, 3], ![0, 4, 1, 5, 6, 3], ![4, 5, 0, 6, 1, 2], ![3, 0, 2, 1, 6, 5], ![3, 0, 1, 2, 6, 4], ![0, 3, 1, 2, 5, 4]], proof := .tail 5 }

theorem namedLeaf017_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2705)) namedLeaf017 = true :=
  by decide +kernel

def namedLeaf018 : LeafData := { rows := ![![1, 2, 4, 5, 3, 6], ![0, 4, 2, 5, 6, 3], ![0, 4, 1, 6, 5, 3], ![4, 5, 0, 6, 1, 2], ![3, 0, 2, 1, 6, 5], ![3, 0, 1, 6, 2, 4], ![0, 3, 1, 5, 2, 4]], proof := .tail 96 }

theorem namedLeaf018_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2706)) namedLeaf018 = true :=
  by decide +kernel

def namedLeaf019 : LeafData := { rows := ![![1, 2, 4, 5, 3, 6], ![0, 4, 2, 6, 5, 3], ![0, 4, 1, 6, 5, 3], ![4, 5, 0, 6, 1, 2], ![3, 0, 2, 1, 6, 5], ![3, 0, 6, 1, 2, 4], ![0, 3, 5, 1, 2, 4]], proof := .tail 51 }

theorem namedLeaf019_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2707)) namedLeaf019 = true :=
  by decide +kernel

def namedLeaf020 : LeafData := { rows := ![![1, 2, 4, 5, 3, 6], ![0, 4, 6, 2, 5, 3], ![0, 4, 6, 1, 5, 3], ![4, 5, 0, 6, 1, 2], ![3, 0, 2, 1, 6, 5], ![3, 0, 6, 1, 2, 4], ![0, 3, 5, 2, 1, 4]], proof := .tail 93 }

theorem namedLeaf020_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2708)) namedLeaf020 = true :=
  by decide +kernel

def namedLeaf021 : LeafData := { rows := ![![1, 2, 4, 5, 3, 6], ![0, 6, 4, 2, 5, 3], ![0, 4, 6, 1, 5, 3], ![4, 5, 0, 6, 1, 2], ![3, 0, 2, 6, 1, 5], ![3, 0, 6, 1, 2, 4], ![0, 3, 5, 2, 4, 1]], proof := .tail 10 }

theorem namedLeaf021_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2709)) namedLeaf021 = true :=
  by decide +kernel

def namedLeaf022 : LeafData := { rows := ![![1, 2, 4, 5, 3, 6], ![0, 6, 4, 2, 5, 3], ![0, 6, 4, 1, 5, 3], ![4, 5, 0, 6, 1, 2], ![3, 0, 6, 2, 1, 5], ![3, 0, 6, 1, 2, 4], ![0, 3, 5, 4, 2, 1]], proof := .tail 138 }

theorem namedLeaf022_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2710)) namedLeaf022 = true :=
  by decide +kernel

def namedLeaf023 : LeafData := { rows := ![![1, 2, 4, 5, 3, 6], ![0, 4, 5, 2, 6, 3], ![0, 4, 5, 1, 6, 3], ![4, 5, 0, 6, 1, 2], ![3, 0, 2, 1, 5, 6], ![3, 0, 2, 1, 4, 6], ![0, 3, 1, 2, 4, 5]], proof := .tail 135 }

theorem namedLeaf023_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2711)) namedLeaf023 = true :=
  by decide +kernel

def namedLeaf024 : LeafData := { rows := ![![1, 2, 4, 5, 3, 6], ![0, 4, 5, 2, 6, 3], ![0, 4, 5, 1, 6, 3], ![4, 5, 0, 6, 1, 2], ![3, 0, 2, 1, 6, 5], ![3, 0, 2, 1, 6, 4], ![0, 3, 1, 2, 5, 4]], proof := .tail 77 }

theorem namedLeaf024_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2712)) namedLeaf024 = true :=
  by decide +kernel

def namedLeaf025 : LeafData := { rows := ![![1, 2, 4, 5, 3, 6], ![0, 5, 4, 2, 6, 3], ![0, 4, 5, 1, 6, 3], ![4, 5, 0, 6, 1, 2], ![3, 0, 2, 5, 1, 6], ![3, 0, 2, 4, 1, 6], ![0, 3, 1, 2, 4, 5]], proof := .tail 188 }

theorem namedLeaf025_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2713)) namedLeaf025 = true :=
  by decide +kernel

def namedLeaf026 : LeafData := { rows := ![![1, 2, 4, 5, 3, 6], ![0, 5, 4, 2, 6, 3], ![0, 5, 4, 1, 6, 3], ![4, 5, 0, 6, 1, 2], ![3, 0, 5, 2, 1, 6], ![3, 0, 4, 2, 1, 6], ![0, 3, 1, 2, 4, 5]], proof := .tail 171 }

theorem namedLeaf026_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2714)) namedLeaf026 = true :=
  by decide +kernel

def namedLeaf027 : LeafData := { rows := ![![1, 2, 4, 5, 3, 6], ![0, 4, 5, 6, 2, 3], ![0, 4, 5, 6, 1, 3], ![4, 5, 0, 6, 1, 2], ![3, 0, 2, 1, 5, 6], ![3, 0, 2, 1, 4, 6], ![0, 3, 2, 1, 4, 5]], proof := .tail 200 }

theorem namedLeaf027_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2715)) namedLeaf027 = true :=
  by decide +kernel

def namedLeaf028 : LeafData := { rows := ![![1, 2, 4, 5, 3, 6], ![0, 4, 5, 6, 2, 3], ![0, 4, 5, 6, 1, 3], ![4, 5, 0, 6, 1, 2], ![3, 0, 2, 1, 6, 5], ![3, 0, 2, 1, 6, 4], ![0, 3, 2, 1, 5, 4]], proof := .tail 200 }

theorem namedLeaf028_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2716)) namedLeaf028 = true :=
  by decide +kernel

def namedLeaf029 : LeafData := { rows := ![![1, 2, 4, 5, 3, 6], ![0, 4, 6, 5, 2, 3], ![0, 4, 5, 6, 1, 3], ![4, 5, 0, 6, 1, 2], ![3, 0, 2, 1, 6, 5], ![3, 0, 2, 6, 1, 4], ![0, 3, 2, 5, 1, 4]], proof := .tail 167 }

theorem namedLeaf029_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2717)) namedLeaf029 = true :=
  by decide +kernel

def namedLeaf030 : LeafData := { rows := ![![1, 2, 4, 5, 3, 6], ![0, 4, 6, 5, 2, 3], ![0, 4, 6, 5, 1, 3], ![4, 5, 0, 6, 1, 2], ![3, 0, 2, 1, 6, 5], ![3, 0, 6, 2, 1, 4], ![0, 3, 5, 2, 1, 4]], proof := .tail 47 }

theorem namedLeaf030_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2718)) namedLeaf030 = true :=
  by decide +kernel

def namedLeaf031 : LeafData := { rows := ![![1, 2, 4, 5, 3, 6], ![0, 6, 4, 5, 2, 3], ![0, 4, 5, 6, 1, 3], ![4, 5, 0, 6, 1, 2], ![3, 0, 2, 6, 1, 5], ![3, 0, 2, 6, 1, 4], ![0, 3, 2, 5, 4, 1]], proof := .tail 62 }

theorem namedLeaf031_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2719)) namedLeaf031 = true :=
  by decide +kernel

def namedLeaf032 : LeafData := { rows := ![![1, 2, 4, 5, 3, 6], ![0, 6, 4, 5, 2, 3], ![0, 4, 6, 5, 1, 3], ![4, 5, 0, 6, 1, 2], ![3, 0, 2, 6, 1, 5], ![3, 0, 6, 2, 1, 4], ![0, 3, 5, 2, 4, 1]], proof := .tail 47 }

theorem namedLeaf032_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2720)) namedLeaf032 = true :=
  by decide +kernel

def namedLeaf033 : LeafData := { rows := ![![1, 2, 4, 5, 3, 6], ![0, 6, 4, 5, 2, 3], ![0, 6, 4, 5, 1, 3], ![4, 5, 0, 6, 1, 2], ![3, 0, 6, 2, 1, 5], ![3, 0, 6, 2, 1, 4], ![0, 3, 5, 4, 2, 1]], proof := .tail 64 }

theorem namedLeaf033_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2721)) namedLeaf033 = true :=
  by decide +kernel

def namedLeaf034 : LeafData := { rows := ![![1, 2, 4, 5, 3, 6], ![0, 5, 4, 6, 2, 3], ![0, 4, 5, 6, 1, 3], ![4, 5, 0, 6, 1, 2], ![3, 0, 2, 5, 1, 6], ![3, 0, 2, 4, 1, 6], ![0, 3, 2, 1, 4, 5]], proof := .tail 199 }

theorem namedLeaf034_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2722)) namedLeaf034 = true :=
  by decide +kernel

def namedLeaf035 : LeafData := { rows := ![![1, 2, 4, 5, 3, 6], ![0, 5, 4, 6, 2, 3], ![0, 5, 4, 6, 1, 3], ![4, 5, 0, 6, 1, 2], ![3, 0, 5, 2, 1, 6], ![3, 0, 4, 2, 1, 6], ![0, 3, 2, 1, 4, 5]], proof := .tail 91 }

theorem namedLeaf035_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2723)) namedLeaf035 = true :=
  by decide +kernel

def namedLeaf036 : LeafData := { rows := ![![1, 2, 4, 5, 3, 6], ![0, 5, 6, 4, 2, 3], ![0, 4, 5, 6, 1, 3], ![4, 5, 0, 6, 1, 2], ![3, 0, 2, 5, 6, 1], ![3, 0, 2, 4, 1, 6], ![0, 3, 2, 4, 1, 5]], proof := .tail 184 }

theorem namedLeaf036_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2724)) namedLeaf036 = true :=
  by decide +kernel

def namedLeaf037 : LeafData := { rows := ![![1, 2, 4, 5, 3, 6], ![0, 5, 6, 4, 2, 3], ![0, 5, 4, 6, 1, 3], ![4, 5, 0, 6, 1, 2], ![3, 0, 5, 2, 6, 1], ![3, 0, 4, 2, 1, 6], ![0, 3, 2, 4, 1, 5]], proof := .tail 108 }

theorem namedLeaf037_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2725)) namedLeaf037 = true :=
  by decide +kernel

def namedLeaf038 : LeafData := { rows := ![![1, 2, 4, 5, 3, 6], ![0, 5, 6, 4, 2, 3], ![0, 5, 6, 4, 1, 3], ![4, 5, 0, 6, 1, 2], ![3, 0, 5, 6, 2, 1], ![3, 0, 4, 2, 1, 6], ![0, 3, 4, 2, 1, 5]], proof := .tail 58 }

theorem namedLeaf038_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2726)) namedLeaf038 = true :=
  by decide +kernel

def namedLeaf039 : LeafData := { rows := ![![1, 2, 4, 5, 3, 6], ![0, 6, 5, 4, 2, 3], ![0, 4, 5, 6, 1, 3], ![4, 5, 0, 6, 1, 2], ![3, 0, 2, 5, 6, 1], ![3, 0, 2, 4, 6, 1], ![0, 3, 2, 4, 5, 1]], proof := .tail 128 }

theorem namedLeaf039_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2727)) namedLeaf039 = true :=
  by decide +kernel

def namedLeaf040 : LeafData := { rows := ![![1, 2, 4, 5, 3, 6], ![0, 6, 5, 4, 2, 3], ![0, 4, 5, 6, 1, 3], ![4, 5, 0, 6, 1, 2], ![3, 0, 2, 6, 5, 1], ![3, 0, 2, 6, 4, 1], ![0, 3, 2, 5, 4, 1]], proof := .tail 143 }

theorem namedLeaf040_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2728)) namedLeaf040 = true :=
  by decide +kernel

def namedLeaf041 : LeafData := { rows := ![![1, 2, 4, 5, 3, 6], ![0, 6, 5, 4, 2, 3], ![0, 4, 6, 5, 1, 3], ![4, 5, 0, 6, 1, 2], ![3, 0, 2, 6, 5, 1], ![3, 0, 6, 2, 4, 1], ![0, 3, 5, 2, 4, 1]], proof := .tail 152 }

theorem namedLeaf041_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2729)) namedLeaf041 = true :=
  by decide +kernel

def namedLeaf042 : LeafData := { rows := ![![1, 2, 4, 5, 3, 6], ![0, 6, 5, 4, 2, 3], ![0, 6, 4, 5, 1, 3], ![4, 5, 0, 6, 1, 2], ![3, 0, 6, 2, 5, 1], ![3, 0, 6, 2, 4, 1], ![0, 3, 5, 4, 2, 1]], proof := .tail 59 }

theorem namedLeaf042_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2730)) namedLeaf042 = true :=
  by decide +kernel

def namedLeaf043 : LeafData := { rows := ![![1, 2, 4, 5, 3, 6], ![0, 6, 5, 4, 2, 3], ![0, 5, 4, 6, 1, 3], ![4, 5, 0, 6, 1, 2], ![3, 0, 5, 2, 6, 1], ![3, 0, 4, 2, 6, 1], ![0, 3, 2, 4, 5, 1]], proof := .tail 43 }

theorem namedLeaf043_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2731)) namedLeaf043 = true :=
  by decide +kernel

def namedLeaf044 : LeafData := { rows := ![![1, 2, 4, 5, 3, 6], ![0, 6, 5, 4, 2, 3], ![0, 5, 6, 4, 1, 3], ![4, 5, 0, 6, 1, 2], ![3, 0, 5, 6, 2, 1], ![3, 0, 4, 2, 6, 1], ![0, 3, 4, 2, 5, 1]], proof := .tail 128 }

theorem namedLeaf044_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2732)) namedLeaf044 = true :=
  by decide +kernel

def namedLeaf045 : LeafData := { rows := ![![1, 2, 4, 5, 3, 6], ![0, 6, 5, 4, 2, 3], ![0, 6, 5, 4, 1, 3], ![4, 5, 0, 6, 1, 2], ![3, 0, 5, 6, 2, 1], ![3, 0, 4, 6, 2, 1], ![0, 3, 4, 5, 2, 1]], proof := .tail 132 }

theorem namedLeaf045_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2733)) namedLeaf045 = true :=
  by decide +kernel

def namedLeaf046 : LeafData := { rows := ![![1, 2, 4, 5, 3, 6], ![0, 6, 5, 4, 2, 3], ![0, 6, 5, 4, 1, 3], ![4, 5, 0, 6, 1, 2], ![3, 0, 6, 5, 2, 1], ![3, 0, 6, 4, 2, 1], ![0, 3, 5, 4, 2, 1]], proof := .tail 50 }

theorem namedLeaf046_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2734)) namedLeaf046 = true :=
  by decide +kernel

def namedLeaf047 : LeafData := { rows := ![![1, 2, 5, 4, 3, 6], ![0, 2, 5, 4, 3, 6], ![0, 1, 5, 4, 3, 6], ![4, 5, 0, 1, 2, 6], ![3, 5, 0, 1, 2, 6], ![3, 4, 0, 1, 2, 6], ![0, 1, 2, 3, 4, 5]], proof := .tail 140 }

theorem namedLeaf047_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2735)) namedLeaf047 = true :=
  by decide +kernel

def namedLeaf048 : LeafData := { rows := ![![1, 2, 5, 4, 3, 6], ![0, 2, 5, 4, 3, 6], ![0, 1, 5, 4, 6, 3], ![4, 5, 0, 1, 6, 2], ![3, 5, 0, 1, 2, 6], ![3, 4, 0, 1, 2, 6], ![0, 1, 3, 2, 4, 5]], proof := .tail 156 }

theorem namedLeaf048_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2736)) namedLeaf048 = true :=
  by decide +kernel

def namedLeaf049 : LeafData := { rows := ![![1, 2, 5, 4, 3, 6], ![0, 2, 5, 4, 3, 6], ![0, 1, 5, 6, 4, 3], ![4, 5, 0, 1, 6, 2], ![3, 5, 0, 1, 6, 2], ![3, 4, 0, 1, 2, 6], ![0, 1, 3, 4, 2, 5]], proof := .tail 4 }

theorem namedLeaf049_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2737)) namedLeaf049 = true :=
  by decide +kernel

def namedLeaf050 : LeafData := { rows := ![![1, 2, 5, 4, 3, 6], ![0, 2, 5, 4, 3, 6], ![0, 1, 6, 5, 4, 3], ![4, 5, 0, 1, 6, 2], ![3, 5, 0, 1, 6, 2], ![3, 4, 0, 1, 6, 2], ![0, 1, 3, 4, 5, 2]], proof := .tail 105 }

theorem namedLeaf050_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2738)) namedLeaf050 = true :=
  by decide +kernel

def namedLeaf051 : LeafData := { rows := ![![1, 2, 5, 4, 3, 6], ![0, 2, 5, 4, 6, 3], ![0, 1, 5, 4, 6, 3], ![4, 5, 0, 6, 1, 2], ![3, 5, 0, 1, 2, 6], ![3, 4, 0, 1, 2, 6], ![0, 3, 1, 2, 4, 5]], proof := .tail 198 }

theorem namedLeaf051_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2739)) namedLeaf051 = true :=
  by decide +kernel

def namedLeaf052 : LeafData := { rows := ![![1, 2, 5, 4, 3, 6], ![0, 2, 5, 4, 6, 3], ![0, 1, 5, 6, 4, 3], ![4, 5, 0, 6, 1, 2], ![3, 5, 0, 1, 6, 2], ![3, 4, 0, 1, 2, 6], ![0, 3, 1, 4, 2, 5]], proof := .tail 41 }

theorem namedLeaf052_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2740)) namedLeaf052 = true :=
  by decide +kernel

def namedLeaf053 : LeafData := { rows := ![![1, 2, 5, 4, 3, 6], ![0, 2, 5, 4, 6, 3], ![0, 1, 6, 5, 4, 3], ![4, 5, 0, 6, 1, 2], ![3, 5, 0, 1, 6, 2], ![3, 4, 0, 1, 6, 2], ![0, 3, 1, 4, 5, 2]], proof := .tail 105 }

theorem namedLeaf053_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2741)) namedLeaf053 = true :=
  by decide +kernel

def namedLeaf054 : LeafData := { rows := ![![1, 2, 5, 4, 3, 6], ![0, 2, 5, 6, 4, 3], ![0, 1, 5, 6, 4, 3], ![4, 5, 0, 6, 1, 2], ![3, 5, 0, 6, 1, 2], ![3, 4, 0, 1, 2, 6], ![0, 3, 4, 1, 2, 5]], proof := .tail 106 }

theorem namedLeaf054_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2742)) namedLeaf054 = true :=
  by decide +kernel

def namedLeaf055 : LeafData := { rows := ![![1, 2, 5, 4, 3, 6], ![0, 2, 5, 6, 4, 3], ![0, 1, 6, 5, 4, 3], ![4, 5, 0, 6, 1, 2], ![3, 5, 0, 6, 1, 2], ![3, 4, 0, 1, 6, 2], ![0, 3, 4, 1, 5, 2]], proof := .tail 105 }

theorem namedLeaf055_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2743)) namedLeaf055 = true :=
  by decide +kernel

def namedLeaf056 : LeafData := { rows := ![![1, 2, 5, 4, 3, 6], ![0, 2, 6, 5, 4, 3], ![0, 1, 6, 5, 4, 3], ![4, 5, 0, 6, 1, 2], ![3, 5, 0, 6, 1, 2], ![3, 4, 0, 6, 1, 2], ![0, 3, 4, 5, 1, 2]], proof := .tail 164 }

theorem namedLeaf056_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2744)) namedLeaf056 = true :=
  by decide +kernel

def namedLeaf057 : LeafData := { rows := ![![1, 2, 5, 4, 3, 6], ![0, 6, 2, 5, 4, 3], ![0, 6, 1, 5, 4, 3], ![4, 5, 0, 6, 1, 2], ![3, 5, 0, 6, 1, 2], ![3, 4, 0, 6, 1, 2], ![0, 3, 4, 5, 2, 1]], proof := .tail 65 }

theorem namedLeaf057_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2745)) namedLeaf057 = true :=
  by decide +kernel

def namedLeaf058 : LeafData := { rows := ![![1, 2, 5, 4, 3, 6], ![0, 5, 2, 4, 3, 6], ![0, 5, 1, 4, 3, 6], ![4, 5, 0, 1, 2, 6], ![3, 5, 0, 1, 2, 6], ![3, 4, 0, 2, 1, 6], ![0, 1, 2, 3, 4, 5]], proof := .tail 182 }

theorem namedLeaf058_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2746)) namedLeaf058 = true :=
  by decide +kernel

def namedLeaf059 : LeafData := { rows := ![![1, 2, 5, 4, 3, 6], ![0, 5, 2, 4, 3, 6], ![0, 5, 1, 4, 6, 3], ![4, 5, 0, 1, 6, 2], ![3, 5, 0, 1, 2, 6], ![3, 4, 0, 2, 1, 6], ![0, 1, 3, 2, 4, 5]], proof := .tail 156 }

theorem namedLeaf059_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2747)) namedLeaf059 = true :=
  by decide +kernel

def namedLeaf060 : LeafData := { rows := ![![1, 2, 5, 4, 3, 6], ![0, 5, 2, 4, 3, 6], ![0, 5, 1, 6, 4, 3], ![4, 5, 0, 1, 6, 2], ![3, 5, 0, 1, 6, 2], ![3, 4, 0, 2, 1, 6], ![0, 1, 3, 4, 2, 5]], proof := .tail 4 }

theorem namedLeaf060_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2748)) namedLeaf060 = true :=
  by decide +kernel

def namedLeaf061 : LeafData := { rows := ![![1, 2, 5, 4, 3, 6], ![0, 5, 2, 4, 6, 3], ![0, 5, 1, 4, 6, 3], ![4, 5, 0, 6, 1, 2], ![3, 5, 0, 1, 2, 6], ![3, 4, 0, 2, 1, 6], ![0, 3, 1, 2, 4, 5]], proof := .tail 61 }

theorem namedLeaf061_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2749)) namedLeaf061 = true :=
  by decide +kernel

def namedLeaf062 : LeafData := { rows := ![![1, 2, 5, 4, 3, 6], ![0, 5, 2, 4, 6, 3], ![0, 5, 1, 6, 4, 3], ![4, 5, 0, 6, 1, 2], ![3, 5, 0, 1, 6, 2], ![3, 4, 0, 2, 1, 6], ![0, 3, 1, 4, 2, 5]], proof := .tail 41 }

theorem namedLeaf062_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2750)) namedLeaf062 = true :=
  by decide +kernel

def namedLeaf063 : LeafData := { rows := ![![1, 2, 5, 4, 3, 6], ![0, 5, 2, 6, 4, 3], ![0, 5, 1, 6, 4, 3], ![4, 5, 0, 6, 1, 2], ![3, 5, 0, 6, 1, 2], ![3, 4, 0, 2, 1, 6], ![0, 3, 4, 1, 2, 5]], proof := .tail 106 }

theorem namedLeaf063_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2751)) namedLeaf063 = true :=
  by decide +kernel

def namedLeaf064 : LeafData := { rows := ![![1, 2, 5, 4, 3, 6], ![0, 5, 6, 2, 4, 3], ![0, 5, 6, 1, 4, 3], ![4, 5, 0, 6, 1, 2], ![3, 5, 0, 6, 1, 2], ![3, 4, 0, 2, 1, 6], ![0, 3, 4, 2, 1, 5]], proof := .tail 45 }

theorem namedLeaf064_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2752)) namedLeaf064 = true :=
  by decide +kernel

def namedLeaf065 : LeafData := { rows := ![![1, 2, 5, 4, 3, 6], ![0, 6, 5, 2, 4, 3], ![0, 5, 6, 1, 4, 3], ![4, 5, 0, 6, 1, 2], ![3, 5, 0, 6, 1, 2], ![3, 4, 0, 2, 6, 1], ![0, 3, 4, 2, 5, 1]], proof := .tail 129 }

theorem namedLeaf065_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2753)) namedLeaf065 = true :=
  by decide +kernel

def namedLeaf066 : LeafData := { rows := ![![1, 2, 5, 4, 3, 6], ![0, 6, 5, 2, 4, 3], ![0, 6, 5, 1, 4, 3], ![4, 5, 0, 6, 1, 2], ![3, 5, 0, 6, 1, 2], ![3, 4, 0, 6, 2, 1], ![0, 3, 4, 5, 2, 1]], proof := .tail 95 }

theorem namedLeaf066_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2754)) namedLeaf066 = true :=
  by decide +kernel

def namedLeaf067 : LeafData := { rows := ![![1, 2, 5, 4, 3, 6], ![0, 5, 4, 2, 3, 6], ![0, 5, 4, 1, 3, 6], ![4, 5, 0, 1, 2, 6], ![3, 5, 0, 2, 1, 6], ![3, 4, 0, 2, 1, 6], ![0, 1, 2, 3, 4, 5]], proof := .tail 78 }

theorem namedLeaf067_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2755)) namedLeaf067 = true :=
  by decide +kernel

def namedLeaf068 : LeafData := { rows := ![![1, 2, 5, 4, 3, 6], ![0, 5, 4, 2, 3, 6], ![0, 5, 4, 1, 6, 3], ![4, 5, 0, 1, 6, 2], ![3, 5, 0, 2, 1, 6], ![3, 4, 0, 2, 1, 6], ![0, 1, 3, 2, 4, 5]], proof := .tail 168 }

theorem namedLeaf068_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2756)) namedLeaf068 = true :=
  by decide +kernel

def namedLeaf069 : LeafData := { rows := ![![1, 2, 5, 4, 3, 6], ![0, 5, 4, 2, 6, 3], ![0, 5, 4, 1, 6, 3], ![4, 5, 0, 6, 1, 2], ![3, 5, 0, 2, 1, 6], ![3, 4, 0, 2, 1, 6], ![0, 3, 1, 2, 4, 5]], proof := .tail 171 }

theorem namedLeaf069_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2757)) namedLeaf069 = true :=
  by decide +kernel

def namedLeaf070 : LeafData := { rows := ![![1, 2, 5, 4, 3, 6], ![0, 5, 4, 6, 2, 3], ![0, 5, 4, 6, 1, 3], ![4, 5, 0, 6, 1, 2], ![3, 5, 0, 2, 1, 6], ![3, 4, 0, 2, 1, 6], ![0, 3, 2, 1, 4, 5]], proof := .tail 91 }

theorem namedLeaf070_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2758)) namedLeaf070 = true :=
  by decide +kernel

def namedLeaf071 : LeafData := { rows := ![![1, 2, 5, 4, 3, 6], ![0, 5, 6, 4, 2, 3], ![0, 5, 4, 6, 1, 3], ![4, 5, 0, 6, 1, 2], ![3, 5, 0, 2, 6, 1], ![3, 4, 0, 2, 1, 6], ![0, 3, 2, 4, 1, 5]], proof := .tail 116 }

theorem namedLeaf071_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2759)) namedLeaf071 = true :=
  by decide +kernel

def namedLeaf072 : LeafData := { rows := ![![1, 2, 5, 4, 3, 6], ![0, 5, 6, 4, 2, 3], ![0, 5, 6, 4, 1, 3], ![4, 5, 0, 6, 1, 2], ![3, 5, 0, 6, 2, 1], ![3, 4, 0, 2, 1, 6], ![0, 3, 4, 2, 1, 5]], proof := .tail 31 }

theorem namedLeaf072_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2760)) namedLeaf072 = true :=
  by decide +kernel

def namedLeaf073 : LeafData := { rows := ![![1, 2, 5, 4, 3, 6], ![0, 6, 5, 4, 2, 3], ![0, 5, 4, 6, 1, 3], ![4, 5, 0, 6, 1, 2], ![3, 5, 0, 2, 6, 1], ![3, 4, 0, 2, 6, 1], ![0, 3, 2, 4, 5, 1]], proof := .tail 82 }

theorem namedLeaf073_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2761)) namedLeaf073 = true :=
  by decide +kernel

def namedLeaf074 : LeafData := { rows := ![![1, 2, 5, 4, 3, 6], ![0, 6, 5, 4, 2, 3], ![0, 5, 6, 4, 1, 3], ![4, 5, 0, 6, 1, 2], ![3, 5, 0, 6, 2, 1], ![3, 4, 0, 2, 6, 1], ![0, 3, 4, 2, 5, 1]], proof := .tail 31 }

theorem namedLeaf074_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2762)) namedLeaf074 = true :=
  by decide +kernel

def namedLeaf075 : LeafData := { rows := ![![1, 2, 5, 4, 3, 6], ![0, 6, 5, 4, 2, 3], ![0, 6, 5, 4, 1, 3], ![4, 5, 0, 6, 1, 2], ![3, 5, 0, 6, 2, 1], ![3, 4, 0, 6, 2, 1], ![0, 3, 4, 5, 2, 1]], proof := .tail 132 }

theorem namedLeaf075_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2763)) namedLeaf075 = true :=
  by decide +kernel

def namedLeaf076 : LeafData := { rows := ![![1, 2, 5, 4, 3, 6], ![0, 2, 5, 4, 3, 6], ![0, 1, 5, 4, 3, 6], ![5, 4, 0, 1, 2, 6], ![5, 3, 0, 1, 2, 6], ![4, 3, 0, 1, 2, 6], ![0, 1, 2, 3, 4, 5]], proof := .tail 7 }

theorem namedLeaf076_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2764)) namedLeaf076 = true :=
  by decide +kernel

def namedLeaf077 : LeafData := { rows := ![![1, 2, 5, 4, 3, 6], ![0, 2, 5, 4, 3, 6], ![0, 1, 5, 4, 6, 3], ![5, 4, 0, 1, 6, 2], ![5, 3, 0, 1, 2, 6], ![4, 3, 0, 1, 2, 6], ![0, 1, 3, 2, 4, 5]], proof := .tail 87 }

theorem namedLeaf077_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2765)) namedLeaf077 = true :=
  by decide +kernel

def namedLeaf078 : LeafData := { rows := ![![1, 2, 5, 4, 3, 6], ![0, 2, 5, 4, 3, 6], ![0, 1, 5, 6, 4, 3], ![5, 4, 0, 1, 6, 2], ![5, 3, 0, 1, 6, 2], ![4, 3, 0, 1, 2, 6], ![0, 1, 3, 4, 2, 5]], proof := .tail 183 }

theorem namedLeaf078_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2766)) namedLeaf078 = true :=
  by decide +kernel

def namedLeaf079 : LeafData := { rows := ![![1, 2, 5, 4, 3, 6], ![0, 2, 5, 4, 3, 6], ![0, 1, 6, 5, 4, 3], ![5, 4, 0, 1, 6, 2], ![5, 3, 0, 1, 6, 2], ![4, 3, 0, 1, 6, 2], ![0, 1, 3, 4, 5, 2]], proof := .tail 24 }

theorem namedLeaf079_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2767)) namedLeaf079 = true :=
  by decide +kernel

def namedLeaf080 : LeafData := { rows := ![![1, 2, 5, 4, 3, 6], ![0, 2, 5, 4, 6, 3], ![0, 1, 5, 4, 6, 3], ![5, 4, 0, 6, 1, 2], ![5, 3, 0, 1, 2, 6], ![4, 3, 0, 1, 2, 6], ![0, 3, 1, 2, 4, 5]], proof := .tail 94 }

theorem namedLeaf080_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2768)) namedLeaf080 = true :=
  by decide +kernel

def namedLeaf081 : LeafData := { rows := ![![1, 2, 5, 4, 3, 6], ![0, 2, 5, 4, 6, 3], ![0, 1, 5, 6, 4, 3], ![5, 4, 0, 6, 1, 2], ![5, 3, 0, 1, 6, 2], ![4, 3, 0, 1, 2, 6], ![0, 3, 1, 4, 2, 5]], proof := .tail 183 }

theorem namedLeaf081_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2769)) namedLeaf081 = true :=
  by decide +kernel

def namedLeaf082 : LeafData := { rows := ![![1, 2, 5, 4, 3, 6], ![0, 2, 5, 4, 6, 3], ![0, 1, 6, 5, 4, 3], ![5, 4, 0, 6, 1, 2], ![5, 3, 0, 1, 6, 2], ![4, 3, 0, 1, 6, 2], ![0, 3, 1, 4, 5, 2]], proof := .tail 24 }

theorem namedLeaf082_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2770)) namedLeaf082 = true :=
  by decide +kernel

def namedLeaf083 : LeafData := { rows := ![![1, 2, 5, 4, 3, 6], ![0, 2, 5, 6, 4, 3], ![0, 1, 5, 6, 4, 3], ![5, 4, 0, 6, 1, 2], ![5, 3, 0, 6, 1, 2], ![4, 3, 0, 1, 2, 6], ![0, 3, 4, 1, 2, 5]], proof := .tail 169 }

theorem namedLeaf083_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2771)) namedLeaf083 = true :=
  by decide +kernel

def namedLeaf084 : LeafData := { rows := ![![1, 2, 5, 4, 3, 6], ![0, 2, 5, 6, 4, 3], ![0, 1, 6, 5, 4, 3], ![5, 4, 0, 6, 1, 2], ![5, 3, 0, 6, 1, 2], ![4, 3, 0, 1, 6, 2], ![0, 3, 4, 1, 5, 2]], proof := .tail 24 }

theorem namedLeaf084_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2772)) namedLeaf084 = true :=
  by decide +kernel

def namedLeaf085 : LeafData := { rows := ![![1, 2, 5, 4, 3, 6], ![0, 2, 6, 5, 4, 3], ![0, 1, 6, 5, 4, 3], ![5, 4, 0, 6, 1, 2], ![5, 3, 0, 6, 1, 2], ![4, 3, 0, 6, 1, 2], ![0, 3, 4, 5, 1, 2]], proof := .tail 181 }

theorem namedLeaf085_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2773)) namedLeaf085 = true :=
  by decide +kernel

def namedLeaf086 : LeafData := { rows := ![![1, 2, 5, 4, 3, 6], ![0, 6, 2, 5, 4, 3], ![0, 6, 1, 5, 4, 3], ![5, 4, 0, 6, 1, 2], ![5, 3, 0, 6, 1, 2], ![4, 3, 0, 6, 1, 2], ![0, 3, 4, 5, 2, 1]], proof := .tail 158 }

theorem namedLeaf086_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2774)) namedLeaf086 = true :=
  by decide +kernel

def namedLeaf087 : LeafData := { rows := ![![1, 2, 5, 4, 3, 6], ![0, 5, 2, 4, 3, 6], ![0, 5, 1, 4, 3, 6], ![5, 4, 0, 1, 2, 6], ![5, 3, 0, 1, 2, 6], ![4, 3, 0, 2, 1, 6], ![0, 1, 2, 3, 4, 5]], proof := .tail 159 }

theorem namedLeaf087_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2775)) namedLeaf087 = true :=
  by decide +kernel

def namedLeaf088 : LeafData := { rows := ![![1, 2, 5, 4, 3, 6], ![0, 5, 2, 4, 3, 6], ![0, 5, 1, 4, 6, 3], ![5, 4, 0, 1, 6, 2], ![5, 3, 0, 1, 2, 6], ![4, 3, 0, 2, 1, 6], ![0, 1, 3, 2, 4, 5]], proof := .tail 87 }

theorem namedLeaf088_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2776)) namedLeaf088 = true :=
  by decide +kernel

def namedLeaf089 : LeafData := { rows := ![![1, 2, 5, 4, 3, 6], ![0, 5, 2, 4, 3, 6], ![0, 5, 1, 6, 4, 3], ![5, 4, 0, 1, 6, 2], ![5, 3, 0, 1, 6, 2], ![4, 3, 0, 2, 1, 6], ![0, 1, 3, 4, 2, 5]], proof := .tail 183 }

theorem namedLeaf089_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2777)) namedLeaf089 = true :=
  by decide +kernel

def namedLeaf090 : LeafData := { rows := ![![1, 2, 5, 4, 3, 6], ![0, 5, 2, 4, 6, 3], ![0, 5, 1, 4, 6, 3], ![5, 4, 0, 6, 1, 2], ![5, 3, 0, 1, 2, 6], ![4, 3, 0, 2, 1, 6], ![0, 3, 1, 2, 4, 5]], proof := .tail 94 }

theorem namedLeaf090_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2778)) namedLeaf090 = true :=
  by decide +kernel

def namedLeaf091 : LeafData := { rows := ![![1, 2, 5, 4, 3, 6], ![0, 5, 2, 4, 6, 3], ![0, 5, 1, 6, 4, 3], ![5, 4, 0, 6, 1, 2], ![5, 3, 0, 1, 6, 2], ![4, 3, 0, 2, 1, 6], ![0, 3, 1, 4, 2, 5]], proof := .tail 183 }

theorem namedLeaf091_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2779)) namedLeaf091 = true :=
  by decide +kernel

def namedLeaf092 : LeafData := { rows := ![![1, 2, 5, 4, 3, 6], ![0, 5, 2, 6, 4, 3], ![0, 5, 1, 6, 4, 3], ![5, 4, 0, 6, 1, 2], ![5, 3, 0, 6, 1, 2], ![4, 3, 0, 2, 1, 6], ![0, 3, 4, 1, 2, 5]], proof := .tail 169 }

theorem namedLeaf092_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2780)) namedLeaf092 = true :=
  by decide +kernel

def namedLeaf093 : LeafData := { rows := ![![1, 2, 5, 4, 3, 6], ![0, 5, 6, 2, 4, 3], ![0, 5, 6, 1, 4, 3], ![5, 4, 0, 6, 1, 2], ![5, 3, 0, 6, 1, 2], ![4, 3, 0, 2, 1, 6], ![0, 3, 4, 2, 1, 5]], proof := .tail 1 }

theorem namedLeaf093_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2781)) namedLeaf093 = true :=
  by decide +kernel

def namedLeaf094 : LeafData := { rows := ![![1, 2, 5, 4, 3, 6], ![0, 6, 5, 2, 4, 3], ![0, 5, 6, 1, 4, 3], ![5, 4, 0, 6, 1, 2], ![5, 3, 0, 6, 1, 2], ![4, 3, 0, 2, 6, 1], ![0, 3, 4, 2, 5, 1]], proof := .tail 36 }

theorem namedLeaf094_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2782)) namedLeaf094 = true :=
  by decide +kernel

def namedLeaf095 : LeafData := { rows := ![![1, 2, 5, 4, 3, 6], ![0, 6, 5, 2, 4, 3], ![0, 6, 5, 1, 4, 3], ![5, 4, 0, 6, 1, 2], ![5, 3, 0, 6, 1, 2], ![4, 3, 0, 6, 2, 1], ![0, 3, 4, 5, 2, 1]], proof := .tail 120 }

theorem namedLeaf095_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2783)) namedLeaf095 = true :=
  by decide +kernel

def namedLeaf096 : LeafData := { rows := ![![1, 2, 5, 4, 3, 6], ![0, 5, 4, 2, 3, 6], ![0, 5, 4, 1, 3, 6], ![5, 4, 0, 1, 2, 6], ![5, 3, 0, 2, 1, 6], ![4, 3, 0, 2, 1, 6], ![0, 1, 2, 3, 4, 5]], proof := .tail 81 }

theorem namedLeaf096_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2784)) namedLeaf096 = true :=
  by decide +kernel

def namedLeaf097 : LeafData := { rows := ![![1, 2, 5, 4, 3, 6], ![0, 5, 4, 2, 3, 6], ![0, 5, 4, 1, 6, 3], ![5, 4, 0, 1, 6, 2], ![5, 3, 0, 2, 1, 6], ![4, 3, 0, 2, 1, 6], ![0, 1, 3, 2, 4, 5]], proof := .tail 53 }

theorem namedLeaf097_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2785)) namedLeaf097 = true :=
  by decide +kernel

def namedLeaf098 : LeafData := { rows := ![![1, 2, 5, 4, 3, 6], ![0, 5, 4, 2, 6, 3], ![0, 5, 4, 1, 6, 3], ![5, 4, 0, 6, 1, 2], ![5, 3, 0, 2, 1, 6], ![4, 3, 0, 2, 1, 6], ![0, 3, 1, 2, 4, 5]], proof := .tail 94 }

theorem namedLeaf098_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2786)) namedLeaf098 = true :=
  by decide +kernel

def namedLeaf099 : LeafData := { rows := ![![1, 2, 5, 4, 3, 6], ![0, 5, 4, 6, 2, 3], ![0, 5, 4, 6, 1, 3], ![5, 4, 0, 6, 1, 2], ![5, 3, 0, 2, 1, 6], ![4, 3, 0, 2, 1, 6], ![0, 3, 2, 1, 4, 5]], proof := .tail 124 }

theorem namedLeaf099_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2787)) namedLeaf099 = true :=
  by decide +kernel

def namedLeaf100 : LeafData := { rows := ![![1, 2, 5, 4, 3, 6], ![0, 5, 6, 4, 2, 3], ![0, 5, 4, 6, 1, 3], ![5, 4, 0, 6, 1, 2], ![5, 3, 0, 2, 6, 1], ![4, 3, 0, 2, 1, 6], ![0, 3, 2, 4, 1, 5]], proof := .tail 38 }

theorem namedLeaf100_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2788)) namedLeaf100 = true :=
  by decide +kernel

def namedLeaf101 : LeafData := { rows := ![![1, 2, 5, 4, 3, 6], ![0, 5, 6, 4, 2, 3], ![0, 5, 6, 4, 1, 3], ![5, 4, 0, 6, 1, 2], ![5, 3, 0, 6, 2, 1], ![4, 3, 0, 2, 1, 6], ![0, 3, 4, 2, 1, 5]], proof := .tail 138 }

theorem namedLeaf101_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2789)) namedLeaf101 = true :=
  by decide +kernel

def namedLeaf102 : LeafData := { rows := ![![1, 2, 5, 4, 3, 6], ![0, 6, 5, 4, 2, 3], ![0, 5, 4, 6, 1, 3], ![5, 4, 0, 6, 1, 2], ![5, 3, 0, 2, 6, 1], ![4, 3, 0, 2, 6, 1], ![0, 3, 2, 4, 5, 1]], proof := .tail 71 }

theorem namedLeaf102_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2790)) namedLeaf102 = true :=
  by decide +kernel

def namedLeaf103 : LeafData := { rows := ![![1, 2, 5, 4, 3, 6], ![0, 6, 5, 4, 2, 3], ![0, 5, 6, 4, 1, 3], ![5, 4, 0, 6, 1, 2], ![5, 3, 0, 6, 2, 1], ![4, 3, 0, 2, 6, 1], ![0, 3, 4, 2, 5, 1]], proof := .tail 138 }

theorem namedLeaf103_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2791)) namedLeaf103 = true :=
  by decide +kernel

def namedLeaf104 : LeafData := { rows := ![![1, 2, 5, 4, 3, 6], ![0, 6, 5, 4, 2, 3], ![0, 6, 5, 4, 1, 3], ![5, 4, 0, 6, 1, 2], ![5, 3, 0, 6, 2, 1], ![4, 3, 0, 6, 2, 1], ![0, 3, 4, 5, 2, 1]], proof := .tail 39 }

theorem namedLeaf104_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2792)) namedLeaf104 = true :=
  by decide +kernel

def namedLeaf105 : LeafData := { rows := ![![1, 2, 4, 5, 6, 3], ![0, 2, 4, 5, 6, 3], ![0, 1, 4, 5, 6, 3], ![4, 5, 6, 0, 1, 2], ![3, 0, 1, 2, 5, 6], ![3, 0, 1, 2, 4, 6], ![3, 0, 1, 2, 4, 5]], proof := .tail 60 }

theorem namedLeaf105_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2793)) namedLeaf105 = true :=
  by decide +kernel

def namedLeaf106 : LeafData := { rows := ![![1, 2, 4, 5, 6, 3], ![0, 2, 4, 5, 6, 3], ![0, 1, 4, 5, 6, 3], ![4, 5, 6, 0, 1, 2], ![3, 0, 1, 2, 6, 5], ![3, 0, 1, 2, 6, 4], ![3, 0, 1, 2, 5, 4]], proof := .tail 201 }

theorem namedLeaf106_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2794)) namedLeaf106 = true :=
  by decide +kernel

def namedLeaf107 : LeafData := { rows := ![![1, 2, 4, 5, 6, 3], ![0, 2, 4, 5, 6, 3], ![0, 1, 4, 6, 5, 3], ![4, 5, 6, 0, 1, 2], ![3, 0, 1, 2, 6, 5], ![3, 0, 1, 6, 2, 4], ![3, 0, 1, 5, 2, 4]], proof := .low (![123, 117, 66, 30, 33, 150, 147, 9, 154, 70, 157, 112, 6, 3, 20, 196, 203, 170, 131, 202, 133, 37, 205, 72, 15, 80, 97, 165]) }

theorem namedLeaf107_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2795)) namedLeaf107 = true :=
  by decide +kernel

def namedLeaf108 : LeafData := { rows := ![![1, 2, 4, 5, 6, 3], ![0, 2, 4, 5, 6, 3], ![0, 1, 6, 4, 5, 3], ![4, 5, 6, 0, 1, 2], ![3, 0, 1, 6, 2, 5], ![3, 0, 1, 6, 2, 4], ![3, 0, 1, 5, 4, 2]], proof := .tail 44 }

theorem namedLeaf108_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2796)) namedLeaf108 = true :=
  by decide +kernel

def namedLeaf109 : LeafData := { rows := ![![1, 2, 4, 5, 6, 3], ![0, 2, 4, 5, 6, 3], ![0, 1, 5, 4, 6, 3], ![4, 5, 6, 0, 1, 2], ![3, 0, 1, 5, 2, 6], ![3, 0, 1, 4, 2, 6], ![3, 0, 1, 2, 4, 5]], proof := .tail 14 }

theorem namedLeaf109_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2797)) namedLeaf109 = true :=
  by decide +kernel

def namedLeaf110 : LeafData := { rows := ![![1, 2, 4, 5, 6, 3], ![0, 2, 4, 5, 6, 3], ![0, 1, 5, 6, 4, 3], ![4, 5, 6, 0, 1, 2], ![3, 0, 1, 5, 6, 2], ![3, 0, 1, 4, 2, 6], ![3, 0, 1, 4, 2, 5]], proof := .low (![52, 55, 110, 12, 73, 150, 147, 134, 144, 153, 175, 189, 6, 56, 13, 179, 203, 79, 130, 21, 2, 2, 195, 72, 75, 80, 97, 165]) }

theorem namedLeaf110_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2798)) namedLeaf110 = true :=
  by decide +kernel

def namedLeaf111 : LeafData := { rows := ![![1, 2, 4, 5, 6, 3], ![0, 2, 4, 5, 6, 3], ![0, 1, 6, 5, 4, 3], ![4, 5, 6, 0, 1, 2], ![3, 0, 1, 5, 6, 2], ![3, 0, 1, 4, 6, 2], ![3, 0, 1, 4, 5, 2]], proof := .tail 22 }

theorem namedLeaf111_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2799)) namedLeaf111 = true :=
  by decide +kernel

def namedLeaf112 : LeafData := { rows := ![![1, 2, 4, 5, 6, 3], ![0, 2, 4, 5, 6, 3], ![0, 1, 6, 5, 4, 3], ![4, 5, 6, 0, 1, 2], ![3, 0, 1, 6, 5, 2], ![3, 0, 1, 6, 4, 2], ![3, 0, 1, 5, 4, 2]], proof := .tail 180 }

theorem namedLeaf112_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2800)) namedLeaf112 = true :=
  by decide +kernel

def namedLeaf113 : LeafData := { rows := ![![1, 2, 4, 5, 6, 3], ![0, 2, 4, 6, 5, 3], ![0, 1, 4, 6, 5, 3], ![4, 5, 6, 0, 1, 2], ![3, 0, 1, 2, 6, 5], ![3, 0, 6, 1, 2, 4], ![3, 0, 5, 1, 2, 4]], proof := .low (![127, 117, 66, 197, 137, 18, 176, 57, 23, 126, 86, 186, 6, 109, 118, 187, 186, 170, 54, 125, 186, 100, 42, 186, 190, 48, 101, 89]) }

theorem namedLeaf113_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2801)) namedLeaf113 = true :=
  by decide +kernel

def namedLeaf114 : LeafData := { rows := ![![1, 2, 4, 5, 6, 3], ![0, 2, 4, 6, 5, 3], ![0, 1, 6, 4, 5, 3], ![4, 5, 6, 0, 1, 2], ![3, 0, 1, 6, 2, 5], ![3, 0, 6, 1, 2, 4], ![3, 0, 5, 1, 4, 2]], proof := .tail 185 }

theorem namedLeaf114_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2802)) namedLeaf114 = true :=
  by decide +kernel

def namedLeaf115 : LeafData := { rows := ![![1, 2, 4, 5, 6, 3], ![0, 2, 4, 6, 5, 3], ![0, 1, 6, 5, 4, 3], ![4, 5, 6, 0, 1, 2], ![3, 0, 1, 6, 5, 2], ![3, 0, 6, 1, 4, 2], ![3, 0, 5, 1, 4, 2]], proof := .tail 17 }

theorem namedLeaf115_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2803)) namedLeaf115 = true :=
  by decide +kernel

def namedLeaf116 : LeafData := { rows := ![![1, 2, 4, 5, 6, 3], ![0, 2, 6, 4, 5, 3], ![0, 1, 6, 4, 5, 3], ![4, 5, 6, 0, 1, 2], ![3, 0, 6, 1, 2, 5], ![3, 0, 6, 1, 2, 4], ![3, 0, 5, 4, 1, 2]], proof := .tail 204 }

theorem namedLeaf116_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2804)) namedLeaf116 = true :=
  by decide +kernel

def namedLeaf117 : LeafData := { rows := ![![1, 2, 4, 5, 6, 3], ![0, 2, 6, 4, 5, 3], ![0, 1, 6, 5, 4, 3], ![4, 5, 6, 0, 1, 2], ![3, 0, 6, 1, 5, 2], ![3, 0, 6, 1, 4, 2], ![3, 0, 5, 4, 1, 2]], proof := .tail 194 }

theorem namedLeaf117_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2805)) namedLeaf117 = true :=
  by decide +kernel

def namedLeaf118 : LeafData := { rows := ![![1, 2, 4, 5, 6, 3], ![0, 2, 5, 4, 6, 3], ![0, 1, 5, 4, 6, 3], ![4, 5, 6, 0, 1, 2], ![3, 0, 5, 1, 2, 6], ![3, 0, 4, 1, 2, 6], ![3, 0, 1, 2, 4, 5]], proof := .low (![16, 85, 83, 98, 121, 111, 149, 46, 161, 35, 115, 76, 29, 155, 163, 115, 173, 19, 122, 115, 67, 146, 84, 104, 151, 27, 34, 174]) }

theorem namedLeaf118_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2806)) namedLeaf118 = true :=
  by decide +kernel

def namedLeaf119 : LeafData := { rows := ![![1, 2, 4, 5, 6, 3], ![0, 2, 5, 4, 6, 3], ![0, 1, 5, 6, 4, 3], ![4, 5, 6, 0, 1, 2], ![3, 0, 5, 1, 6, 2], ![3, 0, 4, 1, 2, 6], ![3, 0, 1, 4, 2, 5]], proof := .tail 136 }

theorem namedLeaf119_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2807)) namedLeaf119 = true :=
  by decide +kernel

def namedLeaf120 : LeafData := { rows := ![![1, 2, 4, 5, 6, 3], ![0, 2, 5, 4, 6, 3], ![0, 1, 6, 5, 4, 3], ![4, 5, 6, 0, 1, 2], ![3, 0, 5, 1, 6, 2], ![3, 0, 4, 1, 6, 2], ![3, 0, 1, 4, 5, 2]], proof := .tail 49 }

theorem namedLeaf120_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2808)) namedLeaf120 = true :=
  by decide +kernel

def namedLeaf121 : LeafData := { rows := ![![1, 2, 4, 5, 6, 3], ![0, 2, 5, 6, 4, 3], ![0, 1, 5, 6, 4, 3], ![4, 5, 6, 0, 1, 2], ![3, 0, 5, 6, 1, 2], ![3, 0, 4, 1, 2, 6], ![3, 0, 4, 1, 2, 5]], proof := .low (![119, 68, 83, 160, 90, 69, 92, 145, 161, 178, 40, 142, 193, 63, 113, 103, 142, 107, 102, 166, 142, 141, 139, 26, 74, 192, 88, 162]) }

theorem namedLeaf121_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2809)) namedLeaf121 = true :=
  by decide +kernel

def namedLeaf122 : LeafData := { rows := ![![1, 2, 4, 5, 6, 3], ![0, 2, 5, 6, 4, 3], ![0, 1, 6, 5, 4, 3], ![4, 5, 6, 0, 1, 2], ![3, 0, 5, 6, 1, 2], ![3, 0, 4, 1, 6, 2], ![3, 0, 4, 1, 5, 2]], proof := .tail 105 }

theorem namedLeaf122_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2810)) namedLeaf122 = true :=
  by decide +kernel

def namedLeaf123 : LeafData := { rows := ![![1, 2, 4, 5, 6, 3], ![0, 2, 6, 5, 4, 3], ![0, 1, 6, 5, 4, 3], ![4, 5, 6, 0, 1, 2], ![3, 0, 5, 6, 1, 2], ![3, 0, 4, 6, 1, 2], ![3, 0, 4, 5, 1, 2]], proof := .tail 164 }

theorem namedLeaf123_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2811)) namedLeaf123 = true :=
  by decide +kernel

def namedLeaf124 : LeafData := { rows := ![![1, 2, 4, 5, 6, 3], ![0, 2, 6, 5, 4, 3], ![0, 1, 6, 5, 4, 3], ![4, 5, 6, 0, 1, 2], ![3, 0, 6, 5, 1, 2], ![3, 0, 6, 4, 1, 2], ![3, 0, 5, 4, 1, 2]], proof := .tail 8 }

theorem namedLeaf124_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2812)) namedLeaf124 = true :=
  by decide +kernel

def namedLeaf125 : LeafData := { rows := ![![1, 2, 4, 5, 6, 3], ![0, 6, 2, 4, 5, 3], ![0, 6, 1, 4, 5, 3], ![4, 5, 6, 0, 1, 2], ![3, 0, 6, 1, 2, 5], ![3, 0, 6, 1, 2, 4], ![3, 0, 5, 4, 2, 1]], proof := .tail 148 }

theorem namedLeaf125_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2813)) namedLeaf125 = true :=
  by decide +kernel

def namedLeaf126 : LeafData := { rows := ![![1, 2, 4, 5, 6, 3], ![0, 6, 2, 4, 5, 3], ![0, 6, 1, 5, 4, 3], ![4, 5, 6, 0, 1, 2], ![3, 0, 6, 1, 5, 2], ![3, 0, 6, 1, 4, 2], ![3, 0, 5, 4, 2, 1]], proof := .tail 194 }

theorem namedLeaf126_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2814)) namedLeaf126 = true :=
  by decide +kernel

def namedLeaf127 : LeafData := { rows := ![![1, 2, 4, 5, 6, 3], ![0, 6, 2, 5, 4, 3], ![0, 6, 1, 5, 4, 3], ![4, 5, 6, 0, 1, 2], ![3, 0, 5, 6, 1, 2], ![3, 0, 4, 6, 1, 2], ![3, 0, 4, 5, 2, 1]], proof := .tail 65 }

theorem namedLeaf127_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2815)) namedLeaf127 = true :=
  by decide +kernel

def fallback : LeafData := { rows := fun _ _ => 0, proof := .tail 0 }
def lookup (offset : ℕ) : LeafData :=
  if offset < 128 then (if offset < 64 then (if offset < 32 then (if offset < 16 then (if offset < 8 then (if offset < 4 then (if offset < 2 then (if offset < 1 then (namedLeaf000) else (namedLeaf001)) else (if offset < 3 then (namedLeaf002) else (namedLeaf003))) else (if offset < 6 then (if offset < 5 then (namedLeaf004) else (namedLeaf005)) else (if offset < 7 then (namedLeaf006) else (namedLeaf007)))) else (if offset < 12 then (if offset < 10 then (if offset < 9 then (namedLeaf008) else (namedLeaf009)) else (if offset < 11 then (namedLeaf010) else (namedLeaf011))) else (if offset < 14 then (if offset < 13 then (namedLeaf012) else (namedLeaf013)) else (if offset < 15 then (namedLeaf014) else (namedLeaf015))))) else (if offset < 24 then (if offset < 20 then (if offset < 18 then (if offset < 17 then (namedLeaf016) else (namedLeaf017)) else (if offset < 19 then (namedLeaf018) else (namedLeaf019))) else (if offset < 22 then (if offset < 21 then (namedLeaf020) else (namedLeaf021)) else (if offset < 23 then (namedLeaf022) else (namedLeaf023)))) else (if offset < 28 then (if offset < 26 then (if offset < 25 then (namedLeaf024) else (namedLeaf025)) else (if offset < 27 then (namedLeaf026) else (namedLeaf027))) else (if offset < 30 then (if offset < 29 then (namedLeaf028) else (namedLeaf029)) else (if offset < 31 then (namedLeaf030) else (namedLeaf031)))))) else (if offset < 48 then (if offset < 40 then (if offset < 36 then (if offset < 34 then (if offset < 33 then (namedLeaf032) else (namedLeaf033)) else (if offset < 35 then (namedLeaf034) else (namedLeaf035))) else (if offset < 38 then (if offset < 37 then (namedLeaf036) else (namedLeaf037)) else (if offset < 39 then (namedLeaf038) else (namedLeaf039)))) else (if offset < 44 then (if offset < 42 then (if offset < 41 then (namedLeaf040) else (namedLeaf041)) else (if offset < 43 then (namedLeaf042) else (namedLeaf043))) else (if offset < 46 then (if offset < 45 then (namedLeaf044) else (namedLeaf045)) else (if offset < 47 then (namedLeaf046) else (namedLeaf047))))) else (if offset < 56 then (if offset < 52 then (if offset < 50 then (if offset < 49 then (namedLeaf048) else (namedLeaf049)) else (if offset < 51 then (namedLeaf050) else (namedLeaf051))) else (if offset < 54 then (if offset < 53 then (namedLeaf052) else (namedLeaf053)) else (if offset < 55 then (namedLeaf054) else (namedLeaf055)))) else (if offset < 60 then (if offset < 58 then (if offset < 57 then (namedLeaf056) else (namedLeaf057)) else (if offset < 59 then (namedLeaf058) else (namedLeaf059))) else (if offset < 62 then (if offset < 61 then (namedLeaf060) else (namedLeaf061)) else (if offset < 63 then (namedLeaf062) else (namedLeaf063))))))) else (if offset < 96 then (if offset < 80 then (if offset < 72 then (if offset < 68 then (if offset < 66 then (if offset < 65 then (namedLeaf064) else (namedLeaf065)) else (if offset < 67 then (namedLeaf066) else (namedLeaf067))) else (if offset < 70 then (if offset < 69 then (namedLeaf068) else (namedLeaf069)) else (if offset < 71 then (namedLeaf070) else (namedLeaf071)))) else (if offset < 76 then (if offset < 74 then (if offset < 73 then (namedLeaf072) else (namedLeaf073)) else (if offset < 75 then (namedLeaf074) else (namedLeaf075))) else (if offset < 78 then (if offset < 77 then (namedLeaf076) else (namedLeaf077)) else (if offset < 79 then (namedLeaf078) else (namedLeaf079))))) else (if offset < 88 then (if offset < 84 then (if offset < 82 then (if offset < 81 then (namedLeaf080) else (namedLeaf081)) else (if offset < 83 then (namedLeaf082) else (namedLeaf083))) else (if offset < 86 then (if offset < 85 then (namedLeaf084) else (namedLeaf085)) else (if offset < 87 then (namedLeaf086) else (namedLeaf087)))) else (if offset < 92 then (if offset < 90 then (if offset < 89 then (namedLeaf088) else (namedLeaf089)) else (if offset < 91 then (namedLeaf090) else (namedLeaf091))) else (if offset < 94 then (if offset < 93 then (namedLeaf092) else (namedLeaf093)) else (if offset < 95 then (namedLeaf094) else (namedLeaf095)))))) else (if offset < 112 then (if offset < 104 then (if offset < 100 then (if offset < 98 then (if offset < 97 then (namedLeaf096) else (namedLeaf097)) else (if offset < 99 then (namedLeaf098) else (namedLeaf099))) else (if offset < 102 then (if offset < 101 then (namedLeaf100) else (namedLeaf101)) else (if offset < 103 then (namedLeaf102) else (namedLeaf103)))) else (if offset < 108 then (if offset < 106 then (if offset < 105 then (namedLeaf104) else (namedLeaf105)) else (if offset < 107 then (namedLeaf106) else (namedLeaf107))) else (if offset < 110 then (if offset < 109 then (namedLeaf108) else (namedLeaf109)) else (if offset < 111 then (namedLeaf110) else (namedLeaf111))))) else (if offset < 120 then (if offset < 116 then (if offset < 114 then (if offset < 113 then (namedLeaf112) else (namedLeaf113)) else (if offset < 115 then (namedLeaf114) else (namedLeaf115))) else (if offset < 118 then (if offset < 117 then (namedLeaf116) else (namedLeaf117)) else (if offset < 119 then (namedLeaf118) else (namedLeaf119)))) else (if offset < 124 then (if offset < 122 then (if offset < 121 then (namedLeaf120) else (namedLeaf121)) else (if offset < 123 then (namedLeaf122) else (namedLeaf123))) else (if offset < 126 then (if offset < 125 then (namedLeaf124) else (namedLeaf125)) else (if offset < 127 then (namedLeaf126) else (namedLeaf127)))))))) else fallback

theorem point_checked (j : Fin 128) :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 (2688 + j.val))) (lookup j.val) = true := by
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

theorem correct (id : Fin 24698) (hlow : 2688 ≤ id.val) (hhigh : id.val < 2816) :
    leafCheck library (N4R2WordTree.catalog id) (lookup (id.val - 2688)) = true := by
  let j : Fin 128 := ⟨id.val - 2688, by omega⟩
  have hsum : 2688 + j.val = id.val := by dsimp [j]; omega
  have hindex : Fin.ofNat 24698 (2688 + j.val) = id := by
    apply Fin.ext
    simp only [Fin.ofNat, hsum, Nat.mod_eq_of_lt id.isLt]
  have hh := point_checked j
  rw [hindex] at hh
  exact hh

#print axioms point_checked
#print axioms correct
end Jsp404.N4R2OuterLeftData.LeafShard021
