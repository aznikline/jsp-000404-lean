import Jsp000404.N4R2OuterLeftReplay
import Jsp000404.N4R2WordCatalog

set_option autoImplicit false
set_option pp.fullNames true
set_option maxRecDepth 8192
set_option maxHeartbeats 0
set_option Elab.async false

namespace Jsp404.N4R2OuterLeftData.LeafShard010
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

-- Cycle fingerprint 0186cde1ba2091ea5ad41ac7327a986fec34dcc878691752cfda83994a7bbabf.
def localCycle00001 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 1 2, .distance 2 6, .distance 5 6, .distance 4 6, .distance 0 4, .distance 4 5, .theta 4]
    constant := ![3, 0, -1, -1, 0, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, true, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 16 0, .triangle 18 0, .triangle 30 1, .triangle 34 2, .triangle 13 0, .triangle 12 0, .corridorLower 4 5]

-- Cycle fingerprint 01cea0dc875d7d7dd92635fcd2d925b33d2b61ed34c5115a0899a940b6fed7d3.
def localCycle00002 : Cycle where
  length := 10
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 3, .distance 3 4, .distance 3 5, .distance 5 6, .distance 4 6, .distance 0 4, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, 0, -1, 0, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, true, false, false, false, true] }
  origin := ![.corridorUpper 2 3, .triangle 15 2, .triangle 19 0, .triangle 31 2, .triangle 33 0, .triangle 34 2, .triangle 13 0, .triangle 12 0, .corridorLower 4 5, .thetaNext 3]

-- Cycle fingerprint 02ad48b0b0c5f9f9b9c24506b0139233bd57f33d9edd49a1ae9e401357548783.
def localCycle00003 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 5, .distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 3 6, .distance 3 4, .distance 1 4, .distance 1 5]
    constant := ![-1, -1, 0, 0, 3, -1, 0, 0, -2]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, true, false] }
  origin := ![.triangle 3 0, .corridorLower 0 1, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 27 0, .triangle 32 1, .triangle 19 2, .gapLower 1 4]

-- Cycle fingerprint 02cb8fe6948b9495c90f9956277e71b83a87c010a44258b82eecdd6ce638cc54.
def localCycle00004 : Cycle where
  length := 8
  data := {
    node := ![.distance 4 5, .theta 4, .theta 3, .distance 2 3, .distance 1 3, .distance 1 6, .distance 1 4, .distance 0 4, .distance 4 5]
    constant := ![-1, 0, 3, 0, -2, -2, 0, -1]
    coefficient := ![0, 0, 1, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, true, false] }
  origin := ![.corridorLower 4 5, .thetaNext 3, .corridorUpper 2 3, .triangle 15 2, .gapLower 1 5, .gapLower 1 4, .triangle 2 2, .triangle 12 0]

-- Cycle fingerprint 02f2c6d93501835e1b91e9abeee6a9bb2a265455a81feb143d3cebf6da62593a.
def localCycle00005 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 4 6, .distance 3 6, .distance 2 6, .distance 1 6, .distance 1 3, .distance 3 4, .distance 4 5, .theta 4]
    constant := ![4, 0, 0, 0, -3, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, false] }
  origin := ![.gapLower 4 6, .gapLower 6 4, .triangle 27 2, .triangle 18 2, .gapLower 1 5, .triangle 19 0, .triangle 31 0, .corridorLower 4 5]

-- Cycle fingerprint 0711e128e426893115e7ba88dd472024711f6569bfa17cf59f02da2bab5aa25f.
def localCycle00006 : Cycle where
  length := 11
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 2 4, .distance 2 5, .distance 5 6, .distance 3 5, .distance 1 3, .distance 1 2, .distance 0 1]
    constant := ![-1, 0, 0, 3, 0, 0, -1, -1, -1, 0, -1]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, false, false, false, false, false] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 25 2, .triangle 28 2, .triangle 30 0, .triangle 33 0, .triangle 20 0, .gapLower 1 2, .triangle 0 0]

-- Cycle fingerprint 0960a777e6a0f8ed64280dc50e8ce9a35186a3997b732c0fb82adab7b1b14aaf.
def localCycle00007 : Cycle where
  length := 5
  data := {
    node := ![.distance 1 2, .distance 2 5, .distance 3 5, .distance 1 5, .distance 1 3, .distance 1 2]
    constant := ![2, 0, 0, -3, 0]
    coefficient := ![0, 0, 0, 0, 0]
    strict := ![true, false, false, false, true] }
  origin := ![.gapUpper 2 2, .gapLower 5 4, .gapLower 5 3, .gapLower 1 3, .triangle 15 1]

-- Cycle fingerprint 09dfa431ee781f51624bfc8227f5a650a6db90644b248ac862210637f084d462.
def localCycle00008 : Cycle where
  length := 4
  data := {
    node := ![.distance 1 5, .distance 1 3, .distance 1 2, .distance 2 5, .distance 1 5]
    constant := ![-2, -2, 2, 0]
    coefficient := ![0, 0, 0, 0]
    strict := ![false, false, true, true] }
  origin := ![.gapLower 1 3, .gapLower 1 2, .gapUpper 2 2, .triangle 17 2]

-- Cycle fingerprint 10f20961839520b140c365a972636f9a38530c68476ad59b858a53c16e3b483e.
def localCycle00009 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 2 4, .distance 1 2, .distance 2 3, .distance 3 6, .distance 0 3, .theta 0, .zero]
    constant := ![0, 3, 0, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 16 0, .triangle 15 0, .triangle 27 0, .triangle 11 0, .corridorLower 0 3, .thetaLower 0]

-- Cycle fingerprint 12d4e056473b37f3bf0a10ec2fba7fdb71379d667303e3429a79afbbe461499a.
def localCycle00010 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 3 4, .distance 1 3, .distance 3 5, .distance 4 5, .distance 0 4, .distance 4 6, .theta 4]
    constant := ![3, -1, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 19 0, .triangle 20 0, .triangle 31 1, .triangle 12 0, .triangle 13 0, .corridorLower 4 6]

-- Cycle fingerprint 13e46ed3e757c5b38599cfa0f0d52628f9d2198742958780285756d6ed3221f0.
def localCycle00011 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 3, .distance 1 2, .distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 3 6, .distance 3 4, .distance 1 3]
    constant := ![0, -3, -1, 0, 0, 3, -1, 0, -1]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, true, false] }
  origin := ![.gapLower 1 2, .gapLower 1 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 27 0, .triangle 32 1, .triangle 19 0]

-- Cycle fingerprint 166db7943b94fe23bff4b8acea1f0de214065f278da2beb9f789aeb724cad938.
def localCycle00012 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 2 4, .distance 1 2, .distance 2 5, .distance 2 3, .distance 0 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, -1, -1, -1, 0, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, true, false, true, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 29 0, .triangle 16 0, .triangle 17 0, .triangle 26 1, .triangle 5 0, .triangle 0 1, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint 172c4f7481207d7c9e0f6c940f81fa100f4e5c7d7f252e456c906bc2dd5247b1.
def localCycle00013 : Cycle where
  length := 9
  data := {
    node := ![.distance 2 3, .distance 1 3, .distance 1 6, .distance 1 4, .distance 1 5, .distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3]
    constant := ![0, -2, 0, -2, -1, -1, 0, 0, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1, 1]
    strict := ![true, false, true, false, false, false, false, false, false] }
  origin := ![.triangle 15 2, .gapLower 1 5, .triangle 23 1, .gapLower 1 3, .triangle 3 0, .corridorLower 0 1, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3]

-- Cycle fingerprint 17e9dd780a027022edc8d5dc5e3eac9e6eab38c4dd65e71fa55eb2c6f4b9340e.
def localCycle00014 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 1 2, .distance 2 3, .distance 3 5, .distance 4 5, .distance 0 4, .distance 4 6, .theta 4]
    constant := ![3, 0, -1, -1, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, true, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 16 0, .triangle 15 0, .triangle 26 0, .triangle 31 1, .triangle 12 0, .triangle 13 0, .corridorLower 4 6]

-- Cycle fingerprint 184a43766e02c7ee52e169aca8221669cf9cea72b6c69733ceac80673f78cfd4.
def localCycle00015 : Cycle where
  length := 10
  data := {
    node := ![.distance 3 6, .distance 1 3, .distance 1 4, .distance 0 4, .distance 4 5, .theta 4, .zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6]
    constant := ![-1, -2, 0, -1, -1, 0, 0, 3, 0, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![false, false, true, false, false, false, false, false, true, true] }
  origin := ![.triangle 21 0, .gapLower 1 4, .triangle 2 2, .triangle 12 0, .corridorLower 4 5, .thetaLower 4, .thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2]

-- Cycle fingerprint 198fedc519c1a39e4dd39461d8f78926ec1fcbe20dde7edc74dc5d982d8d2f22.
def localCycle00016 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 4 6, .distance 1 4, .distance 0 4, .distance 4 5, .theta 4]
    constant := ![3, 0, -1, -1, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 29 0, .triangle 23 0, .triangle 2 2, .triangle 12 0, .corridorLower 4 5]

-- Cycle fingerprint 1d2938958239ccdc44a2b9513f673f5f08934b578c4af0f138bf2ec252b17a83.
def localCycle00017 : Cycle where
  length := 8
  data := {
    node := ![.distance 1 2, .distance 0 1, .theta 0, .zero, .theta 6, .distance 5 6, .distance 4 6, .distance 2 4, .distance 1 2]
    constant := ![-2, -1, 0, 0, 3, 0, -1, -1]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, false] }
  origin := ![.gapLower 1 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 29 0, .triangle 16 0]

-- Cycle fingerprint 1dbeedf275e1ae1119d8159edc8ab4b951843d76ed7fc9df62cd0ed0e69ede65.
def localCycle00018 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 5, .distance 1 2, .distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 1 3, .distance 1 6, .distance 1 4, .distance 1 5]
    constant := ![0, -1, -1, 0, 0, 3, 0, 0, -2, -2]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![true, false, false, false, false, false, true, true, false, false] }
  origin := ![.triangle 17 1, .triangle 0 0, .corridorLower 0 1, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 15 2, .triangle 21 2, .gapLower 1 4, .gapLower 1 3]

-- Cycle fingerprint 1dbfe66f9a8a5314850ed079a6948b4d0d3b91d638ef0d6a7bef8a0344304ba0.
def localCycle00019 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 4, .distance 1 3, .distance 3 5, .distance 5 6, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, -1, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, true] }
  origin := ![.corridorUpper 2 3, .triangle 25 0, .triangle 19 0, .triangle 20 0, .triangle 33 0, .triangle 34 0, .corridorLower 4 5, .thetaNext 3]

-- Cycle fingerprint 1de52e7982a6b76571e664ad5c40c8e9c3aadd3ce4175b0239449de135979460.
def localCycle00020 : Cycle where
  length := 9
  data := {
    node := ![.distance 3 6, .distance 1 6, .distance 1 4, .distance 1 5, .distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 3 6]
    constant := ![0, -2, -2, -1, -1, 0, 0, 3, -1]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![false, false, false, false, false, false, false, false, false] }
  origin := ![.gapLower 6 2, .gapLower 1 5, .gapLower 1 4, .triangle 3 0, .corridorLower 0 1, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 27 0]

-- Cycle fingerprint 1e17f00cccdb6e0662f49cf0f11613a445dcf05035a2ee866ec12b41d13589ff.
def localCycle00021 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 3 4, .distance 1 3, .distance 3 6, .distance 4 6, .distance 0 4, .distance 4 5, .theta 4]
    constant := ![3, -1, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 19 0, .triangle 21 0, .triangle 32 1, .triangle 13 0, .triangle 12 0, .corridorLower 4 5]

-- Cycle fingerprint 1f0f11a7570d8978f257ec6bdcef3dd26c79285a8ad33aa4d8b858bf0c547e40.
def localCycle00022 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 1 4, .distance 1 5, .distance 5 6, .distance 4 6, .distance 0 4, .distance 4 5, .theta 4]
    constant := ![3, 0, 0, 0, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, true, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 16 2, .triangle 22 2, .triangle 24 0, .triangle 34 2, .triangle 13 0, .triangle 12 0, .corridorLower 4 5]

-- Cycle fingerprint 212707d1c4897ac7eb4fb713c4a1625a763075dae5002419feb11f9d46539bdb.
def localCycle00023 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 3, .distance 2 5, .distance 5 6, .distance 3 6, .distance 1 3, .distance 3 5, .distance 4 5, .theta 4]
    constant := ![3, -1, 0, -1, 0, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 0, .triangle 26 2, .triangle 30 0, .triangle 33 2, .triangle 21 0, .triangle 20 0, .triangle 31 1, .corridorLower 4 5]

-- Cycle fingerprint 2130f8febb69c431552037f800103aecfc88993348c97dd2e26a9e8e6da7cb26.
def localCycle00024 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 4, .distance 3 5, .distance 5 6, .distance 4 6, .distance 0 4, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, -1, 0, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false, false, true] }
  origin := ![.corridorUpper 2 3, .triangle 25 0, .triangle 31 2, .triangle 33 0, .triangle 34 2, .triangle 13 0, .triangle 12 0, .corridorLower 4 5, .thetaNext 3]

-- Cycle fingerprint 229210a148f78e976ebeb8e84af4505e350ec8c3fbe187c260838e25e7dc9c01.
def localCycle00025 : Cycle where
  length := 11
  data := {
    node := ![.distance 2 3, .distance 2 5, .distance 5 6, .distance 3 5, .distance 1 3, .distance 1 2, .distance 0 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 2 3]
    constant := ![0, -1, -1, -1, 0, -1, -1, 0, 0, 3, -1]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![true, false, false, false, false, false, false, false, false, false, false] }
  origin := ![.triangle 26 2, .triangle 30 0, .triangle 33 0, .triangle 20 0, .gapLower 1 2, .triangle 0 0, .corridorLower 0 1, .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 25 0]

-- Cycle fingerprint 2338686051e9c9bad8ddead004c6ee27225f3348302a7f72ab63d14c8cdf4870.
def localCycle00026 : Cycle where
  length := 12
  data := {
    node := ![.distance 5 6, .distance 4 6, .distance 3 6, .distance 2 6, .distance 1 6, .distance 1 3, .distance 1 4, .distance 0 4, .distance 4 5, .theta 4, .zero, .theta 6, .distance 5 6]
    constant := ![0, 0, 0, 0, -2, -2, 0, -1, -1, 0, 0, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1]
    strict := ![true, true, true, true, false, false, true, false, false, false, false, false] }
  origin := ![.triangle 34 2, .triangle 32 2, .triangle 27 2, .triangle 18 2, .gapLower 1 5, .gapLower 1 4, .triangle 2 2, .triangle 12 0, .corridorLower 4 5, .thetaLower 4, .thetaUpper 6, .corridorUpper 5 6]

-- Cycle fingerprint 234f8090dcf64527f8a20af286fc53308c84b5f380df84a67e9d487a94843391.
def localCycle00027 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 3, .distance 1 4, .distance 4 6, .distance 3 4, .distance 0 4, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, 0, 0, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, true, false, false, true] }
  origin := ![.corridorUpper 2 3, .triangle 15 2, .triangle 19 2, .triangle 23 0, .triangle 32 0, .triangle 9 2, .triangle 12 0, .corridorLower 4 5, .thetaNext 3]

-- Cycle fingerprint 288248ca73cf81170c3acad7cde94193670ced8f24b4b39ebf05f8a0de07efcc.
def localCycle00028 : Cycle where
  length := 5
  data := {
    node := ![.theta 3, .distance 1 3, .distance 3 4, .distance 2 3, .distance 3 6, .theta 3]
    constant := ![3, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false] }
  origin := ![.corridorUpper 1 3, .triangle 19 0, .triangle 25 0, .triangle 27 0, .corridorLower 3 6]

-- Cycle fingerprint 28b80fe553dd982bc7eba9b160e865b578ba68691740076f41e799b0208d31e7.
def localCycle00029 : Cycle where
  length := 10
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 1 2, .distance 2 3, .distance 3 6, .distance 5 6, .distance 4 6, .distance 0 4, .distance 4 5, .theta 4]
    constant := ![3, 0, -1, -1, -1, 0, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, true, true, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 16 0, .triangle 15 0, .triangle 27 0, .triangle 33 1, .triangle 34 2, .triangle 13 0, .triangle 12 0, .corridorLower 4 5]

-- Cycle fingerprint 2909974737b0ff7a0fc4e5a2906828a65b3b47d1379731298a475ceaa028cb91.
def localCycle00030 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 3 5, .distance 5 6, .distance 4 6, .distance 2 4, .distance 1 4, .distance 0 4, .distance 4 5, .theta 4]
    constant := ![3, 0, -1, 0, -1, 0, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, true, true, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 31 2, .triangle 33 0, .triangle 34 2, .triangle 29 0, .triangle 16 2, .triangle 2 2, .triangle 12 0, .corridorLower 4 5]

-- Cycle fingerprint 29f9a214c136ce13df8963c6d04dd67bd59e362ced61f7c877401bc83e4e7e75.
def localCycle00031 : Cycle where
  length := 9
  data := {
    node := ![.distance 2 3, .distance 1 2, .distance 0 1, .theta 1, .zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 2 3]
    constant := ![-1, -2, -2, 0, 0, 3, 0, 0, -1]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, true, false] }
  origin := ![.triangle 15 0, .gapLower 1 1, .gapLower 1 0, .thetaLower 1, .thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 27 0]

-- Cycle fingerprint 2cc63c30bbeb512ac6b6e692697b7c5209b90f8f61acaeebc76fb63d83e31384.
def localCycle00032 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 1 3, .distance 1 4, .distance 1 5, .distance 1 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, 0, -1, 0, -2, 0, -2, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, true, false, true, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 21 0, .triangle 19 2, .gapLower 1 3, .triangle 17 1, .gapLower 1 1, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint 2eeb717854d5534f136cafd416abc919a61db05b565fc8290a620ce26497f572.
def localCycle00033 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 1 4, .distance 1 5, .distance 0 1, .theta 1, .zero]
    constant := ![0, 3, 0, -1, -2, -1, -2, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 23 0, .gapLower 1 3, .triangle 3 0, .gapLower 1 0, .thetaLower 1]

-- Cycle fingerprint 314d335f91cf606b28803fbb47b9f0be5694d7a0bd67a6ea134d4d4fd267f55d.
def localCycle00034 : Cycle where
  length := 9
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 1 3, .distance 3 4, .distance 2 3, .distance 3 6, .distance 4 6, .distance 5 6, .theta 5]
    constant := ![3, 0, -1, -1, -1, -1, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, true, true, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 20 0, .triangle 19 0, .triangle 25 0, .triangle 27 0, .triangle 32 1, .triangle 34 1, .corridorLower 5 6]

-- Cycle fingerprint 31c2206412be8aafa78cbeead9f69e0a25752ac8f89e8fe08edf9d5aa5eaecd2.
def localCycle00035 : Cycle where
  length := 6
  data := {
    node := ![.theta 4, .distance 3 4, .distance 1 3, .distance 3 5, .distance 5 6, .distance 4 5, .theta 4]
    constant := ![3, -1, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 19 0, .triangle 20 0, .triangle 33 0, .triangle 34 0, .corridorLower 4 5]

-- Cycle fingerprint 332cc52b7029845fffd531f30bd5044cef76231465d7003a6fea911e467a4710.
def localCycle00036 : Cycle where
  length := 6
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 3, .distance 3 5, .distance 5 6, .distance 4 5, .theta 4]
    constant := ![3, -1, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 0, .triangle 26 0, .triangle 33 0, .triangle 34 0, .corridorLower 4 5]

-- Cycle fingerprint 33afa973b286000b78a81732291956859e553ff6bc12db54c0043516ba308324.
def localCycle00037 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 3, .distance 3 4, .distance 4 6, .distance 0 4, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, 0, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false, true] }
  origin := ![.corridorUpper 2 3, .triangle 15 2, .triangle 19 0, .triangle 32 0, .triangle 13 0, .triangle 12 0, .corridorLower 4 5, .thetaNext 3]

-- Cycle fingerprint 3589e22d1251e85e207711531ae8b200cef8913e73a5c3b9e684617c2f8c2ccf.
def localCycle00038 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 3, .distance 1 2, .distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 3 6, .distance 3 4, .distance 1 3]
    constant := ![0, -2, -1, 0, 0, 3, -1, 0, -1]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, true, false] }
  origin := ![.gapLower 1 2, .gapLower 1 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 27 0, .triangle 32 1, .triangle 19 0]

-- Cycle fingerprint 3613446bd866db898dfc7deae3261687f6fdba214c47a60745d5465382b6b8e8.
def localCycle00039 : Cycle where
  length := 9
  data := {
    node := ![.distance 2 3, .distance 1 2, .distance 0 1, .theta 0, .zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 2 3]
    constant := ![-1, -3, -1, 0, 0, 3, 0, 0, -1]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, true, false] }
  origin := ![.triangle 15 0, .gapLower 1 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 27 0]

-- Cycle fingerprint 375ea4c2c7514e5d8c8336103f287623329b36af107ecf83787fe2c31825d88f.
def localCycle00040 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 3, .distance 2 3, .distance 3 6, .distance 3 4, .distance 1 3, .distance 3 5, .distance 0 3, .distance 0 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, -1, 0, -1, -1, -1, 0, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, true, true, false, false] }
  origin := ![.thetaUpper 3, .corridorUpper 2 3, .triangle 27 0, .triangle 32 1, .triangle 19 0, .triangle 20 0, .triangle 10 0, .triangle 5 1, .triangle 0 1, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint 391402375facd85d6513782bfd2ac90f402a40cb5f27e9a8e2d7dd5fd905aaaf.
def localCycle00041 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 1 2, .distance 2 3, .distance 2 4, .distance 4 5, .distance 3 4, .distance 4 6, .theta 4, .theta 3, .theta 2]
    constant := ![3, -1, 0, -1, -1, -1, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, true, true] }
  origin := ![.corridorUpper 1 2, .triangle 15 0, .triangle 25 2, .triangle 28 0, .triangle 31 0, .triangle 32 0, .corridorLower 4 6, .thetaNext 3, .thetaNext 2]

-- Cycle fingerprint 3dbe551122f8947322f827df98068866c44f1067cdba1c21cf383ef2ed742ac8.
def localCycle00042 : Cycle where
  length := 9
  data := {
    node := ![.distance 2 4, .distance 1 2, .distance 0 1, .theta 1, .theta 0, .zero, .theta 6, .distance 5 6, .distance 4 6, .distance 2 4]
    constant := ![-1, -2, -2, 0, 0, 0, 3, 0, -1]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, true, false, false, false, true, false] }
  origin := ![.triangle 16 0, .gapLower 1 1, .gapLower 1 0, .thetaNext 0, .thetaLower 0, .thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 29 0]

-- Cycle fingerprint 3f0de987ee7ec2a7df53413973586ca15e21179d12b65b74f85c16cb454f600f.
def localCycle00043 : Cycle where
  length := 5
  data := {
    node := ![.distance 2 3, .distance 2 5, .distance 5 6, .distance 4 6, .distance 3 4, .distance 2 3]
    constant := ![0, 2, 0, -1, -1]
    coefficient := ![0, 0, 0, 0, 0]
    strict := ![true, true, true, false, false] }
  origin := ![.triangle 26 2, .gapUpper 5 5, .triangle 34 2, .triangle 32 0, .triangle 25 0]

-- Cycle fingerprint 40545932fa7aa145e1e42b7fa600c16b40f51c3eb25a2bbddf8361857b0b1fbe.
def localCycle00044 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 2 3, .distance 2 4, .distance 4 6, .distance 3 4, .distance 1 3, .distance 3 5, .theta 3]
    constant := ![3, 0, -1, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 25 2, .triangle 29 0, .triangle 32 0, .triangle 19 0, .triangle 20 0, .corridorLower 3 5]

-- Cycle fingerprint 411cf94a90fcf69f3f7fd26c170fc9a8383bea0af4ba86a794a9f6e717607403.
def localCycle00045 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 4, .distance 2 3, .distance 1 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 0, .triangle 25 0, .triangle 15 0, .triangle 0 0, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint 422971613005ef0bd29b9ef45e224d4eeb9908a51a1d3bbbe642fd875dc6b1ec.
def localCycle00046 : Cycle where
  length := 11
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 4, .distance 3 5, .distance 1 3, .distance 3 6, .distance 5 6, .distance 4 6, .distance 0 4, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, -1, 0, -1, -1, 0, 0, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, true, false, false, false, true] }
  origin := ![.corridorUpper 2 3, .triangle 25 0, .triangle 31 2, .triangle 20 0, .triangle 21 0, .triangle 33 1, .triangle 34 2, .triangle 13 0, .triangle 12 0, .corridorLower 4 5, .thetaNext 3]

-- Cycle fingerprint 426fdf46015497c4e9aeaec0a52ec29a3c094174273d753ab7b226c9c3391222.
def localCycle00047 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 2, .distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 2 4, .distance 4 6, .distance 3 4, .distance 1 3, .distance 1 2]
    constant := ![-1, -1, 0, 0, 3, 0, -1, -1, -1, 0]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, false, false, false] }
  origin := ![.triangle 0 0, .corridorLower 0 1, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 25 2, .triangle 29 0, .triangle 32 0, .triangle 19 0, .gapLower 1 2]

-- Cycle fingerprint 460514d6cc83c0d028f860ce407f9df91151c1c57f8c8785d2d1a89aaf732121.
def localCycle00048 : Cycle where
  length := 10
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 3, .distance 1 2, .distance 2 6, .distance 3 6, .distance 5 6, .distance 4 6, .distance 0 4, .distance 4 5, .theta 4]
    constant := ![3, -1, -1, -1, 0, 0, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, true, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 0, .triangle 15 0, .triangle 18 0, .triangle 27 1, .triangle 33 1, .triangle 34 2, .triangle 13 0, .triangle 12 0, .corridorLower 4 5]

-- Cycle fingerprint 46141d1289555f9827b3f475616466dbf1325b773cb680e056d94d809013fe2a.
def localCycle00049 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 4 5, .distance 2 5, .distance 1 2, .distance 2 4, .distance 2 3, .distance 3 6, .distance 4 6, .theta 4]
    constant := ![3, -1, 0, -1, -1, 0, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 31 0, .gapLower 5 4, .triangle 17 0, .triangle 16 0, .triangle 25 1, .triangle 27 0, .triangle 32 1, .corridorLower 4 6]

-- Cycle fingerprint 468ef8c8bd31c5535802dc119046cde744a8ec9f6151def4d93ec40b64ba642b.
def localCycle00050 : Cycle where
  length := 13
  data := {
    node := ![.distance 3 6, .distance 2 6, .distance 1 6, .distance 1 3, .distance 1 4, .distance 1 5, .distance 1 2, .distance 0 1, .theta 0, .zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6]
    constant := ![0, 0, -2, 0, 0, -2, -1, -1, 0, 0, 3, 0, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![true, true, false, true, true, false, false, false, false, false, false, true, true] }
  origin := ![.triangle 27 2, .triangle 18 2, .gapLower 1 5, .triangle 19 2, .triangle 22 2, .gapLower 1 2, .triangle 0 0, .corridorLower 0 1, .thetaLower 0, .thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2]

-- Cycle fingerprint 46b157eed94c04617dccd74d5f8919e60284156085af571ecd7b8d571ad5e1d0.
def localCycle00051 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 4 6, .distance 2 4, .distance 2 3, .distance 3 5, .distance 1 3, .distance 1 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, -1, -1, 0, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, true, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 32 0, .triangle 29 0, .triangle 25 1, .triangle 26 0, .triangle 20 0, .triangle 15 1, .triangle 0 0, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint 47dad1ee5f0782910928be91a19498503cd5dac5e8394503f1133d1818218aa0.
def localCycle00052 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 1 2, .distance 2 5, .distance 4 5, .distance 0 4, .distance 4 6, .theta 4]
    constant := ![3, 0, -1, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 16 0, .triangle 17 0, .triangle 28 1, .triangle 12 0, .triangle 13 0, .corridorLower 4 6]

-- Cycle fingerprint 4b3cb3a1321da42435205a11386c8914a1eea40da5e1a631cba2932f54f59d68.
def localCycle00053 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 1 3, .distance 3 6, .distance 5 6, .distance 4 6, .distance 0 4, .distance 4 5, .theta 4]
    constant := ![3, -1, -1, 0, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 19 0, .triangle 21 0, .triangle 33 1, .triangle 34 2, .triangle 13 0, .triangle 12 0, .corridorLower 4 5]

-- Cycle fingerprint 4d599a757a758831129bbcdde5188a9242e1a7a5ecf19eeb3696da9a22238c4b.
def localCycle00054 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 2 3, .distance 3 4, .distance 3 5, .distance 1 3, .distance 1 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, 0, -1, -1, 0, -1, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, true, false, true, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 27 0, .triangle 25 0, .triangle 31 2, .triangle 20 0, .triangle 15 1, .triangle 0 0, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint 4d9ccbbd8fcc4b446da7bef1147a9045238ff097f2c079a9a869db171ddc3338.
def localCycle00055 : Cycle where
  length := 10
  data := {
    node := ![.theta 0, .zero, .theta 3, .distance 2 3, .distance 3 6, .distance 3 4, .distance 1 3, .distance 1 2, .distance 0 1, .theta 1, .theta 0]
    constant := ![0, 0, 3, -1, 0, -1, 0, -1, -3, 0]
    coefficient := ![0, 1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, false, false, true] }
  origin := ![.thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 27 0, .triangle 32 1, .triangle 19 0, .gapLower 1 2, .triangle 0 0, .gapLower 1 0, .thetaNext 0]

-- Cycle fingerprint 4e6fb2ba9260d24de1aad22fea2b4bdf7c43f917106f40bf92d6993b2e0d79c2.
def localCycle00056 : Cycle where
  length := 10
  data := {
    node := ![.theta 3, .distance 2 3, .distance 2 4, .distance 2 5, .distance 5 6, .distance 4 6, .distance 3 4, .distance 0 4, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, 0, 0, -1, 0, -1, 0, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, false, false, false, true] }
  origin := ![.corridorUpper 2 3, .triangle 25 2, .triangle 28 2, .triangle 30 0, .triangle 34 2, .triangle 32 0, .gapLower 4 2, .triangle 12 0, .corridorLower 4 5, .thetaNext 3]

-- Cycle fingerprint 4e9b2629dfc8c9ff953721933d193803c15c22f521a4649e4c80c6a7f9e0f5b4.
def localCycle00057 : Cycle where
  length := 3
  data := {
    node := ![.distance 1 4, .theta 1, .distance 1 6, .distance 1 4]
    constant := ![-1, 2, -2]
    coefficient := ![0, 1, 0]
    strict := ![false, false, false] }
  origin := ![.corridorLower 1 4, .gapLower 1 6, .gapLower 1 5]

-- Cycle fingerprint 4f63b219e2b38ffd074e55cd6bb78f94aa058d6c094116f0443c76bed08b2e3f.
def localCycle00058 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 3, .distance 3 4, .distance 3 5, .distance 0 3, .distance 0 2, .distance 0 1, .theta 0, .zero, .theta 1, .distance 1 6, .distance 1 3]
    constant := ![-1, 0, -1, 0, 0, -1, 0, 0, 1, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![false, true, false, false, true, false, false, false, false, true] }
  origin := ![.triangle 19 0, .triangle 31 2, .triangle 10 0, .gapLower 0 2, .triangle 0 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 1, .gapLower 1 6, .triangle 21 1]

-- Cycle fingerprint 5194e5a1c819c71055ac6ebf27d09e77cb0ade5deee65955cdda51e4703700cc.
def localCycle00059 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 1 4, .distance 4 5, .distance 3 4, .distance 2 3, .distance 3 6, .distance 4 6, .theta 4]
    constant := ![3, -1, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false] }
  origin := ![.corridorUpper 1 4, .triangle 22 0, .triangle 31 0, .triangle 25 0, .triangle 27 0, .triangle 32 1, .corridorLower 4 6]

-- Cycle fingerprint 54a66e493e3473bde7d002f5ffc7e58e1ffe4133b09ec0113748ba7750338c70.
def localCycle00060 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 3, .distance 1 6, .distance 0 1, .theta 1, .zero, .theta 3, .distance 2 3, .distance 1 3]
    constant := ![-2, -1, -2, 0, 0, 3, 0]
    coefficient := ![0, 0, 0, 0, 1, 1, 0]
    strict := ![false, false, false, false, false, false, true] }
  origin := ![.gapLower 1 5, .triangle 4 0, .gapLower 1 0, .thetaLower 1, .thetaUpper 3, .corridorUpper 2 3, .triangle 15 2]

-- Cycle fingerprint 54ca3878f49c2bd843547607fa2cb44ba4a02d6a7a200b2f34d8fdb8385c02ca.
def localCycle00061 : Cycle where
  length := 9
  data := {
    node := ![.distance 2 3, .distance 1 3, .distance 1 6, .distance 1 5, .distance 1 2, .distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3]
    constant := ![0, -2, 0, -2, -1, -1, 0, 0, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1, 1]
    strict := ![true, false, true, false, false, false, false, false, false] }
  origin := ![.triangle 15 2, .gapLower 1 5, .triangle 24 1, .gapLower 1 2, .triangle 0 0, .corridorLower 0 1, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3]

-- Cycle fingerprint 5733ead26b5b52b5c31439d1654986a2878a72d28330b3623fd1ba6db1e81354.
def localCycle00062 : Cycle where
  length := 8
  data := {
    node := ![.distance 4 5, .theta 4, .theta 3, .theta 2, .theta 1, .distance 1 6, .distance 0 6, .distance 0 4, .distance 4 5]
    constant := ![-1, 0, 0, 0, 1, 0, 0, -1]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![false, true, true, true, false, true, true, false] }
  origin := ![.corridorLower 4 5, .thetaNext 3, .thetaNext 2, .thetaNext 1, .gapLower 1 6, .triangle 4 2, .triangle 13 1, .triangle 12 0]

-- Cycle fingerprint 575f09772bb820c91919545a7cf91d7f96de05c5cc6341b5c30e1305edb3efdf.
def localCycle00063 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .theta 1, .zero, .theta 3, .distance 2 3, .distance 3 6, .distance 3 4, .distance 3 5, .distance 1 5, .distance 1 3, .distance 0 1]
    constant := ![-2, 0, 0, 3, -1, 0, 0, 0, -2, -1]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, false, false, false] }
  origin := ![.gapLower 1 0, .thetaLower 1, .thetaUpper 3, .corridorUpper 2 3, .triangle 27 0, .triangle 32 1, .triangle 31 2, .gapLower 5 3, .gapLower 1 3, .triangle 1 0]

-- Cycle fingerprint 58aff2e0ee323701e88e2712da09efa5105f14d96faa198ee1de7fb132564929.
def localCycle00064 : Cycle where
  length := 10
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 3, .distance 1 4, .distance 1 5, .distance 5 6, .distance 4 6, .distance 0 4, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, 0, 0, 0, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, true, false, false, false, true] }
  origin := ![.corridorUpper 2 3, .triangle 15 2, .triangle 19 2, .triangle 22 2, .triangle 24 0, .triangle 34 2, .triangle 13 0, .triangle 12 0, .corridorLower 4 5, .thetaNext 3]

-- Cycle fingerprint 59eb4095046d42467e49f148ab275c597618561e57ee437b26cd68d4395efce6.
def localCycle00065 : Cycle where
  length := 8
  data := {
    node := ![.distance 3 5, .distance 0 3, .distance 0 2, .distance 0 1, .theta 1, .distance 1 6, .distance 1 3, .distance 3 4, .distance 3 5]
    constant := ![-1, 0, 0, -2, 2, 0, -1, 0]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![false, false, true, false, false, true, false, true] }
  origin := ![.triangle 10 0, .gapLower 0 2, .triangle 0 1, .gapLower 1 0, .gapLower 1 6, .triangle 21 1, .triangle 19 0, .triangle 31 2]

-- Cycle fingerprint 5c5f31992d733c23ca381660d973decc6636788c5b155f75b6a4271c15453da7.
def localCycle00066 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 3, .distance 3 5, .distance 1 3, .distance 3 6, .distance 5 6, .distance 4 5, .theta 4]
    constant := ![3, -1, -1, -1, -1, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 0, .triangle 26 0, .triangle 20 0, .triangle 21 0, .triangle 33 1, .triangle 34 0, .corridorLower 4 5]

-- Cycle fingerprint 5ca91127718b82423bc5d6b9b092d4b9113a6ae74ead0b5aca8b33bd61d464bf.
def localCycle00067 : Cycle where
  length := 12
  data := {
    node := ![.distance 5 6, .distance 4 6, .distance 3 6, .distance 2 6, .distance 1 6, .distance 1 3, .distance 1 4, .distance 1 5, .distance 0 1, .theta 0, .zero, .theta 6, .distance 5 6]
    constant := ![0, 0, 0, 0, -2, 0, -2, -1, -1, 0, 0, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1]
    strict := ![true, true, true, true, false, true, false, false, false, false, false, false] }
  origin := ![.triangle 34 2, .triangle 32 2, .triangle 27 2, .triangle 18 2, .gapLower 1 5, .triangle 19 2, .gapLower 1 3, .triangle 3 0, .corridorLower 0 1, .thetaLower 0, .thetaUpper 6, .corridorUpper 5 6]

-- Cycle fingerprint 5cf55d992eb4818302ae72b383e2c1da3704eb928b82034fcbdd1f6088c7e83c.
def localCycle00068 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 4, .distance 4 6, .distance 0 4, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true] }
  origin := ![.corridorUpper 2 3, .triangle 25 0, .triangle 32 0, .triangle 13 0, .triangle 12 0, .corridorLower 4 5, .thetaNext 3]

-- Cycle fingerprint 5e29f29680339a5164dc989c89d8022feaa528ba15801bee92dcc6b4bd323934.
def localCycle00069 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 1 4, .distance 4 5, .distance 2 4, .distance 4 6, .distance 5 6, .theta 5, .theta 4]
    constant := ![3, 0, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, true, false, true] }
  origin := ![.corridorUpper 3 4, .triangle 19 2, .triangle 22 0, .triangle 28 0, .triangle 29 0, .triangle 34 1, .corridorLower 5 6, .thetaNext 4]

-- Cycle fingerprint 5ff02fe104436a3d3bf86c372f8c1eb97e73ff28f245e56910bf43602c702801.
def localCycle00070 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 2, .distance 0 1, .theta 1, .zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 2 3, .distance 1 2]
    constant := ![-1, -3, 0, 0, 3, 0, 0, -1, -1]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, false, false] }
  origin := ![.triangle 0 0, .gapLower 1 0, .thetaLower 1, .thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 27 0, .triangle 15 0]

-- Cycle fingerprint 62adccc8300b1959634482ca30bb9abbf9cdd105741569bb44833136e87301e5.
def localCycle00071 : Cycle where
  length := 5
  data := {
    node := ![.theta 3, .distance 1 3, .distance 3 5, .distance 2 3, .distance 3 6, .theta 3]
    constant := ![3, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false] }
  origin := ![.corridorUpper 1 3, .triangle 20 0, .triangle 26 0, .triangle 27 0, .corridorLower 3 6]

-- Cycle fingerprint 633a621d61789a8ac4038a47b875a84726317e4b891db140b512bdb07ee7d54b.
def localCycle00072 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 3, .distance 2 3, .distance 3 6, .distance 3 4, .distance 1 4, .distance 1 5, .distance 1 3, .distance 1 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, -1, 0, 0, 0, -2, 0, -2, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true, false, true, false, false, false] }
  origin := ![.thetaUpper 3, .corridorUpper 2 3, .triangle 27 0, .triangle 32 1, .gapLower 4 3, .triangle 22 2, .gapLower 1 3, .triangle 15 1, .gapLower 1 1, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint 643dc50bd320ea94fee513e05471f03215c68c2d3157e7250f335490d8d29e14.
def localCycle00073 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 2 3, .distance 1 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, 0, -1, -1, -2, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 27 0, .triangle 15 0, .gapLower 1 1, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint 646e00c23a8848cd65c87040ab5567d8484a645593bb2f1ef44c2e0833cd9058.
def localCycle00074 : Cycle where
  length := 6
  data := {
    node := ![.theta 3, .distance 1 3, .distance 3 5, .distance 3 4, .distance 2 3, .distance 3 6, .theta 3]
    constant := ![3, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false] }
  origin := ![.corridorUpper 1 3, .triangle 20 0, .triangle 31 1, .triangle 25 0, .triangle 27 0, .corridorLower 3 6]

-- Cycle fingerprint 66a3ae3ba9c6a68d890ae4132309d8d5ce3d6cc1f916db99a1864f320685e031.
def localCycle00075 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 3, .distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 3 6, .distance 3 4, .distance 1 4, .distance 1 5, .distance 1 3]
    constant := ![-1, -1, 0, 0, 3, -1, 0, 0, -2, -2]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, false, false, false] }
  origin := ![.triangle 1 0, .corridorLower 0 1, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 27 0, .triangle 32 1, .gapLower 4 3, .gapLower 1 4, .gapLower 1 3]

-- Cycle fingerprint 680c2751dd2fe91a73b09949334e398a1671f14aa2fb33d069de1e363d106990.
def localCycle00076 : Cycle where
  length := 3
  data := {
    node := ![.distance 2 5, .distance 1 5, .distance 1 2, .distance 2 5]
    constant := ![0, -3, 2]
    coefficient := ![0, 0, 0]
    strict := ![false, false, true] }
  origin := ![.gapLower 5 4, .gapLower 1 2, .gapUpper 2 2]

-- Cycle fingerprint 6a1864bef040aee89c04787d7bb11d74c68e37fd3016cf98a071d9f28af07a1c.
def localCycle00077 : Cycle where
  length := 8
  data := {
    node := ![.theta 6, .distance 5 6, .distance 4 6, .distance 2 4, .distance 1 2, .distance 0 1, .theta 0, .zero, .theta 6]
    constant := ![3, 0, -1, -1, -3, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, false, false, false, false, false, false] }
  origin := ![.corridorUpper 5 6, .triangle 34 2, .triangle 29 0, .triangle 16 0, .gapLower 1 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 6]

-- Cycle fingerprint 6fb3b476f387cb8b1aafdad675465a3521ec91669e3d2babe00b7fae22931128.
def localCycle00078 : Cycle where
  length := 8
  data := {
    node := ![.distance 5 6, .distance 4 6, .distance 3 6, .distance 1 3, .distance 1 4, .distance 1 5, .distance 1 2, .distance 2 5, .distance 5 6]
    constant := ![0, 0, -1, 0, -3, 0, 2, 2]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![true, true, false, true, false, true, true, true] }
  origin := ![.triangle 34 2, .triangle 32 2, .triangle 21 0, .triangle 19 2, .gapLower 1 3, .triangle 17 1, .gapUpper 2 2, .gapUpper 5 5]

-- Cycle fingerprint 71205de578173ae6b1b8e911eefef38377829f01772457349c86c17638810c11.
def localCycle00079 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 2 4, .distance 4 6, .distance 3 4, .distance 0 4, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, 0, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, false, false, true] }
  origin := ![.corridorUpper 2 3, .triangle 25 2, .triangle 29 0, .triangle 32 0, .triangle 9 2, .triangle 12 0, .corridorLower 4 5, .thetaNext 3]

-- Cycle fingerprint 7208884fc6b5acd7a6dc8a9f3c6a1ea382ce974231ff24fb061f5cb4c51f45fc.
def localCycle00080 : Cycle where
  length := 9
  data := {
    node := ![.distance 3 6, .distance 1 6, .distance 1 4, .distance 1 2, .distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 3 6]
    constant := ![0, -2, 0, -2, -1, 0, 0, 3, -1]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![true, false, true, false, false, false, false, false, false] }
  origin := ![.triangle 21 2, .gapLower 1 5, .triangle 16 1, .gapLower 1 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 27 0]

-- Cycle fingerprint 73753195de7419b491e9ae099bf4885fe126e34b78eed02a4a6bbf1d1f40e58b.
def localCycle00081 : Cycle where
  length := 7
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 2 3, .distance 3 4, .distance 4 6, .distance 5 6, .theta 5]
    constant := ![3, 0, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, true, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 26 0, .triangle 25 0, .triangle 32 0, .triangle 34 1, .corridorLower 5 6]

-- Cycle fingerprint 749da69e16b75100e696b68d313d628d1316f966ac86a0678517de32fa0969a5.
def localCycle00082 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 3 4, .distance 1 3, .distance 3 5, .distance 2 3, .distance 3 6, .distance 4 6, .theta 4]
    constant := ![3, -1, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 19 0, .triangle 20 0, .triangle 26 0, .triangle 27 0, .triangle 32 1, .corridorLower 4 6]

-- Cycle fingerprint 79bd2092f40034fe75e04d60b1d43e41e51f8ecaa87a87ab610344340d13393d.
def localCycle00083 : Cycle where
  length := 9
  data := {
    node := ![.distance 3 6, .distance 1 3, .distance 1 4, .distance 0 1, .theta 1, .zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6]
    constant := ![-1, -2, -1, -2, 0, 0, 3, 0, 0]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, false, false, false, false, true, true] }
  origin := ![.triangle 21 0, .gapLower 1 4, .triangle 2 0, .gapLower 1 0, .thetaLower 1, .thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2]

-- Cycle fingerprint 7a5292c0d6d002c406a90406488524e5316ce174e7d38bc84701d799cafbf9b5.
def localCycle00084 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 3, .distance 3 6, .distance 4 6, .distance 1 4, .distance 0 4, .distance 4 5, .theta 4]
    constant := ![3, -1, -1, 0, -1, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 0, .triangle 27 0, .triangle 32 1, .triangle 23 0, .triangle 2 2, .triangle 12 0, .corridorLower 4 5]

-- Cycle fingerprint 7a5c39c3dd6aef6fe51c65626ee4e4f9f13eb0f1d89dc8c3166e5bc9ef6536d6.
def localCycle00085 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 1 4, .distance 4 5, .distance 2 4, .distance 4 6, .distance 5 6, .theta 5, .theta 4]
    constant := ![3, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, true] }
  origin := ![.corridorUpper 1 4, .triangle 22 0, .triangle 28 0, .triangle 29 0, .triangle 34 1, .corridorLower 5 6, .thetaNext 4]

-- Cycle fingerprint 7cc9f06f75f9c4a23fafad1310fba47e756d489cc9cdb83dd7dbf1a32af914eb.
def localCycle00086 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .theta 3, .distance 2 3, .distance 3 6, .distance 1 6, .distance 1 4, .distance 0 4, .distance 4 5, .theta 4]
    constant := ![0, 3, -1, 0, -3, 0, -1, -1]
    coefficient := ![0, 1, 0, 0, 0, 0, 0, 0]
    strict := ![true, false, false, false, false, true, false, false] }
  origin := ![.thetaNext 3, .corridorUpper 2 3, .triangle 27 0, .gapLower 6 2, .gapLower 1 5, .triangle 2 2, .triangle 12 0, .corridorLower 4 5]

-- Cycle fingerprint 7e2f3b1380934eb028f52671578db233b99210dcf3e50e04e2b1bfb78035946a.
def localCycle00087 : Cycle where
  length := 10
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 2, .distance 2 6, .distance 5 6, .distance 3 6, .distance 4 6, .distance 0 4, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, -1, -1, 0, 0, 0, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, true, false, false, false, true] }
  origin := ![.corridorUpper 2 3, .triangle 15 0, .triangle 18 0, .triangle 30 1, .triangle 33 2, .triangle 32 1, .triangle 13 0, .triangle 12 0, .corridorLower 4 5, .thetaNext 3]

-- Cycle fingerprint 7f37112fcaf32676a637cdf8b9feda80ccd7f2da747d1884f1db4c2c55d1e290.
def localCycle00088 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 2 3, .distance 3 4, .distance 1 3, .distance 3 5, .distance 0 3, .theta 0, .zero]
    constant := ![0, 3, 0, 0, -1, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 27 0, .triangle 25 0, .triangle 19 0, .triangle 20 0, .triangle 10 0, .corridorLower 0 3, .thetaLower 0]

-- Cycle fingerprint 7f8cad7a0c006cd971792e0ae120aa147d786e7a48d2e1cd0f372b0456ba075d.
def localCycle00089 : Cycle where
  length := 4
  data := {
    node := ![.distance 1 3, .distance 1 2, .distance 2 5, .distance 3 5, .distance 1 3]
    constant := ![-3, 2, 0, -1]
    coefficient := ![0, 0, 0, 0]
    strict := ![false, true, false, false] }
  origin := ![.gapLower 1 2, .gapUpper 2 2, .gapLower 5 4, .triangle 20 0]

-- Cycle fingerprint 810272ee07644e8a4ac52706ee77dcadfdafc245e905a9a5b81136b861eef014.
def localCycle00090 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 5, .distance 0 1, .theta 0, .zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 1 3, .distance 1 4, .distance 1 5]
    constant := ![-1, -1, 0, 0, 3, 0, 0, -1, -2, -2]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, false, false, false] }
  origin := ![.triangle 3 0, .corridorLower 0 1, .thetaLower 0, .thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 21 0, .gapLower 1 4, .gapLower 1 3]

-- Cycle fingerprint 82190763a960bced7b82708ed585d179b5d77d9afa3baca2d80a2e30c7eb71d9.
def localCycle00091 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 1 4, .distance 4 6, .distance 0 4, .distance 4 5, .theta 4]
    constant := ![3, 0, 0, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 16 2, .triangle 23 0, .triangle 13 0, .triangle 12 0, .corridorLower 4 5]

-- Cycle fingerprint 82b45b80c840c636f21eb383670da444ad17699961e20f97da302437ff6fa67e.
def localCycle00092 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 3 4, .distance 4 6, .distance 2 4, .distance 1 4, .distance 0 4, .distance 4 5, .theta 4]
    constant := ![3, -1, -1, 0, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 32 0, .triangle 29 0, .triangle 16 2, .triangle 2 2, .triangle 12 0, .corridorLower 4 5]

-- Cycle fingerprint 84cb98fceaed0995746b442e538f9e44c030bc32a41a57d217531e9f52cb6020.
def localCycle00093 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 4, .distance 1 3, .distance 1 5, .distance 5 6, .distance 3 5, .theta 3]
    constant := ![3, -1, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 25 0, .triangle 19 0, .triangle 20 2, .triangle 24 0, .triangle 33 0, .corridorLower 3 5]

-- Cycle fingerprint 8695e95c3d9b42b988f1f331e1fa48b928e1a5096df25261257b471e968065b2.
def localCycle00094 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 2 5, .distance 5 6, .distance 4 6, .distance 1 4, .distance 0 4, .distance 4 5, .theta 4]
    constant := ![3, 0, 0, -1, 0, -1, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, true, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 28 2, .triangle 30 0, .triangle 34 2, .triangle 23 0, .triangle 2 2, .triangle 12 0, .corridorLower 4 5]

-- Cycle fingerprint 86bef04538bb77a1fcd2dc42b2226703e9269b3a876a8a89aa4047fd85954e1b.
def localCycle00095 : Cycle where
  length := 5
  data := {
    node := ![.theta 4, .distance 3 4, .distance 4 5, .distance 0 4, .distance 4 6, .theta 4]
    constant := ![3, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 31 0, .triangle 12 0, .triangle 13 0, .corridorLower 4 6]

-- Cycle fingerprint 86ec0aa2e1e6f72b37acb0eca1bb9c957bafddf26019074fcda5264395768dfe.
def localCycle00096 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 3, .distance 1 6, .distance 1 4, .distance 1 2, .distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 1 3]
    constant := ![0, -2, 0, -2, -1, 0, 0, 3, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![true, false, true, false, false, false, false, false, true] }
  origin := ![.triangle 21 2, .gapLower 1 4, .triangle 16 1, .gapLower 1 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 15 2]

-- Cycle fingerprint 8769ccd6c192d1a1b8176496a95c895a46873f2cb638aec6ae667f70292d8f13.
def localCycle00097 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 3, .distance 3 6, .distance 5 6, .distance 4 6, .distance 1 4, .distance 0 4, .distance 4 5, .theta 4]
    constant := ![3, -1, -1, 0, 0, -1, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false, true, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 0, .triangle 27 0, .triangle 33 1, .triangle 34 2, .triangle 23 0, .triangle 2 2, .triangle 12 0, .corridorLower 4 5]

-- Cycle fingerprint 88e21bcfbf8eb6b6a0696bf476aec8b575ea2f09c1d91fbff6116883e0084813.
def localCycle00098 : Cycle where
  length := 9
  data := {
    node := ![.distance 4 6, .distance 1 4, .distance 1 5, .distance 1 2, .distance 0 1, .theta 1, .zero, .theta 6, .distance 5 6, .distance 4 6]
    constant := ![-1, -2, 0, -1, -2, 0, 0, 3, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![false, false, true, false, false, false, false, false, true] }
  origin := ![.triangle 23 0, .gapLower 1 3, .triangle 17 1, .triangle 0 0, .gapLower 1 0, .thetaLower 1, .thetaUpper 6, .corridorUpper 5 6, .triangle 34 2]

-- Cycle fingerprint 8a01a048be269d29799081124abc3d36a3e5308393ae256ea421444d0d869296.
def localCycle00099 : Cycle where
  length := 11
  data := {
    node := ![.theta 1, .zero, .theta 3, .distance 2 3, .distance 3 6, .distance 3 4, .distance 1 4, .distance 1 5, .distance 1 3, .distance 1 2, .distance 0 1, .theta 1]
    constant := ![0, 0, 3, -1, 0, 0, -2, 0, 0, -1, -2]
    coefficient := ![0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, true, true, false, false] }
  origin := ![.thetaLower 1, .thetaUpper 3, .corridorUpper 2 3, .triangle 27 0, .triangle 32 1, .gapLower 4 3, .gapLower 1 4, .triangle 20 1, .triangle 15 1, .triangle 0 0, .gapLower 1 0]

-- Cycle fingerprint 8b9e0160055da9eff658fccf0aa016223b2f6ca549fe1f7903b025286ab77435.
def localCycle00100 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 4 6, .distance 2 4, .distance 1 4, .distance 1 3, .distance 3 5, .distance 0 5, .distance 4 5, .theta 4]
    constant := ![3, -1, -1, 0, 0, -1, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false, true, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 32 0, .triangle 29 0, .triangle 16 2, .triangle 19 1, .triangle 20 0, .triangle 10 2, .triangle 12 1, .corridorLower 4 5]

-- Cycle fingerprint 8f52677f4b61ba22cb9e5633c9a0a331301fbb8b2647a99d5eb4125bfb1435d5.
def localCycle00101 : Cycle where
  length := 9
  data := {
    node := ![.distance 3 6, .distance 4 6, .distance 1 4, .distance 1 3, .distance 3 5, .distance 4 5, .theta 4, .distance 3 4, .distance 2 3, .distance 3 6]
    constant := ![0, -1, 0, -1, 0, -1, 3, -1, -1]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 0, 0]
    strict := ![true, false, false, false, true, false, false, false, false] }
  origin := ![.triangle 32 1, .triangle 23 0, .gapLower 1 4, .triangle 20 0, .triangle 31 1, .corridorLower 4 5, .corridorUpper 3 4, .triangle 25 0, .triangle 27 0]

-- Cycle fingerprint 8fbb46c75f81f4de49b710240d38b90b0482e2d3378bd8f8fee6060017d115bb.
def localCycle00102 : Cycle where
  length := 7
  data := {
    node := ![.distance 4 6, .distance 1 4, .distance 1 3, .distance 3 5, .theta 3, .distance 2 3, .distance 3 4, .distance 4 6]
    constant := ![-1, 0, -1, -1, 3, -1, -1]
    coefficient := ![0, 0, 0, 0, 1, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.triangle 23 0, .gapLower 1 4, .triangle 20 0, .corridorLower 3 5, .corridorUpper 2 3, .triangle 25 0, .triangle 32 0]

-- Cycle fingerprint 91bc19565844ade036fd4e27b8758bde9fca52ea0e67379a95afb45bc7b71ce9.
def localCycle00103 : Cycle where
  length := 8
  data := {
    node := ![.distance 5 6, .distance 4 6, .distance 1 4, .distance 1 5, .distance 0 1, .theta 0, .zero, .theta 6, .distance 5 6]
    constant := ![0, -1, -2, -1, -1, 0, 0, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 1]
    strict := ![true, false, false, false, false, false, false, false] }
  origin := ![.triangle 34 2, .triangle 23 0, .gapLower 1 3, .triangle 3 0, .corridorLower 0 1, .thetaLower 0, .thetaUpper 6, .corridorUpper 5 6]

-- Cycle fingerprint 9261f4635444a370eb8a09c137e910d5e34d349427606ce51443c628123900b6.
def localCycle00104 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 1 4, .distance 4 5, .distance 3 5, .distance 2 3, .distance 3 4, .distance 4 6, .theta 4]
    constant := ![3, -1, 0, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false] }
  origin := ![.corridorUpper 1 4, .triangle 22 0, .triangle 31 2, .triangle 26 0, .triangle 25 0, .triangle 32 0, .corridorLower 4 6]

-- Cycle fingerprint 92e03298a505e523ef289d17f0370d159fed363c5c61f54a55318b90239951a1.
def localCycle00105 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 1 3, .distance 3 4, .distance 4 5, .distance 2 4, .distance 2 3, .distance 3 6, .theta 3]
    constant := ![3, -1, -1, -1, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.corridorUpper 1 3, .triangle 19 0, .triangle 31 0, .triangle 28 0, .gapLower 2 3, .triangle 27 0, .corridorLower 3 6]

-- Cycle fingerprint 9355b87c99287add2dc707307d213f7a52c144dc10929ed18cb7f18d698eeb5b.
def localCycle00106 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 3, .distance 3 6, .distance 5 6, .distance 4 6, .distance 0 4, .distance 4 5, .theta 4]
    constant := ![3, -1, -1, 0, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 0, .triangle 27 0, .triangle 33 1, .triangle 34 2, .triangle 13 0, .triangle 12 0, .corridorLower 4 5]

-- Cycle fingerprint 94a2ce94169ef253c5ff23335bad564c0cee29f1e648c2538aa749cacf50f4a2.
def localCycle00107 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 1 2, .distance 2 3, .distance 3 4, .distance 4 5, .distance 0 4, .distance 4 6, .theta 4, .theta 3, .theta 2]
    constant := ![3, -1, -1, -1, -1, -1, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, true, true] }
  origin := ![.corridorUpper 1 2, .triangle 15 0, .triangle 25 0, .triangle 31 0, .triangle 12 0, .triangle 13 0, .corridorLower 4 6, .thetaNext 3, .thetaNext 2]

-- Cycle fingerprint 960c5d96731c45e9f5f865aaddbcdc653f3de329dbd0034d979f16fc2cc7c611.
def localCycle00108 : Cycle where
  length := 3
  data := {
    node := ![.distance 3 4, .distance 1 3, .distance 1 4, .distance 3 4]
    constant := ![2, -3, 0]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.gapUpper 3 3, .gapLower 1 4, .triangle 19 1]

-- Cycle fingerprint 96e58ccf38ee68974f674384b74670c14e4a4eedd12f0ff333b397744a290189.
def localCycle00109 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 2 4, .distance 2 5, .distance 5 6, .distance 4 6, .distance 3 4, .distance 1 3, .distance 3 5, .theta 3]
    constant := ![3, 0, 0, -1, 0, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 25 2, .triangle 28 2, .triangle 30 0, .triangle 34 2, .triangle 32 0, .triangle 19 0, .triangle 20 0, .corridorLower 3 5]

-- Cycle fingerprint 97a97a494518cf00afc68ab675d0ef61978b7a75bdfea85fbdef98baba6c2f09.
def localCycle00110 : Cycle where
  length := 9
  data := {
    node := ![.distance 4 6, .distance 1 4, .distance 1 5, .distance 1 2, .distance 0 1, .theta 0, .zero, .theta 6, .distance 5 6, .distance 4 6]
    constant := ![-1, -2, -2, -1, -1, 0, 0, 3, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![false, false, false, false, false, false, false, false, true] }
  origin := ![.triangle 23 0, .gapLower 1 3, .gapLower 1 2, .triangle 0 0, .corridorLower 0 1, .thetaLower 0, .thetaUpper 6, .corridorUpper 5 6, .triangle 34 2]

-- Cycle fingerprint 97b07eec1711b136e2036390c9899aeb710928adb718f55d10c9d7504de33e91.
def localCycle00111 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 1 3, .distance 1 4, .distance 1 5, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, 0, -1, 0, -2, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, true, false, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 21 0, .triangle 19 2, .gapLower 1 3, .triangle 3 0, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint 98c8dfeceb4bb63e61d7a35048e14aed82f1dc2aa429f4b514b702e3e06f13eb.
def localCycle00112 : Cycle where
  length := 13
  data := {
    node := ![.distance 3 6, .distance 2 6, .distance 1 6, .distance 1 3, .distance 1 4, .distance 1 5, .distance 1 2, .distance 0 1, .theta 0, .zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6]
    constant := ![0, 0, -2, 0, 0, 0, -2, -1, 0, 0, 3, 0, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![true, true, false, true, true, false, false, false, false, false, false, true, true] }
  origin := ![.triangle 27 2, .triangle 18 2, .gapLower 1 5, .triangle 19 2, .triangle 22 2, .gapLower 1 2, .gapLower 1 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2]

-- Cycle fingerprint 99600781ac5bfbaaca0de997ea3248593cdc3d5bc0054e27c4247dabbbf0ea23.
def localCycle00113 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 2, .distance 2 6, .distance 5 6, .distance 4 6, .distance 3 4, .theta 3]
    constant := ![3, -1, -1, 0, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 0, .triangle 18 0, .triangle 30 1, .triangle 34 2, .triangle 32 0, .corridorLower 3 4]

-- Cycle fingerprint 9b786d8e721a49ddf038c99d84d3f2a1d6f49a7a21f1f5d54f39bf525cd66678.
def localCycle00114 : Cycle where
  length := 6
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 3, .distance 3 5, .distance 5 6, .distance 4 5, .theta 4]
    constant := ![3, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 0, .triangle 26 0, .triangle 33 0, .triangle 34 0, .gapLower 4 0]

-- Cycle fingerprint 9d14d1dc17e161bd93c124898d818697ec9fd18f8afebafee59fb6fa07834f53.
def localCycle00115 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 2 4, .distance 4 6, .distance 3 4, .distance 0 4, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, 0, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false, true] }
  origin := ![.corridorUpper 2 3, .triangle 25 2, .triangle 29 0, .triangle 32 0, .gapLower 4 2, .triangle 12 0, .corridorLower 4 5, .thetaNext 3]

-- Cycle fingerprint 9d4cfd3c428f7c59ee465f09adcc6e743dc7904036d788b463e6a70bf7e72593.
def localCycle00116 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 2, .distance 0 1, .theta 0, .zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 1 3, .distance 1 4, .distance 1 2]
    constant := ![-2, -1, 0, 0, 3, 0, 0, -1, -2, 0]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, false, false, true] }
  origin := ![.gapLower 1 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 21 0, .gapLower 1 4, .triangle 16 1]

-- Cycle fingerprint 9d85feceb09cd5509ebfa5bb3647d8cfb6ebc1351a84e20e608b661f3f9bfab5.
def localCycle00117 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 4, .distance 1 5, .distance 1 2, .distance 2 5, .distance 5 6, .distance 4 6, .distance 2 4, .distance 1 4]
    constant := ![-3, 0, 2, 2, 0, -1, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, false, true] }
  origin := ![.gapLower 1 3, .triangle 17 1, .gapUpper 2 2, .gapUpper 5 5, .gapLower 6 5, .triangle 29 0, .triangle 16 2]

-- Cycle fingerprint 9ea40b52308d1d2757e179369f0326160c990ac1b5a5d0fc3723772a94ef65be.
def localCycle00118 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 3, .distance 2 5, .distance 5 6, .distance 4 6, .distance 0 4, .distance 4 5, .theta 4]
    constant := ![3, -1, 0, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 0, .triangle 26 2, .triangle 30 0, .triangle 34 2, .triangle 13 0, .triangle 12 0, .corridorLower 4 5]

-- Cycle fingerprint a0289adce31cf7dec560f66d83f75a0b0a245c4a0ffa9433510667a8728ce86a.
def localCycle00119 : Cycle where
  length := 10
  data := {
    node := ![.theta 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 3 6, .distance 3 4, .distance 1 3, .distance 1 2, .distance 0 1, .theta 1]
    constant := ![0, 0, 0, 3, -1, 0, -1, 0, -2, -2]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![true, false, false, false, false, true, false, false, false, false] }
  origin := ![.thetaNext 0, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 27 0, .triangle 32 1, .triangle 19 0, .gapLower 1 2, .gapLower 1 1, .gapLower 1 0]

-- Cycle fingerprint a0b053d72131ceb7ca428d3a248e006683442f092f51243a17f55ec802db1b73.
def localCycle00120 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .theta 1, .distance 1 3, .distance 1 6, .distance 1 4, .distance 0 4, .distance 4 5, .theta 4, .theta 3, .theta 2]
    constant := ![0, 2, 0, -2, 0, -1, -1, 0, 0]
    coefficient := ![0, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![true, false, true, false, true, false, false, true, true] }
  origin := ![.thetaNext 1, .gapLower 1 6, .triangle 21 2, .gapLower 1 4, .triangle 2 2, .triangle 12 0, .corridorLower 4 5, .thetaNext 3, .thetaNext 2]

-- Cycle fingerprint a20a249ee47e837583c628d09b65d4a629abe41830cdadda379036b1f74228cd.
def localCycle00121 : Cycle where
  length := 11
  data := {
    node := ![.theta 0, .zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 1 3, .distance 1 4, .distance 1 5, .distance 1 2, .distance 0 1, .theta 0]
    constant := ![0, 0, 3, 0, 0, -1, -2, 0, -2, -1, -1]
    coefficient := ![0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false, false, true, false, false, false] }
  origin := ![.thetaLower 0, .thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 21 0, .gapLower 1 4, .triangle 22 2, .gapLower 1 2, .triangle 0 0, .corridorLower 0 1]

-- Cycle fingerprint a3140abd7817e2da4c8f910bec82db01ea786180dccb7cc9962c41d286ce448f.
def localCycle00122 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 3, .distance 2 3, .distance 3 6, .distance 3 4, .distance 1 4, .distance 1 5, .distance 1 3, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, -1, 0, 0, 0, -2, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true, false, false, false, false] }
  origin := ![.thetaUpper 3, .corridorUpper 2 3, .triangle 27 0, .triangle 32 1, .gapLower 4 3, .triangle 22 2, .gapLower 1 3, .triangle 1 0, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint a588e130ebdd5e1ddba05ca693afe4aa3909c4ae91b438ce9ec3cf3b30fcc524.
def localCycle00123 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 4, .distance 2 3, .distance 2 5, .distance 1 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, -1, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, false, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 0, .triangle 25 0, .triangle 26 2, .triangle 17 0, .triangle 0 0, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint a84cb2e430f5ed1f2b47c1704d9357e7b15e2b664c68d105225905c9991d0573.
def localCycle00124 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 2, .distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 3 6, .distance 3 4, .distance 1 4, .distance 1 5, .distance 1 2]
    constant := ![-2, -1, 0, 0, 3, -1, 0, 0, -2, 0]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, true, false, true] }
  origin := ![.gapLower 1 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 27 0, .triangle 32 1, .triangle 19 2, .gapLower 1 4, .triangle 17 1]

-- Cycle fingerprint ab6e4c2274aac93b56f152633829cbb9f2968dbaca316e6065c8fea117388a90.
def localCycle00125 : Cycle where
  length := 13
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 1 2, .distance 2 4, .distance 2 3, .distance 3 6, .distance 0 3, .distance 0 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, 0, -1, -1, 0, -1, -1, 0, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, true, false, false, true, true, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 17 0, .triangle 16 0, .triangle 25 1, .triangle 27 0, .triangle 11 0, .triangle 5 1, .triangle 0 1, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint ab9b3db30ff53487a34bdd68c6a0d0328992dcb7b8571c41a5d066ab2beaa3a8.
def localCycle00126 : Cycle where
  length := 9
  data := {
    node := ![.distance 3 4, .distance 1 3, .distance 1 2, .distance 0 1, .theta 1, .zero, .theta 3, .distance 2 3, .distance 3 6, .distance 3 4]
    constant := ![-1, -2, -1, -2, 0, 0, 3, -1, 0]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, false, false, false, false, false, true] }
  origin := ![.triangle 19 0, .gapLower 1 2, .triangle 0 0, .gapLower 1 0, .thetaLower 1, .thetaUpper 3, .corridorUpper 2 3, .triangle 27 0, .triangle 32 1]

-- Cycle fingerprint aba4dec62cbf002ad99eaf7ff380faf3ddfce8a043c48b55eee8bf206429a3da.
def localCycle00127 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 3, .distance 3 4, .distance 3 5, .distance 0 3, .distance 0 2, .distance 0 1, .theta 0, .zero, .theta 1, .distance 1 6, .distance 1 3]
    constant := ![-1, 0, -1, 0, 0, -1, 0, 0, 2, -2]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![false, true, false, false, true, false, false, false, false, false] }
  origin := ![.triangle 19 0, .triangle 31 2, .triangle 10 0, .gapLower 0 2, .triangle 0 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 1, .gapLower 1 6, .gapLower 1 5]

-- Cycle fingerprint b0746369f46b1f811b26c199f46d782217d4f5ba0c30f114860efe6913bd9b67.
def localCycle00128 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 3 5, .distance 5 6, .distance 2 6, .distance 1 6, .distance 4 6, .distance 0 4, .distance 4 5, .theta 4]
    constant := ![3, 0, -1, 0, 0, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, true, true, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 31 2, .triangle 33 0, .triangle 30 2, .triangle 18 2, .triangle 23 1, .triangle 13 0, .triangle 12 0, .corridorLower 4 5]

-- Cycle fingerprint b09bc96bb6ceae67d0883c761191b4ddcb349e68bb620a7d76627f99d51463de.
def localCycle00129 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 3 5, .distance 2 5, .distance 1 2, .distance 2 3, .distance 0 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, -1, 0, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, true, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 33 0, .triangle 26 2, .triangle 17 0, .triangle 15 0, .triangle 5 0, .triangle 0 1, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint b13192062db68e4f0afd8f6e7e2c5b06b3ebb774879ba6a317b27d129c8a0ab3.
def localCycle00130 : Cycle where
  length := 10
  data := {
    node := ![.theta 3, .distance 2 3, .distance 2 4, .distance 2 5, .distance 5 6, .distance 4 6, .distance 3 4, .distance 0 4, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, 0, 0, -1, 0, -1, 0, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, true, false, false, true] }
  origin := ![.corridorUpper 2 3, .triangle 25 2, .triangle 28 2, .triangle 30 0, .triangle 34 2, .triangle 32 0, .triangle 9 2, .triangle 12 0, .corridorLower 4 5, .thetaNext 3]

-- Cycle fingerprint b15e76d864290fd7cf4dc9e0a9b309b3ee1e60cc9d3976f18128b0cf55a2f9a3.
def localCycle00131 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 4, .distance 1 3, .distance 3 6, .distance 0 3, .distance 0 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, -1, -1, -1, -1, 0, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, true, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 0, .triangle 19 0, .triangle 21 0, .triangle 11 0, .triangle 5 1, .triangle 0 1, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint b3e6fdbe2bbc2bb521154ac6f2bfddaef3101eef95c050f72467a8b3d4bca03f.
def localCycle00132 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 6, .distance 3 4, .distance 1 4, .distance 1 5, .distance 0 5, .distance 0 3, .theta 3]
    constant := ![3, -1, 0, 0, -3, 0, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, true, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 27 0, .triangle 32 1, .triangle 19 2, .gapLower 1 4, .triangle 3 2, .triangle 10 1, .gapLower 3 0]

-- Cycle fingerprint b464592f2c9f6688abde1e561f15edac777317bcd9f37e3dbcc6f457e615a1a9.
def localCycle00133 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 2, .distance 0 1, .theta 0, .zero, .theta 6, .distance 5 6, .distance 4 6, .distance 1 4, .distance 1 5, .distance 1 2]
    constant := ![-1, -1, 0, 0, 3, 0, -1, 0, -2]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, true, false] }
  origin := ![.triangle 0 0, .corridorLower 0 1, .thetaLower 0, .thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 23 0, .triangle 22 2, .gapLower 1 2]

-- Cycle fingerprint b5f6b4461ca4055e7705988327d92280c3023bcd6010d35ee15e8a44e57ae5a3.
def localCycle00134 : Cycle where
  length := 3
  data := {
    node := ![.distance 0 1, .theta 1, .distance 1 6, .distance 0 1]
    constant := ![-2, 2, -1]
    coefficient := ![0, 1, 0]
    strict := ![false, false, false] }
  origin := ![.gapLower 1 0, .gapLower 1 6, .triangle 4 0]

-- Cycle fingerprint b7fee979524574f43dcf811a7f4b56c7c864b32cef1aaf3aa03f2ef82908011a.
def localCycle00135 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .theta 1, .distance 1 3, .distance 1 6, .distance 0 6, .distance 0 4, .distance 4 5, .theta 4, .theta 3, .theta 2]
    constant := ![0, 2, -2, 0, 0, -1, -1, 0, 0]
    coefficient := ![0, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![true, false, false, true, true, false, false, true, true] }
  origin := ![.thetaNext 1, .gapLower 1 6, .gapLower 1 5, .triangle 4 2, .triangle 13 1, .triangle 12 0, .corridorLower 4 5, .thetaNext 3, .thetaNext 2]

-- Cycle fingerprint b89b1dc65cc43ced18841e295e4e6e1e56e3ce07ef673d00ea7049837e58800d.
def localCycle00136 : Cycle where
  length := 9
  data := {
    node := ![.distance 3 4, .distance 1 3, .distance 1 2, .distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 3 6, .distance 3 4]
    constant := ![-1, -2, -2, -1, 0, 0, 3, -1, 0]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, false, false, false, false, false, true] }
  origin := ![.triangle 19 0, .gapLower 1 2, .gapLower 1 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 27 0, .triangle 32 1]

-- Cycle fingerprint b9fcd7856be30af5bf2db02fb8e635a27b99c1b91dca5e426c1466599d5c9408.
def localCycle00137 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 3 4, .distance 3 5, .distance 5 6, .distance 4 6, .distance 0 4, .distance 4 5, .theta 4]
    constant := ![3, 0, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 31 2, .triangle 33 0, .triangle 34 2, .triangle 13 0, .triangle 12 0, .corridorLower 4 5]

-- Cycle fingerprint bbd39cc5d8f88b8395c699f46c3f7a8f271a2704e5d83ec925e1c8cd3baa3a41.
def localCycle00138 : Cycle where
  length := 4
  data := {
    node := ![.distance 2 5, .distance 3 5, .distance 1 3, .distance 1 2, .distance 2 5]
    constant := ![0, -1, -2, 2]
    coefficient := ![0, 0, 0, 0]
    strict := ![false, false, false, true] }
  origin := ![.gapLower 5 4, .triangle 20 0, .gapLower 1 2, .gapUpper 2 2]

-- Cycle fingerprint bc4ce61628607b953dc3fc7671d80050093d89607d0809d6d4121c37a7d1a8af.
def localCycle00139 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 4, .distance 1 5, .distance 1 2, .distance 0 1, .theta 0, .zero, .theta 6, .distance 5 6, .distance 4 6, .distance 1 4]
    constant := ![0, -2, -2, -1, 0, 0, 3, 0, -1]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![true, false, false, false, false, false, false, true, false] }
  origin := ![.triangle 22 2, .gapLower 1 2, .gapLower 1 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 23 0]

-- Cycle fingerprint c01afb07aa35b287026f5a3945cf6a1f785165c4886127aff655c2900dc5efdb.
def localCycle00140 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 5, .distance 1 2, .distance 0 1, .theta 1, .zero, .theta 6, .distance 5 6, .distance 1 5]
    constant := ![-2, -1, -2, 0, 0, 3, -1]
    coefficient := ![0, 0, 0, 0, 1, 1, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 1 2, .triangle 0 0, .gapLower 1 0, .thetaLower 1, .thetaUpper 6, .corridorUpper 5 6, .triangle 24 0]

-- Cycle fingerprint c3ae41357667c62c5beffdf56fba555c5faf547f45d97a40a2c9c5047ad22574.
def localCycle00141 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 2 3, .distance 3 5, .distance 1 3, .distance 1 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, -1, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 25 0, .triangle 26 0, .triangle 20 0, .triangle 15 1, .triangle 0 0, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint c5d509549fb48adb0c4894af5b2df9a75c684f9365924eb85f3c99c204f3c11f.
def localCycle00142 : Cycle where
  length := 10
  data := {
    node := ![.theta 2, .distance 1 2, .distance 2 4, .distance 4 5, .distance 0 4, .distance 4 6, .distance 5 6, .theta 5, .theta 4, .theta 3, .theta 2]
    constant := ![3, -1, -1, -1, -1, 0, -1, 0, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, true, true, true] }
  origin := ![.corridorUpper 1 2, .triangle 16 0, .triangle 28 0, .triangle 12 0, .triangle 13 0, .triangle 34 1, .corridorLower 5 6, .thetaNext 4, .thetaNext 3, .thetaNext 2]

-- Cycle fingerprint c7caca8621e6d63f681d239a48c41132dbd4cb3da6621e9e064592e2edcf645c.
def localCycle00143 : Cycle where
  length := 11
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 3, .distance 2 5, .distance 1 2, .distance 2 6, .distance 5 6, .distance 3 6, .distance 4 6, .distance 0 4, .distance 4 5, .theta 4]
    constant := ![3, -1, 0, -1, -1, 0, 0, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, true, true, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 0, .triangle 26 2, .triangle 17 0, .triangle 18 0, .triangle 30 1, .triangle 33 2, .triangle 32 1, .triangle 13 0, .triangle 12 0, .corridorLower 4 5]

-- Cycle fingerprint c92291c805e47eb266126a768eeec92b633e2775103f1a4de980543141a8cdc3.
def localCycle00144 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 2, .distance 0 1, .theta 1, .theta 0, .zero, .theta 6, .distance 5 6, .distance 4 6, .distance 2 4, .distance 1 2]
    constant := ![-1, -3, 0, 0, 0, 3, 0, -1, -1]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, true, false, false, false, true, false, false] }
  origin := ![.triangle 0 0, .gapLower 1 0, .thetaNext 0, .thetaLower 0, .thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 29 0, .triangle 16 0]

-- Cycle fingerprint cb3a12bf9ef078c3e889b761e5055a1ecfddb176ac7980e9683218e5fdfa4852.
def localCycle00145 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 5, .distance 1 2, .distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 1 3, .distance 1 6, .distance 1 4, .distance 1 5]
    constant := ![-2, -1, -1, 0, 0, 3, 0, 0, -2, 0]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, true, false, true] }
  origin := ![.gapLower 1 2, .triangle 0 0, .corridorLower 0 1, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 15 2, .triangle 21 2, .gapLower 1 4, .triangle 22 2]

-- Cycle fingerprint cbeebf1aedf5dff1687da611773dcf7b2b6c711d7e3b74555bed9460c9062ef2.
def localCycle00146 : Cycle where
  length := 7
  data := {
    node := ![.theta 1, .distance 1 3, .distance 3 6, .distance 3 4, .distance 0 3, .distance 0 2, .distance 0 1, .theta 1]
    constant := ![2, -1, 0, -1, 0, 0, -2]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, false] }
  origin := ![.gapLower 1 6, .triangle 21 0, .triangle 32 1, .triangle 9 0, .gapLower 0 2, .triangle 0 1, .gapLower 1 0]

-- Cycle fingerprint cd4439b57fdcb2fc73fe26f149c3dc4be4c21689e5bbcb307425f630a6be1a4c.
def localCycle00147 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 6, .distance 1 3, .distance 3 4, .distance 0 4, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, -1, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, true] }
  origin := ![.corridorUpper 2 3, .triangle 27 0, .triangle 21 0, .triangle 19 0, .triangle 9 2, .triangle 12 0, .corridorLower 4 5, .thetaNext 3]

-- Cycle fingerprint cd6901e6e20a1a326a2f1363533b00cf33be0e2dd4712fa304946b8764220804.
def localCycle00148 : Cycle where
  length := 14
  data := {
    node := ![.distance 1 6, .distance 1 3, .distance 3 4, .distance 3 5, .distance 0 3, .distance 0 2, .distance 0 1, .theta 1, .zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 2 6, .distance 1 6]
    constant := ![-2, -1, 0, -1, 0, 0, -2, 0, 0, 3, 0, 0, 0, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, false, false, false, false, true, true, true, true] }
  origin := ![.gapLower 1 5, .triangle 19 0, .triangle 31 2, .triangle 10 0, .gapLower 0 2, .triangle 0 1, .gapLower 1 0, .thetaLower 1, .thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 27 2, .triangle 18 2]

-- Cycle fingerprint ced45d7b9294e080a523ca9fb42432595b9ecfdec28509decb5a192cfa09fc36.
def localCycle00149 : Cycle where
  length := 10
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 4, .distance 3 5, .distance 5 6, .distance 4 6, .distance 1 4, .distance 0 4, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, -1, 0, -1, 0, -1, 0, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, true, false, false, true] }
  origin := ![.corridorUpper 2 3, .triangle 25 0, .triangle 31 2, .triangle 33 0, .triangle 34 2, .triangle 23 0, .triangle 2 2, .triangle 12 0, .corridorLower 4 5, .thetaNext 3]

-- Cycle fingerprint d1c4b01732f7ba71383d0c47619e73e98794cb6410fa019b6770622046c00d32.
def localCycle00150 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 2, .distance 0 1, .theta 0, .zero, .theta 6, .distance 5 6, .distance 4 6, .distance 2 4, .distance 1 4, .distance 1 5, .distance 1 2]
    constant := ![-2, -1, 0, 0, 3, 0, -1, 0, -2, 0]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, true, false, true] }
  origin := ![.gapLower 1 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 29 0, .triangle 16 2, .gapLower 1 3, .triangle 17 1]

-- Cycle fingerprint d2b52bfb812bab67ba644b3e9f2fb2aed407bd069c76d4eb59c0e1ce6ec6202b.
def localCycle00151 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 5, .distance 1 3, .distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 3 6, .distance 1 6, .distance 1 4, .distance 1 5]
    constant := ![-2, -1, -1, 0, 0, 3, -1, 0, -2, 0]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false, false, true] }
  origin := ![.gapLower 1 3, .triangle 1 0, .corridorLower 0 1, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 27 0, .gapLower 6 2, .gapLower 1 5, .triangle 22 2]

-- Cycle fingerprint d450811db7272852f8c84489cc38392f38a5fc96f9437df75e2a1e3baa01e93a.
def localCycle00152 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 4, .distance 1 3, .distance 3 6, .distance 4 6, .distance 0 4, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, -1, -1, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, false, true] }
  origin := ![.corridorUpper 2 3, .triangle 25 0, .triangle 19 0, .triangle 21 0, .triangle 32 1, .triangle 13 0, .triangle 12 0, .corridorLower 4 5, .thetaNext 3]

-- Cycle fingerprint d75e2cb1eb959f22a4d66dd85805756811707942f5d236066f13ccb714fe80b2.
def localCycle00153 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 4, .distance 4 6, .distance 1 4, .distance 0 4, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, -1, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, true] }
  origin := ![.corridorUpper 2 3, .triangle 25 0, .triangle 32 0, .triangle 23 0, .triangle 2 2, .triangle 12 0, .corridorLower 4 5, .thetaNext 3]

-- Cycle fingerprint dab56ab642fc668c50eb9a08c375bfc9119da5e5e72b7ef93a05eb10fe05db19.
def localCycle00154 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 1 3, .distance 3 6, .distance 2 6, .distance 5 6, .distance 4 6, .distance 0 4, .distance 4 5, .theta 4]
    constant := ![3, -1, -1, 0, 0, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, true, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 19 0, .triangle 21 0, .triangle 27 2, .triangle 30 1, .triangle 34 2, .triangle 13 0, .triangle 12 0, .corridorLower 4 5]

-- Cycle fingerprint dc68496056b7966e9d23a2012c90cfbd13efa080d128fa97f24881739028c4e9.
def localCycle00155 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 3 5, .distance 5 6, .distance 4 6, .distance 1 4, .distance 0 4, .distance 4 5, .theta 4]
    constant := ![3, 0, -1, 0, -1, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, true, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 31 2, .triangle 33 0, .triangle 34 2, .triangle 23 0, .triangle 2 2, .triangle 12 0, .corridorLower 4 5]

-- Cycle fingerprint dccefcbebe1ee2bfb84e2ae23d56a875a88f8fb08a54066f21ce077b449d6306.
def localCycle00156 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 4 6, .distance 1 4, .distance 1 3, .distance 3 5, .distance 0 5, .distance 4 5, .theta 4]
    constant := ![3, 0, -1, -1, 0, -1, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, false, true, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 29 0, .triangle 23 0, .triangle 19 1, .triangle 20 0, .triangle 10 2, .triangle 12 1, .corridorLower 4 5]

-- Cycle fingerprint dce26f9a47490dd71b0b7d5fe8f06546009c26be8b9e0b6cd478d3b41286a08a.
def localCycle00157 : Cycle where
  length := 9
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 1 2, .distance 2 3, .distance 3 4, .distance 4 6, .distance 5 6, .theta 5]
    constant := ![3, 0, 0, -1, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, false, false, true, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 17 0, .triangle 15 0, .triangle 25 0, .triangle 32 0, .triangle 34 1, .corridorLower 5 6]

-- Cycle fingerprint e244b74d427637f9fd1fb2780b35aa72209a3f91924b45ae092fa92884b88ecd.
def localCycle00158 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 2 4, .distance 1 2, .distance 2 3, .distance 0 2, .theta 0, .zero]
    constant := ![0, 3, 0, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 29 0, .triangle 16 0, .triangle 15 0, .triangle 5 0, .corridorLower 0 2, .thetaLower 0]

-- Cycle fingerprint e3899075cb714a78cdeae14acb77d057b707856b6eea2d7da17f6905e9ebcbd2.
def localCycle00159 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 3, .distance 3 6, .distance 4 6, .distance 0 4, .distance 4 5, .theta 4]
    constant := ![3, -1, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 0, .triangle 27 0, .triangle 32 1, .triangle 13 0, .triangle 12 0, .corridorLower 4 5]

-- Cycle fingerprint e4efb53cd60ef0bb28f9cb51eaa2cd980251388b1b2ac2948284eb9bc666f518.
def localCycle00160 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 1 3, .distance 3 4, .distance 2 3, .distance 3 5, .distance 4 5, .distance 0 4, .distance 4 6, .theta 4, .theta 3]
    constant := ![3, -1, -1, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, false, true] }
  origin := ![.corridorUpper 1 3, .triangle 19 0, .triangle 25 0, .triangle 26 0, .triangle 31 1, .triangle 12 0, .triangle 13 0, .corridorLower 4 6, .thetaNext 3]

-- Cycle fingerprint e5b377f9776cb84f16b5904cc88165dfcc32d114d825a653c5ebed61189d4478.
def localCycle00161 : Cycle where
  length := 3
  data := {
    node := ![.distance 3 6, .distance 1 3, .distance 1 6, .distance 3 6]
    constant := ![2, -3, 0]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.gapUpper 3 4, .gapLower 1 5, .triangle 21 1]

-- Cycle fingerprint e93eefdb27fceac5e8a7097466126a4a45052af1577000665c17b21cece10524.
def localCycle00162 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .theta 3, .distance 2 3, .distance 1 3, .distance 1 6, .distance 1 4, .distance 0 4, .distance 4 5, .theta 4]
    constant := ![0, 3, 0, 0, -3, 0, -1, -1]
    coefficient := ![0, 1, 0, 0, 0, 0, 0, 0]
    strict := ![true, false, true, true, false, true, false, false] }
  origin := ![.thetaNext 3, .corridorUpper 2 3, .triangle 15 2, .triangle 21 2, .gapLower 1 4, .triangle 2 2, .triangle 12 0, .corridorLower 4 5]

-- Cycle fingerprint ea6c83cbbeb2162100c3d747bc32b864ba5e1edabda59a30354cdbe718907a9a.
def localCycle00163 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 3, .distance 1 2, .distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 3 6, .distance 1 6, .distance 1 4, .distance 1 3]
    constant := ![-2, -1, -1, 0, 0, 3, -1, 0, -2, 0]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false, false, true] }
  origin := ![.gapLower 1 2, .triangle 0 0, .corridorLower 0 1, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 27 0, .gapLower 6 2, .gapLower 1 5, .triangle 19 1]

-- Cycle fingerprint ec6a395f1194898bf1c72e81a4c47f8917e068df91497bbe36e3b3f5a8c5f66c.
def localCycle00164 : Cycle where
  length := 6
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 4 6, .distance 0 4, .distance 4 5, .theta 4]
    constant := ![3, 0, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 29 0, .triangle 13 0, .triangle 12 0, .corridorLower 4 5]

-- Cycle fingerprint ee6c5d9e274808f2938c4fc39720a0ff105e78daf937c7c44c3c5d97f4f4bc51.
def localCycle00165 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 2 4, .distance 2 5, .distance 5 6, .distance 4 6, .distance 0 4, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, 0, 0, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, false, false, true] }
  origin := ![.corridorUpper 2 3, .triangle 25 2, .triangle 28 2, .triangle 30 0, .triangle 34 2, .triangle 13 0, .triangle 12 0, .corridorLower 4 5, .thetaNext 3]

-- Cycle fingerprint eeae81c34cc2ea2b5b8beb37542721114255d1d599a4b07170538db175d7a9c8.
def localCycle00166 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 2 5, .distance 5 6, .distance 4 6, .distance 0 4, .distance 4 5, .theta 4]
    constant := ![3, 0, 0, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 28 2, .triangle 30 0, .triangle 34 2, .triangle 13 0, .triangle 12 0, .corridorLower 4 5]

-- Cycle fingerprint eeeb6302e9d8ca5491df1132d9672fff2afdb81749ab0ce8af58a72d37b57212.
def localCycle00167 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 3, .distance 1 6, .distance 1 4, .distance 1 2, .distance 0 1, .theta 1, .zero, .theta 3, .distance 2 3, .distance 1 3]
    constant := ![0, -2, 0, -1, -2, 0, 0, 3, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![true, false, true, false, false, false, false, false, true] }
  origin := ![.triangle 21 2, .gapLower 1 4, .triangle 16 1, .triangle 0 0, .gapLower 1 0, .thetaLower 1, .thetaUpper 3, .corridorUpper 2 3, .triangle 15 2]

-- Cycle fingerprint f466d3cfaaed64ef5ead9d918275cd71109948a5f9105a3826c2f9c644b82ab8.
def localCycle00168 : Cycle where
  length := 8
  data := {
    node := ![.theta 2, .distance 1 2, .distance 2 3, .distance 3 5, .distance 3 4, .distance 4 6, .theta 4, .theta 3, .theta 2]
    constant := ![3, -1, -1, 0, -1, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, true, true] }
  origin := ![.corridorUpper 1 2, .triangle 15 0, .triangle 26 0, .triangle 31 1, .triangle 32 0, .corridorLower 4 6, .thetaNext 3, .thetaNext 2]

-- Cycle fingerprint f473268168de83901d6e5f8144f7c972b1344a8c73bc610076acd56106a6b4f0.
def localCycle00169 : Cycle where
  length := 8
  data := {
    node := ![.distance 4 5, .theta 4, .theta 3, .theta 2, .theta 1, .distance 1 3, .distance 3 6, .distance 3 4, .distance 4 5]
    constant := ![-1, 0, 0, 0, 1, -1, 0, -1]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![false, true, true, true, false, false, true, false] }
  origin := ![.corridorLower 4 5, .thetaNext 3, .thetaNext 2, .thetaNext 1, .gapLower 1 6, .triangle 21 0, .triangle 32 1, .triangle 31 0]

-- Cycle fingerprint f7426e7ede10dc413047f0b35f4c49ecb00695e45beddd2750ad633b13642d8b.
def localCycle00170 : Cycle where
  length := 8
  data := {
    node := ![.theta 0, .zero, .theta 3, .distance 2 3, .distance 1 3, .distance 1 6, .distance 1 2, .distance 0 1, .theta 0]
    constant := ![0, 0, 3, 0, -2, 0, -2, -1]
    coefficient := ![0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true, false, false] }
  origin := ![.thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 15 2, .gapLower 1 5, .triangle 18 1, .gapLower 1 1, .corridorLower 0 1]

-- Cycle fingerprint fb5b890848b93299bad1078920f10aef944bcfd8c3482c181ea2d64b48c7c1f1.
def localCycle00171 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 1 3, .distance 1 5, .distance 5 6, .distance 4 6, .distance 0 4, .distance 4 5, .theta 4]
    constant := ![3, -1, 0, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 19 0, .triangle 20 2, .triangle 24 0, .triangle 34 2, .triangle 13 0, .triangle 12 0, .corridorLower 4 5]

-- Cycle fingerprint fecd6625ec7f57e80c2a6318520207702a99931e99171f87bfef249857265d69.
def localCycle00172 : Cycle where
  length := 11
  data := {
    node := ![.theta 0, .zero, .theta 3, .distance 2 3, .distance 3 6, .distance 3 4, .distance 1 4, .distance 1 5, .distance 1 3, .distance 1 2, .distance 0 1, .theta 0]
    constant := ![0, 0, 3, -1, 0, 0, -2, 0, -2, -1, -1]
    coefficient := ![0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, true, false, false, false] }
  origin := ![.thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 27 0, .triangle 32 1, .gapLower 4 3, .gapLower 1 4, .triangle 20 1, .gapLower 1 2, .triangle 0 0, .corridorLower 0 1]

def library : Library := fun id => if id < 86 then (if id < 43 then (if id < 21 then (if id < 10 then (if id < 5 then (if id < 2 then (if id < 1 then (if id = 0 then some localCycle00000 else none) else (if id = 1 then some localCycle00001 else none)) else (if id < 3 then (if id = 2 then some localCycle00002 else none) else (if id < 4 then (if id = 3 then some localCycle00003 else none) else (if id = 4 then some localCycle00004 else none)))) else (if id < 7 then (if id < 6 then (if id = 5 then some localCycle00005 else none) else (if id = 6 then some localCycle00006 else none)) else (if id < 8 then (if id = 7 then some localCycle00007 else none) else (if id < 9 then (if id = 8 then some localCycle00008 else none) else (if id = 9 then some localCycle00009 else none))))) else (if id < 15 then (if id < 12 then (if id < 11 then (if id = 10 then some localCycle00010 else none) else (if id = 11 then some localCycle00011 else none)) else (if id < 13 then (if id = 12 then some localCycle00012 else none) else (if id < 14 then (if id = 13 then some localCycle00013 else none) else (if id = 14 then some localCycle00014 else none)))) else (if id < 18 then (if id < 16 then (if id = 15 then some localCycle00015 else none) else (if id < 17 then (if id = 16 then some localCycle00016 else none) else (if id = 17 then some localCycle00017 else none))) else (if id < 19 then (if id = 18 then some localCycle00018 else none) else (if id < 20 then (if id = 19 then some localCycle00019 else none) else (if id = 20 then some localCycle00020 else none)))))) else (if id < 32 then (if id < 26 then (if id < 23 then (if id < 22 then (if id = 21 then some localCycle00021 else none) else (if id = 22 then some localCycle00022 else none)) else (if id < 24 then (if id = 23 then some localCycle00023 else none) else (if id < 25 then (if id = 24 then some localCycle00024 else none) else (if id = 25 then some localCycle00025 else none)))) else (if id < 29 then (if id < 27 then (if id = 26 then some localCycle00026 else none) else (if id < 28 then (if id = 27 then some localCycle00027 else none) else (if id = 28 then some localCycle00028 else none))) else (if id < 30 then (if id = 29 then some localCycle00029 else none) else (if id < 31 then (if id = 30 then some localCycle00030 else none) else (if id = 31 then some localCycle00031 else none))))) else (if id < 37 then (if id < 34 then (if id < 33 then (if id = 32 then some localCycle00032 else none) else (if id = 33 then some localCycle00033 else none)) else (if id < 35 then (if id = 34 then some localCycle00034 else none) else (if id < 36 then (if id = 35 then some localCycle00035 else none) else (if id = 36 then some localCycle00036 else none)))) else (if id < 40 then (if id < 38 then (if id = 37 then some localCycle00037 else none) else (if id < 39 then (if id = 38 then some localCycle00038 else none) else (if id = 39 then some localCycle00039 else none))) else (if id < 41 then (if id = 40 then some localCycle00040 else none) else (if id < 42 then (if id = 41 then some localCycle00041 else none) else (if id = 42 then some localCycle00042 else none))))))) else (if id < 64 then (if id < 53 then (if id < 48 then (if id < 45 then (if id < 44 then (if id = 43 then some localCycle00043 else none) else (if id = 44 then some localCycle00044 else none)) else (if id < 46 then (if id = 45 then some localCycle00045 else none) else (if id < 47 then (if id = 46 then some localCycle00046 else none) else (if id = 47 then some localCycle00047 else none)))) else (if id < 50 then (if id < 49 then (if id = 48 then some localCycle00048 else none) else (if id = 49 then some localCycle00049 else none)) else (if id < 51 then (if id = 50 then some localCycle00050 else none) else (if id < 52 then (if id = 51 then some localCycle00051 else none) else (if id = 52 then some localCycle00052 else none))))) else (if id < 58 then (if id < 55 then (if id < 54 then (if id = 53 then some localCycle00053 else none) else (if id = 54 then some localCycle00054 else none)) else (if id < 56 then (if id = 55 then some localCycle00055 else none) else (if id < 57 then (if id = 56 then some localCycle00056 else none) else (if id = 57 then some localCycle00057 else none)))) else (if id < 61 then (if id < 59 then (if id = 58 then some localCycle00058 else none) else (if id < 60 then (if id = 59 then some localCycle00059 else none) else (if id = 60 then some localCycle00060 else none))) else (if id < 62 then (if id = 61 then some localCycle00061 else none) else (if id < 63 then (if id = 62 then some localCycle00062 else none) else (if id = 63 then some localCycle00063 else none)))))) else (if id < 75 then (if id < 69 then (if id < 66 then (if id < 65 then (if id = 64 then some localCycle00064 else none) else (if id = 65 then some localCycle00065 else none)) else (if id < 67 then (if id = 66 then some localCycle00066 else none) else (if id < 68 then (if id = 67 then some localCycle00067 else none) else (if id = 68 then some localCycle00068 else none)))) else (if id < 72 then (if id < 70 then (if id = 69 then some localCycle00069 else none) else (if id < 71 then (if id = 70 then some localCycle00070 else none) else (if id = 71 then some localCycle00071 else none))) else (if id < 73 then (if id = 72 then some localCycle00072 else none) else (if id < 74 then (if id = 73 then some localCycle00073 else none) else (if id = 74 then some localCycle00074 else none))))) else (if id < 80 then (if id < 77 then (if id < 76 then (if id = 75 then some localCycle00075 else none) else (if id = 76 then some localCycle00076 else none)) else (if id < 78 then (if id = 77 then some localCycle00077 else none) else (if id < 79 then (if id = 78 then some localCycle00078 else none) else (if id = 79 then some localCycle00079 else none)))) else (if id < 83 then (if id < 81 then (if id = 80 then some localCycle00080 else none) else (if id < 82 then (if id = 81 then some localCycle00081 else none) else (if id = 82 then some localCycle00082 else none))) else (if id < 84 then (if id = 83 then some localCycle00083 else none) else (if id < 85 then (if id = 84 then some localCycle00084 else none) else (if id = 85 then some localCycle00085 else none)))))))) else (if id < 129 then (if id < 107 then (if id < 96 then (if id < 91 then (if id < 88 then (if id < 87 then (if id = 86 then some localCycle00086 else none) else (if id = 87 then some localCycle00087 else none)) else (if id < 89 then (if id = 88 then some localCycle00088 else none) else (if id < 90 then (if id = 89 then some localCycle00089 else none) else (if id = 90 then some localCycle00090 else none)))) else (if id < 93 then (if id < 92 then (if id = 91 then some localCycle00091 else none) else (if id = 92 then some localCycle00092 else none)) else (if id < 94 then (if id = 93 then some localCycle00093 else none) else (if id < 95 then (if id = 94 then some localCycle00094 else none) else (if id = 95 then some localCycle00095 else none))))) else (if id < 101 then (if id < 98 then (if id < 97 then (if id = 96 then some localCycle00096 else none) else (if id = 97 then some localCycle00097 else none)) else (if id < 99 then (if id = 98 then some localCycle00098 else none) else (if id < 100 then (if id = 99 then some localCycle00099 else none) else (if id = 100 then some localCycle00100 else none)))) else (if id < 104 then (if id < 102 then (if id = 101 then some localCycle00101 else none) else (if id < 103 then (if id = 102 then some localCycle00102 else none) else (if id = 103 then some localCycle00103 else none))) else (if id < 105 then (if id = 104 then some localCycle00104 else none) else (if id < 106 then (if id = 105 then some localCycle00105 else none) else (if id = 106 then some localCycle00106 else none)))))) else (if id < 118 then (if id < 112 then (if id < 109 then (if id < 108 then (if id = 107 then some localCycle00107 else none) else (if id = 108 then some localCycle00108 else none)) else (if id < 110 then (if id = 109 then some localCycle00109 else none) else (if id < 111 then (if id = 110 then some localCycle00110 else none) else (if id = 111 then some localCycle00111 else none)))) else (if id < 115 then (if id < 113 then (if id = 112 then some localCycle00112 else none) else (if id < 114 then (if id = 113 then some localCycle00113 else none) else (if id = 114 then some localCycle00114 else none))) else (if id < 116 then (if id = 115 then some localCycle00115 else none) else (if id < 117 then (if id = 116 then some localCycle00116 else none) else (if id = 117 then some localCycle00117 else none))))) else (if id < 123 then (if id < 120 then (if id < 119 then (if id = 118 then some localCycle00118 else none) else (if id = 119 then some localCycle00119 else none)) else (if id < 121 then (if id = 120 then some localCycle00120 else none) else (if id < 122 then (if id = 121 then some localCycle00121 else none) else (if id = 122 then some localCycle00122 else none)))) else (if id < 126 then (if id < 124 then (if id = 123 then some localCycle00123 else none) else (if id < 125 then (if id = 124 then some localCycle00124 else none) else (if id = 125 then some localCycle00125 else none))) else (if id < 127 then (if id = 126 then some localCycle00126 else none) else (if id < 128 then (if id = 127 then some localCycle00127 else none) else (if id = 128 then some localCycle00128 else none))))))) else (if id < 151 then (if id < 140 then (if id < 134 then (if id < 131 then (if id < 130 then (if id = 129 then some localCycle00129 else none) else (if id = 130 then some localCycle00130 else none)) else (if id < 132 then (if id = 131 then some localCycle00131 else none) else (if id < 133 then (if id = 132 then some localCycle00132 else none) else (if id = 133 then some localCycle00133 else none)))) else (if id < 137 then (if id < 135 then (if id = 134 then some localCycle00134 else none) else (if id < 136 then (if id = 135 then some localCycle00135 else none) else (if id = 136 then some localCycle00136 else none))) else (if id < 138 then (if id = 137 then some localCycle00137 else none) else (if id < 139 then (if id = 138 then some localCycle00138 else none) else (if id = 139 then some localCycle00139 else none))))) else (if id < 145 then (if id < 142 then (if id < 141 then (if id = 140 then some localCycle00140 else none) else (if id = 141 then some localCycle00141 else none)) else (if id < 143 then (if id = 142 then some localCycle00142 else none) else (if id < 144 then (if id = 143 then some localCycle00143 else none) else (if id = 144 then some localCycle00144 else none)))) else (if id < 148 then (if id < 146 then (if id = 145 then some localCycle00145 else none) else (if id < 147 then (if id = 146 then some localCycle00146 else none) else (if id = 147 then some localCycle00147 else none))) else (if id < 149 then (if id = 148 then some localCycle00148 else none) else (if id < 150 then (if id = 149 then some localCycle00149 else none) else (if id = 150 then some localCycle00150 else none)))))) else (if id < 162 then (if id < 156 then (if id < 153 then (if id < 152 then (if id = 151 then some localCycle00151 else none) else (if id = 152 then some localCycle00152 else none)) else (if id < 154 then (if id = 153 then some localCycle00153 else none) else (if id < 155 then (if id = 154 then some localCycle00154 else none) else (if id = 155 then some localCycle00155 else none)))) else (if id < 159 then (if id < 157 then (if id = 156 then some localCycle00156 else none) else (if id < 158 then (if id = 157 then some localCycle00157 else none) else (if id = 158 then some localCycle00158 else none))) else (if id < 160 then (if id = 159 then some localCycle00159 else none) else (if id < 161 then (if id = 160 then some localCycle00160 else none) else (if id = 161 then some localCycle00161 else none))))) else (if id < 167 then (if id < 164 then (if id < 163 then (if id = 162 then some localCycle00162 else none) else (if id = 163 then some localCycle00163 else none)) else (if id < 165 then (if id = 164 then some localCycle00164 else none) else (if id < 166 then (if id = 165 then some localCycle00165 else none) else (if id = 166 then some localCycle00166 else none)))) else (if id < 170 then (if id < 168 then (if id = 167 then some localCycle00167 else none) else (if id < 169 then (if id = 168 then some localCycle00168 else none) else (if id = 169 then some localCycle00169 else none))) else (if id < 171 then (if id = 170 then some localCycle00170 else none) else (if id < 172 then (if id = 171 then some localCycle00171 else none) else (if id = 172 then some localCycle00172 else none))))))))

def namedLeaf000 : LeafData := { rows := ![![1, 2, 3, 6, 4, 5], ![0, 6, 3, 2, 5, 4], ![0, 6, 3, 1, 5, 4], ![0, 6, 2, 1, 5, 4], ![6, 0, 5, 1, 2, 3], ![6, 0, 4, 1, 2, 3], ![5, 4, 0, 3, 2, 1]], proof := .tail 9 }

theorem namedLeaf000_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1280)) namedLeaf000 = true :=
  by decide +kernel

def namedLeaf001 : LeafData := { rows := ![![1, 2, 3, 6, 4, 5], ![0, 6, 3, 5, 2, 4], ![0, 6, 3, 5, 1, 4], ![0, 6, 2, 1, 5, 4], ![6, 0, 5, 1, 2, 3], ![6, 0, 4, 2, 1, 3], ![5, 4, 0, 3, 2, 1]], proof := .tail 52 }

theorem namedLeaf001_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1281)) namedLeaf001 = true :=
  by decide +kernel

def namedLeaf002 : LeafData := { rows := ![![1, 2, 3, 6, 4, 5], ![0, 6, 5, 3, 2, 4], ![0, 6, 3, 5, 1, 4], ![0, 6, 2, 5, 1, 4], ![6, 0, 5, 1, 2, 3], ![6, 0, 4, 2, 3, 1], ![5, 4, 0, 3, 2, 1]], proof := .tail 82 }

theorem namedLeaf002_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1282)) namedLeaf002 = true :=
  by decide +kernel

def namedLeaf003 : LeafData := { rows := ![![1, 2, 3, 6, 4, 5], ![0, 6, 5, 3, 2, 4], ![0, 6, 5, 3, 1, 4], ![0, 6, 5, 2, 1, 4], ![6, 0, 5, 1, 2, 3], ![6, 0, 4, 3, 2, 1], ![5, 4, 0, 3, 2, 1]], proof := .tail 14 }

theorem namedLeaf003_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1283)) namedLeaf003 = true :=
  by decide +kernel

def namedLeaf004 : LeafData := { rows := ![![1, 2, 3, 6, 4, 5], ![0, 6, 3, 4, 2, 5], ![0, 6, 3, 4, 1, 5], ![0, 6, 2, 1, 4, 5], ![6, 0, 2, 1, 3, 5], ![6, 0, 1, 2, 3, 4], ![5, 4, 0, 3, 2, 1]], proof := .tail 125 }

theorem namedLeaf004_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1284)) namedLeaf004 = true :=
  by decide +kernel

def namedLeaf005 : LeafData := { rows := ![![1, 2, 3, 6, 4, 5], ![0, 6, 3, 4, 2, 5], ![0, 6, 3, 4, 1, 5], ![0, 6, 2, 1, 5, 4], ![6, 0, 2, 1, 5, 3], ![6, 0, 1, 2, 4, 3], ![5, 4, 0, 3, 2, 1]], proof := .tail 49 }

theorem namedLeaf005_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1285)) namedLeaf005 = true :=
  by decide +kernel

def namedLeaf006 : LeafData := { rows := ![![1, 2, 3, 6, 4, 5], ![0, 6, 4, 3, 2, 5], ![0, 6, 3, 4, 1, 5], ![0, 6, 2, 4, 1, 5], ![6, 0, 2, 3, 1, 5], ![6, 0, 1, 2, 3, 4], ![5, 4, 0, 3, 2, 1]], proof := .tail 34 }

theorem namedLeaf006_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1286)) namedLeaf006 = true :=
  by decide +kernel

def namedLeaf007 : LeafData := { rows := ![![1, 2, 3, 6, 4, 5], ![0, 6, 4, 3, 2, 5], ![0, 6, 4, 3, 1, 5], ![0, 6, 4, 2, 1, 5], ![6, 0, 3, 2, 1, 5], ![6, 0, 1, 2, 3, 4], ![5, 4, 0, 3, 2, 1]], proof := .tail 157 }

theorem namedLeaf007_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1287)) namedLeaf007 = true :=
  by decide +kernel

def namedLeaf008 : LeafData := { rows := ![![1, 2, 3, 6, 4, 5], ![0, 6, 3, 4, 5, 2], ![0, 6, 3, 4, 5, 1], ![0, 6, 2, 1, 4, 5], ![6, 0, 2, 1, 3, 5], ![6, 0, 2, 1, 3, 4], ![5, 4, 0, 3, 2, 1]], proof := .tail 131 }

theorem namedLeaf008_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1288)) namedLeaf008 = true :=
  by decide +kernel

def namedLeaf009 : LeafData := { rows := ![![1, 2, 3, 6, 4, 5], ![0, 6, 3, 4, 5, 2], ![0, 6, 3, 4, 5, 1], ![0, 6, 2, 1, 5, 4], ![6, 0, 2, 1, 5, 3], ![6, 0, 2, 1, 4, 3], ![5, 4, 0, 3, 2, 1]], proof := .tail 95 }

theorem namedLeaf009_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1289)) namedLeaf009 = true :=
  by decide +kernel

def namedLeaf010 : LeafData := { rows := ![![1, 2, 3, 6, 4, 5], ![0, 6, 3, 5, 4, 2], ![0, 6, 3, 4, 5, 1], ![0, 6, 2, 1, 5, 4], ![6, 0, 2, 5, 1, 3], ![6, 0, 2, 4, 1, 3], ![5, 4, 0, 3, 2, 1]], proof := .tail 69 }

theorem namedLeaf010_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1290)) namedLeaf010 = true :=
  by decide +kernel

def namedLeaf011 : LeafData := { rows := ![![1, 2, 3, 6, 4, 5], ![0, 6, 3, 5, 4, 2], ![0, 6, 3, 5, 4, 1], ![0, 6, 2, 1, 5, 4], ![6, 0, 5, 2, 1, 3], ![6, 0, 4, 2, 1, 3], ![5, 4, 0, 3, 2, 1]], proof := .tail 142 }

theorem namedLeaf011_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1291)) namedLeaf011 = true :=
  by decide +kernel

def namedLeaf012 : LeafData := { rows := ![![1, 2, 3, 6, 4, 5], ![0, 6, 5, 3, 4, 2], ![0, 6, 3, 4, 5, 1], ![0, 6, 2, 5, 1, 4], ![6, 0, 2, 5, 1, 3], ![6, 0, 2, 4, 3, 1], ![5, 4, 0, 3, 2, 1]], proof := .tail 82 }

theorem namedLeaf012_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1292)) namedLeaf012 = true :=
  by decide +kernel

def namedLeaf013 : LeafData := { rows := ![![1, 2, 3, 6, 4, 5], ![0, 6, 5, 3, 4, 2], ![0, 6, 3, 5, 4, 1], ![0, 6, 2, 5, 1, 4], ![6, 0, 5, 2, 1, 3], ![6, 0, 4, 2, 3, 1], ![5, 4, 0, 3, 2, 1]], proof := .tail 82 }

theorem namedLeaf013_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1293)) namedLeaf013 = true :=
  by decide +kernel

def namedLeaf014 : LeafData := { rows := ![![1, 2, 3, 6, 4, 5], ![0, 6, 5, 3, 4, 2], ![0, 6, 5, 3, 4, 1], ![0, 6, 5, 2, 1, 4], ![6, 0, 5, 2, 1, 3], ![6, 0, 4, 3, 2, 1], ![5, 4, 0, 3, 2, 1]], proof := .tail 10 }

theorem namedLeaf014_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1294)) namedLeaf014 = true :=
  by decide +kernel

def namedLeaf015 : LeafData := { rows := ![![1, 2, 3, 6, 4, 5], ![0, 6, 4, 3, 5, 2], ![0, 6, 3, 4, 5, 1], ![0, 6, 2, 4, 1, 5], ![6, 0, 2, 3, 1, 5], ![6, 0, 2, 1, 3, 4], ![5, 4, 0, 3, 2, 1]], proof := .tail 34 }

theorem namedLeaf015_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1295)) namedLeaf015 = true :=
  by decide +kernel

def namedLeaf016 : LeafData := { rows := ![![1, 2, 3, 6, 4, 5], ![0, 6, 4, 3, 5, 2], ![0, 6, 4, 3, 5, 1], ![0, 6, 4, 2, 1, 5], ![6, 0, 3, 2, 1, 5], ![6, 0, 2, 1, 3, 4], ![5, 4, 0, 3, 2, 1]], proof := .tail 81 }

theorem namedLeaf016_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1296)) namedLeaf016 = true :=
  by decide +kernel

def namedLeaf017 : LeafData := { rows := ![![1, 2, 3, 6, 4, 5], ![0, 6, 4, 5, 3, 2], ![0, 6, 3, 4, 5, 1], ![0, 6, 2, 4, 5, 1], ![6, 0, 2, 3, 1, 5], ![6, 0, 2, 3, 1, 4], ![5, 4, 0, 3, 2, 1]], proof := .tail 74 }

theorem namedLeaf017_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1297)) namedLeaf017 = true :=
  by decide +kernel

def namedLeaf018 : LeafData := { rows := ![![1, 2, 3, 6, 4, 5], ![0, 6, 4, 5, 3, 2], ![0, 6, 4, 3, 5, 1], ![0, 6, 4, 2, 5, 1], ![6, 0, 3, 2, 1, 5], ![6, 0, 2, 3, 1, 4], ![5, 4, 0, 3, 2, 1]], proof := .tail 71 }

theorem namedLeaf018_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1298)) namedLeaf018 = true :=
  by decide +kernel

def namedLeaf019 : LeafData := { rows := ![![1, 2, 3, 6, 4, 5], ![0, 6, 4, 5, 3, 2], ![0, 6, 4, 5, 3, 1], ![0, 6, 4, 5, 2, 1], ![6, 0, 3, 2, 1, 5], ![6, 0, 3, 2, 1, 4], ![5, 4, 0, 3, 2, 1]], proof := .tail 168 }

theorem namedLeaf019_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1299)) namedLeaf019 = true :=
  by decide +kernel

def namedLeaf020 : LeafData := { rows := ![![1, 2, 3, 6, 4, 5], ![0, 6, 5, 4, 3, 2], ![0, 6, 3, 4, 5, 1], ![0, 6, 2, 4, 5, 1], ![6, 0, 2, 3, 5, 1], ![6, 0, 2, 3, 4, 1], ![5, 4, 0, 3, 2, 1]], proof := .tail 59 }

theorem namedLeaf020_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1300)) namedLeaf020 = true :=
  by decide +kernel

def namedLeaf021 : LeafData := { rows := ![![1, 2, 3, 6, 4, 5], ![0, 6, 5, 4, 3, 2], ![0, 6, 3, 4, 5, 1], ![0, 6, 2, 5, 4, 1], ![6, 0, 2, 5, 3, 1], ![6, 0, 2, 4, 3, 1], ![5, 4, 0, 3, 2, 1]], proof := .tail 105 }

theorem namedLeaf021_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1301)) namedLeaf021 = true :=
  by decide +kernel

def namedLeaf022 : LeafData := { rows := ![![1, 2, 3, 6, 4, 5], ![0, 6, 5, 4, 3, 2], ![0, 6, 3, 5, 4, 1], ![0, 6, 2, 5, 4, 1], ![6, 0, 5, 2, 3, 1], ![6, 0, 4, 2, 3, 1], ![5, 4, 0, 3, 2, 1]], proof := .tail 28 }

theorem namedLeaf022_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1302)) namedLeaf022 = true :=
  by decide +kernel

def namedLeaf023 : LeafData := { rows := ![![1, 2, 3, 6, 4, 5], ![0, 6, 5, 4, 3, 2], ![0, 6, 5, 3, 4, 1], ![0, 6, 5, 2, 4, 1], ![6, 0, 5, 2, 3, 1], ![6, 0, 4, 3, 2, 1], ![5, 4, 0, 3, 2, 1]], proof := .tail 160 }

theorem namedLeaf023_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1303)) namedLeaf023 = true :=
  by decide +kernel

def namedLeaf024 : LeafData := { rows := ![![1, 2, 3, 6, 4, 5], ![0, 6, 5, 4, 3, 2], ![0, 6, 4, 3, 5, 1], ![0, 6, 4, 2, 5, 1], ![6, 0, 3, 2, 5, 1], ![6, 0, 2, 3, 4, 1], ![5, 4, 0, 3, 2, 1]], proof := .tail 104 }

theorem namedLeaf024_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1304)) namedLeaf024 = true :=
  by decide +kernel

def namedLeaf025 : LeafData := { rows := ![![1, 2, 3, 6, 4, 5], ![0, 6, 5, 4, 3, 2], ![0, 6, 4, 5, 3, 1], ![0, 6, 4, 5, 2, 1], ![6, 0, 3, 2, 5, 1], ![6, 0, 3, 2, 4, 1], ![5, 4, 0, 3, 2, 1]], proof := .tail 85 }

theorem namedLeaf025_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1305)) namedLeaf025 = true :=
  by decide +kernel

def namedLeaf026 : LeafData := { rows := ![![1, 2, 3, 6, 4, 5], ![0, 6, 5, 4, 3, 2], ![0, 6, 5, 4, 3, 1], ![0, 6, 4, 5, 2, 1], ![6, 0, 3, 5, 2, 1], ![6, 0, 3, 4, 2, 1], ![5, 4, 0, 3, 2, 1]], proof := .tail 41 }

theorem namedLeaf026_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1306)) namedLeaf026 = true :=
  by decide +kernel

def namedLeaf027 : LeafData := { rows := ![![1, 2, 3, 6, 4, 5], ![0, 6, 5, 4, 3, 2], ![0, 6, 5, 4, 3, 1], ![0, 6, 5, 4, 2, 1], ![6, 0, 5, 3, 2, 1], ![6, 0, 4, 3, 2, 1], ![5, 4, 0, 3, 2, 1]], proof := .tail 107 }

theorem namedLeaf027_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1307)) namedLeaf027 = true :=
  by decide +kernel

def namedLeaf028 : LeafData := { rows := ![![1, 2, 3, 5, 4, 6], ![0, 2, 3, 5, 4, 6], ![0, 1, 3, 5, 4, 6], ![0, 1, 2, 5, 4, 6], ![5, 0, 1, 2, 3, 6], ![4, 0, 1, 2, 3, 6], ![0, 1, 2, 3, 4, 5]], proof := .tail 45 }

theorem namedLeaf028_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1308)) namedLeaf028 = true :=
  by decide +kernel

def namedLeaf029 : LeafData := { rows := ![![1, 2, 3, 5, 4, 6], ![0, 2, 3, 5, 4, 6], ![0, 1, 3, 5, 4, 6], ![0, 1, 2, 5, 6, 4], ![5, 0, 1, 2, 6, 3], ![4, 0, 1, 2, 3, 6], ![0, 1, 2, 4, 3, 5]], proof := .tail 92 }

theorem namedLeaf029_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1309)) namedLeaf029 = true :=
  by decide +kernel

def namedLeaf030 : LeafData := { rows := ![![1, 2, 3, 5, 4, 6], ![0, 2, 3, 5, 4, 6], ![0, 1, 3, 5, 4, 6], ![0, 1, 2, 6, 5, 4], ![5, 0, 1, 2, 6, 3], ![4, 0, 1, 2, 6, 3], ![0, 1, 2, 4, 5, 3]], proof := .tail 30 }

theorem namedLeaf030_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1310)) namedLeaf030 = true :=
  by decide +kernel

def namedLeaf031 : LeafData := { rows := ![![1, 2, 3, 5, 4, 6], ![0, 2, 3, 5, 4, 6], ![0, 1, 3, 5, 6, 4], ![0, 1, 2, 5, 6, 4], ![5, 0, 1, 6, 2, 3], ![4, 0, 1, 2, 3, 6], ![0, 1, 4, 2, 3, 5]], proof := .tail 16 }

theorem namedLeaf031_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1311)) namedLeaf031 = true :=
  by decide +kernel

def namedLeaf032 : LeafData := { rows := ![![1, 2, 3, 5, 4, 6], ![0, 2, 3, 5, 4, 6], ![0, 1, 3, 5, 6, 4], ![0, 1, 2, 6, 5, 4], ![5, 0, 1, 6, 2, 3], ![4, 0, 1, 2, 6, 3], ![0, 1, 4, 2, 5, 3]], proof := .tail 155 }

theorem namedLeaf032_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1312)) namedLeaf032 = true :=
  by decide +kernel

def namedLeaf033 : LeafData := { rows := ![![1, 2, 3, 5, 4, 6], ![0, 2, 3, 5, 4, 6], ![0, 1, 3, 6, 5, 4], ![0, 1, 2, 6, 5, 4], ![5, 0, 1, 6, 2, 3], ![4, 0, 1, 6, 2, 3], ![0, 1, 4, 5, 2, 3]], proof := .tail 94 }

theorem namedLeaf033_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1313)) namedLeaf033 = true :=
  by decide +kernel

def namedLeaf034 : LeafData := { rows := ![![1, 2, 3, 5, 4, 6], ![0, 2, 3, 5, 4, 6], ![0, 1, 6, 3, 5, 4], ![0, 1, 6, 2, 5, 4], ![5, 0, 1, 6, 2, 3], ![4, 0, 1, 6, 2, 3], ![0, 1, 4, 5, 3, 2]], proof := .tail 97 }

theorem namedLeaf034_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1314)) namedLeaf034 = true :=
  by decide +kernel

def namedLeaf035 : LeafData := { rows := ![![1, 2, 3, 5, 4, 6], ![0, 2, 3, 5, 6, 4], ![0, 1, 3, 5, 6, 4], ![0, 1, 2, 5, 6, 4], ![5, 0, 6, 1, 2, 3], ![4, 0, 1, 2, 3, 6], ![0, 4, 1, 2, 3, 5]], proof := .tail 91 }

theorem namedLeaf035_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1315)) namedLeaf035 = true :=
  by decide +kernel

def namedLeaf036 : LeafData := { rows := ![![1, 2, 3, 5, 4, 6], ![0, 2, 3, 5, 6, 4], ![0, 1, 3, 5, 6, 4], ![0, 1, 2, 6, 5, 4], ![5, 0, 6, 1, 2, 3], ![4, 0, 1, 2, 6, 3], ![0, 4, 1, 2, 5, 3]], proof := .tail 128 }

theorem namedLeaf036_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1316)) namedLeaf036 = true :=
  by decide +kernel

def namedLeaf037 : LeafData := { rows := ![![1, 2, 3, 5, 4, 6], ![0, 2, 3, 5, 6, 4], ![0, 1, 3, 6, 5, 4], ![0, 1, 2, 6, 5, 4], ![5, 0, 6, 1, 2, 3], ![4, 0, 1, 6, 2, 3], ![0, 4, 1, 5, 2, 3]], proof := .tail 166 }

theorem namedLeaf037_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1317)) namedLeaf037 = true :=
  by decide +kernel

def namedLeaf038 : LeafData := { rows := ![![1, 2, 3, 5, 4, 6], ![0, 2, 3, 5, 6, 4], ![0, 1, 6, 3, 5, 4], ![0, 1, 6, 2, 5, 4], ![5, 0, 6, 1, 2, 3], ![4, 0, 1, 6, 2, 3], ![0, 4, 1, 5, 3, 2]], proof := .tail 106 }

theorem namedLeaf038_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1318)) namedLeaf038 = true :=
  by decide +kernel

def namedLeaf039 : LeafData := { rows := ![![1, 2, 3, 5, 4, 6], ![0, 2, 3, 6, 5, 4], ![0, 1, 3, 6, 5, 4], ![0, 1, 2, 6, 5, 4], ![5, 0, 6, 1, 2, 3], ![4, 0, 6, 1, 2, 3], ![0, 4, 5, 1, 2, 3]], proof := .tail 22 }

theorem namedLeaf039_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1319)) namedLeaf039 = true :=
  by decide +kernel

def namedLeaf040 : LeafData := { rows := ![![1, 2, 3, 5, 4, 6], ![0, 2, 3, 6, 5, 4], ![0, 1, 6, 3, 5, 4], ![0, 1, 6, 2, 5, 4], ![5, 0, 6, 1, 2, 3], ![4, 0, 6, 1, 2, 3], ![0, 4, 5, 1, 3, 2]], proof := .tail 106 }

theorem namedLeaf040_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1320)) namedLeaf040 = true :=
  by decide +kernel

def namedLeaf041 : LeafData := { rows := ![![1, 2, 3, 5, 4, 6], ![0, 2, 6, 3, 5, 4], ![0, 1, 6, 3, 5, 4], ![0, 6, 1, 2, 5, 4], ![5, 0, 6, 1, 2, 3], ![4, 0, 6, 1, 2, 3], ![0, 4, 5, 3, 1, 2]], proof := .tail 53 }

theorem namedLeaf041_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1321)) namedLeaf041 = true :=
  by decide +kernel

def namedLeaf042 : LeafData := { rows := ![![1, 2, 3, 5, 4, 6], ![0, 6, 2, 3, 5, 4], ![0, 6, 1, 3, 5, 4], ![0, 6, 1, 2, 5, 4], ![5, 0, 6, 1, 2, 3], ![4, 0, 6, 1, 2, 3], ![0, 4, 5, 3, 2, 1]], proof := .tail 48 }

theorem namedLeaf042_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1322)) namedLeaf042 = true :=
  by decide +kernel

def namedLeaf043 : LeafData := { rows := ![![1, 2, 3, 5, 4, 6], ![0, 2, 3, 5, 4, 6], ![0, 1, 5, 3, 4, 6], ![0, 1, 5, 2, 4, 6], ![5, 0, 1, 2, 3, 6], ![4, 0, 1, 3, 2, 6], ![0, 1, 2, 3, 4, 5]], proof := .tail 43 }

theorem namedLeaf043_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1323)) namedLeaf043 = true :=
  by decide +kernel

def namedLeaf044 : LeafData := { rows := ![![1, 2, 3, 5, 4, 6], ![0, 2, 3, 5, 4, 6], ![0, 1, 5, 3, 4, 6], ![0, 1, 5, 2, 6, 4], ![5, 0, 1, 2, 6, 3], ![4, 0, 1, 3, 2, 6], ![0, 1, 2, 4, 3, 5]], proof := .tail 51 }

theorem namedLeaf044_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1324)) namedLeaf044 = true :=
  by decide +kernel

def namedLeaf045 : LeafData := { rows := ![![1, 2, 3, 5, 4, 6], ![0, 2, 3, 5, 4, 6], ![0, 1, 5, 3, 6, 4], ![0, 1, 5, 2, 6, 4], ![5, 0, 1, 6, 2, 3], ![4, 0, 1, 3, 2, 6], ![0, 1, 4, 2, 3, 5]], proof := .tail 141 }

theorem namedLeaf045_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1325)) namedLeaf045 = true :=
  by decide +kernel

def namedLeaf046 : LeafData := { rows := ![![1, 2, 3, 5, 4, 6], ![0, 2, 3, 5, 4, 6], ![0, 1, 5, 6, 3, 4], ![0, 1, 5, 6, 2, 4], ![5, 0, 1, 6, 2, 3], ![4, 0, 1, 3, 2, 6], ![0, 1, 4, 3, 2, 5]], proof := .tail 84 }

theorem namedLeaf046_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1326)) namedLeaf046 = true :=
  by decide +kernel

def namedLeaf047 : LeafData := { rows := ![![1, 2, 3, 5, 4, 6], ![0, 2, 3, 5, 4, 6], ![0, 1, 6, 5, 3, 4], ![0, 1, 5, 6, 2, 4], ![5, 0, 1, 6, 2, 3], ![4, 0, 1, 3, 6, 2], ![0, 1, 4, 3, 5, 2]], proof := .tail 25 }

theorem namedLeaf047_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1327)) namedLeaf047 = true :=
  by decide +kernel

def namedLeaf048 : LeafData := { rows := ![![1, 2, 3, 5, 4, 6], ![0, 2, 3, 5, 4, 6], ![0, 1, 6, 5, 3, 4], ![0, 1, 6, 5, 2, 4], ![5, 0, 1, 6, 2, 3], ![4, 0, 1, 6, 3, 2], ![0, 1, 4, 5, 3, 2]], proof := .tail 114 }

theorem namedLeaf048_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1328)) namedLeaf048 = true :=
  by decide +kernel

def namedLeaf049 : LeafData := { rows := ![![1, 2, 3, 5, 4, 6], ![0, 2, 3, 5, 6, 4], ![0, 1, 5, 3, 6, 4], ![0, 1, 5, 2, 6, 4], ![5, 0, 6, 1, 2, 3], ![4, 0, 1, 3, 2, 6], ![0, 4, 1, 2, 3, 5]], proof := .tail 141 }

theorem namedLeaf049_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1329)) namedLeaf049 = true :=
  by decide +kernel

def namedLeaf050 : LeafData := { rows := ![![1, 2, 3, 5, 4, 6], ![0, 2, 3, 5, 6, 4], ![0, 1, 5, 6, 3, 4], ![0, 1, 5, 6, 2, 4], ![5, 0, 6, 1, 2, 3], ![4, 0, 1, 3, 2, 6], ![0, 4, 1, 3, 2, 5]], proof := .tail 159 }

theorem namedLeaf050_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1330)) namedLeaf050 = true :=
  by decide +kernel

def namedLeaf051 : LeafData := { rows := ![![1, 2, 3, 5, 4, 6], ![0, 2, 3, 5, 6, 4], ![0, 1, 6, 5, 3, 4], ![0, 1, 5, 6, 2, 4], ![5, 0, 6, 1, 2, 3], ![4, 0, 1, 3, 6, 2], ![0, 4, 1, 3, 5, 2]], proof := .tail 25 }

theorem namedLeaf051_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1331)) namedLeaf051 = true :=
  by decide +kernel

def namedLeaf052 : LeafData := { rows := ![![1, 2, 3, 5, 4, 6], ![0, 2, 3, 5, 6, 4], ![0, 1, 6, 5, 3, 4], ![0, 1, 6, 5, 2, 4], ![5, 0, 6, 1, 2, 3], ![4, 0, 1, 6, 3, 2], ![0, 4, 1, 5, 3, 2]], proof := .tail 36 }

theorem namedLeaf052_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1332)) namedLeaf052 = true :=
  by decide +kernel

def namedLeaf053 : LeafData := { rows := ![![1, 2, 3, 5, 4, 6], ![0, 2, 3, 6, 5, 4], ![0, 1, 6, 5, 3, 4], ![0, 1, 6, 5, 2, 4], ![5, 0, 6, 1, 2, 3], ![4, 0, 6, 1, 3, 2], ![0, 4, 5, 1, 3, 2]], proof := .tail 36 }

theorem namedLeaf053_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1333)) namedLeaf053 = true :=
  by decide +kernel

def namedLeaf054 : LeafData := { rows := ![![1, 2, 3, 5, 4, 6], ![0, 2, 6, 3, 5, 4], ![0, 1, 6, 5, 3, 4], ![0, 6, 1, 5, 2, 4], ![5, 0, 6, 1, 2, 3], ![4, 0, 6, 1, 3, 2], ![0, 4, 5, 3, 1, 2]], proof := .tail 66 }

theorem namedLeaf054_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1334)) namedLeaf054 = true :=
  by decide +kernel

def namedLeaf055 : LeafData := { rows := ![![1, 2, 3, 5, 4, 6], ![0, 6, 2, 3, 5, 4], ![0, 6, 1, 5, 3, 4], ![0, 6, 1, 5, 2, 4], ![5, 0, 6, 1, 2, 3], ![4, 0, 6, 1, 3, 2], ![0, 4, 5, 3, 2, 1]], proof := .tail 66 }

theorem namedLeaf055_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1335)) namedLeaf055 = true :=
  by decide +kernel

def namedLeaf056 : LeafData := { rows := ![![1, 2, 3, 5, 4, 6], ![0, 2, 3, 5, 4, 6], ![0, 1, 5, 4, 3, 6], ![0, 1, 5, 4, 2, 6], ![5, 0, 1, 3, 2, 6], ![4, 0, 1, 3, 2, 6], ![0, 1, 2, 3, 4, 5]], proof := .tail 54 }

theorem namedLeaf056_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1336)) namedLeaf056 = true :=
  by decide +kernel

def namedLeaf057 : LeafData := { rows := ![![1, 2, 3, 5, 4, 6], ![0, 2, 3, 5, 4, 6], ![0, 1, 5, 4, 6, 3], ![0, 1, 5, 4, 6, 2], ![5, 0, 1, 3, 2, 6], ![4, 0, 1, 3, 2, 6], ![0, 1, 3, 2, 4, 5]], proof := .low (![55, 11, 89, 7, 132, 86, 62, 119, 126, 63, 99, 0, 134, 136, 72, 124, 80, 38, 8, 172, 163, 138, 75, 151, 122, 20, 3, 57]) }

theorem namedLeaf057_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1337)) namedLeaf057 = true :=
  by decide +kernel

def namedLeaf058 : LeafData := { rows := ![![1, 2, 3, 5, 4, 6], ![0, 2, 3, 5, 4, 6], ![0, 1, 5, 6, 4, 3], ![0, 1, 5, 4, 6, 2], ![5, 0, 1, 3, 6, 2], ![4, 0, 1, 3, 2, 6], ![0, 1, 3, 4, 2, 5]], proof := .tail 47 }

theorem namedLeaf058_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1338)) namedLeaf058 = true :=
  by decide +kernel

def namedLeaf059 : LeafData := { rows := ![![1, 2, 3, 5, 4, 6], ![0, 2, 3, 5, 4, 6], ![0, 1, 5, 6, 4, 3], ![0, 1, 5, 6, 4, 2], ![5, 0, 1, 6, 3, 2], ![4, 0, 1, 3, 2, 6], ![0, 1, 4, 3, 2, 5]], proof := .tail 153 }

theorem namedLeaf059_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1339)) namedLeaf059 = true :=
  by decide +kernel

def namedLeaf060 : LeafData := { rows := ![![1, 2, 3, 5, 4, 6], ![0, 2, 3, 5, 4, 6], ![0, 1, 6, 5, 4, 3], ![0, 1, 5, 4, 6, 2], ![5, 0, 1, 3, 6, 2], ![4, 0, 1, 3, 6, 2], ![0, 1, 3, 4, 5, 2]], proof := .tail 6 }

theorem namedLeaf060_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1340)) namedLeaf060 = true :=
  by decide +kernel

def namedLeaf061 : LeafData := { rows := ![![1, 2, 3, 5, 4, 6], ![0, 2, 3, 5, 4, 6], ![0, 1, 6, 5, 4, 3], ![0, 1, 5, 6, 4, 2], ![5, 0, 1, 6, 3, 2], ![4, 0, 1, 3, 6, 2], ![0, 1, 4, 3, 5, 2]], proof := .tail 153 }

theorem namedLeaf061_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1341)) namedLeaf061 = true :=
  by decide +kernel

def namedLeaf062 : LeafData := { rows := ![![1, 2, 3, 5, 4, 6], ![0, 2, 3, 5, 4, 6], ![0, 1, 6, 5, 4, 3], ![0, 1, 6, 5, 4, 2], ![5, 0, 1, 6, 3, 2], ![4, 0, 1, 6, 3, 2], ![0, 1, 4, 5, 3, 2]], proof := .tail 149 }

theorem namedLeaf062_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1342)) namedLeaf062 = true :=
  by decide +kernel

def namedLeaf063 : LeafData := { rows := ![![1, 2, 3, 5, 4, 6], ![0, 2, 3, 5, 6, 4], ![0, 1, 5, 6, 4, 3], ![0, 1, 5, 6, 4, 2], ![5, 0, 6, 1, 3, 2], ![4, 0, 1, 3, 2, 6], ![0, 4, 1, 3, 2, 5]], proof := .tail 68 }

theorem namedLeaf063_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1343)) namedLeaf063 = true :=
  by decide +kernel

def namedLeaf064 : LeafData := { rows := ![![1, 2, 3, 5, 4, 6], ![0, 2, 3, 5, 6, 4], ![0, 1, 6, 5, 4, 3], ![0, 1, 5, 6, 4, 2], ![5, 0, 6, 1, 3, 2], ![4, 0, 1, 3, 6, 2], ![0, 4, 1, 3, 5, 2]], proof := .tail 68 }

theorem namedLeaf064_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1344)) namedLeaf064 = true :=
  by decide +kernel

def namedLeaf065 : LeafData := { rows := ![![1, 2, 3, 5, 4, 6], ![0, 2, 3, 5, 6, 4], ![0, 1, 6, 5, 4, 3], ![0, 1, 6, 5, 4, 2], ![5, 0, 6, 1, 3, 2], ![4, 0, 1, 6, 3, 2], ![0, 4, 1, 5, 3, 2]], proof := .tail 24 }

theorem namedLeaf065_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1345)) namedLeaf065 = true :=
  by decide +kernel

def namedLeaf066 : LeafData := { rows := ![![1, 2, 3, 5, 4, 6], ![0, 2, 3, 6, 5, 4], ![0, 1, 6, 5, 4, 3], ![0, 1, 6, 5, 4, 2], ![5, 0, 6, 1, 3, 2], ![4, 0, 6, 1, 3, 2], ![0, 4, 5, 1, 3, 2]], proof := .tail 24 }

theorem namedLeaf066_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1346)) namedLeaf066 = true :=
  by decide +kernel

def namedLeaf067 : LeafData := { rows := ![![1, 2, 3, 5, 4, 6], ![0, 2, 6, 3, 5, 4], ![0, 1, 6, 5, 4, 3], ![0, 6, 1, 5, 4, 2], ![5, 0, 6, 1, 3, 2], ![4, 0, 6, 1, 3, 2], ![0, 4, 5, 3, 1, 2]], proof := .tail 46 }

theorem namedLeaf067_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1347)) namedLeaf067 = true :=
  by decide +kernel

def namedLeaf068 : LeafData := { rows := ![![1, 2, 3, 5, 4, 6], ![0, 6, 2, 3, 5, 4], ![0, 6, 1, 5, 4, 3], ![0, 6, 1, 5, 4, 2], ![5, 0, 6, 1, 3, 2], ![4, 0, 6, 1, 3, 2], ![0, 4, 5, 3, 2, 1]], proof := .tail 46 }

theorem namedLeaf068_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1348)) namedLeaf068 = true :=
  by decide +kernel

def namedLeaf069 : LeafData := { rows := ![![1, 2, 3, 5, 4, 6], ![0, 3, 2, 5, 4, 6], ![0, 3, 1, 5, 4, 6], ![0, 2, 1, 5, 4, 6], ![5, 0, 1, 2, 3, 6], ![4, 0, 1, 2, 3, 6], ![0, 1, 2, 3, 4, 5]], proof := .tail 158 }

theorem namedLeaf069_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1349)) namedLeaf069 = true :=
  by decide +kernel

def namedLeaf070 : LeafData := { rows := ![![1, 2, 3, 5, 4, 6], ![0, 3, 2, 5, 4, 6], ![0, 3, 1, 5, 4, 6], ![0, 2, 1, 5, 6, 4], ![5, 0, 1, 2, 6, 3], ![4, 0, 1, 2, 3, 6], ![0, 1, 2, 4, 3, 5]], proof := .tail 92 }

theorem namedLeaf070_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1350)) namedLeaf070 = true :=
  by decide +kernel

def namedLeaf071 : LeafData := { rows := ![![1, 2, 3, 5, 4, 6], ![0, 3, 2, 5, 4, 6], ![0, 3, 1, 5, 4, 6], ![0, 2, 1, 6, 5, 4], ![5, 0, 1, 2, 6, 3], ![4, 0, 1, 2, 6, 3], ![0, 1, 2, 4, 5, 3]], proof := .tail 30 }

theorem namedLeaf071_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1351)) namedLeaf071 = true :=
  by decide +kernel

def namedLeaf072 : LeafData := { rows := ![![1, 2, 3, 5, 4, 6], ![0, 3, 2, 5, 4, 6], ![0, 3, 1, 5, 6, 4], ![0, 2, 1, 5, 6, 4], ![5, 0, 1, 6, 2, 3], ![4, 0, 1, 2, 3, 6], ![0, 1, 4, 2, 3, 5]], proof := .tail 164 }

theorem namedLeaf072_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1352)) namedLeaf072 = true :=
  by decide +kernel

def namedLeaf073 : LeafData := { rows := ![![1, 2, 3, 5, 4, 6], ![0, 3, 2, 5, 4, 6], ![0, 3, 1, 5, 6, 4], ![0, 2, 1, 6, 5, 4], ![5, 0, 1, 6, 2, 3], ![4, 0, 1, 2, 6, 3], ![0, 1, 4, 2, 5, 3]], proof := .tail 155 }

theorem namedLeaf073_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1353)) namedLeaf073 = true :=
  by decide +kernel

def namedLeaf074 : LeafData := { rows := ![![1, 2, 3, 5, 4, 6], ![0, 3, 2, 5, 4, 6], ![0, 3, 1, 6, 5, 4], ![0, 2, 1, 6, 5, 4], ![5, 0, 1, 6, 2, 3], ![4, 0, 1, 6, 2, 3], ![0, 1, 4, 5, 2, 3]], proof := .tail 166 }

theorem namedLeaf074_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1354)) namedLeaf074 = true :=
  by decide +kernel

def namedLeaf075 : LeafData := { rows := ![![1, 2, 3, 5, 4, 6], ![0, 3, 2, 5, 6, 4], ![0, 3, 1, 5, 6, 4], ![0, 2, 1, 5, 6, 4], ![5, 0, 6, 1, 2, 3], ![4, 0, 1, 2, 3, 6], ![0, 4, 1, 2, 3, 5]], proof := .tail 129 }

theorem namedLeaf075_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1355)) namedLeaf075 = true :=
  by decide +kernel

def namedLeaf076 : LeafData := { rows := ![![1, 2, 3, 5, 4, 6], ![0, 3, 2, 5, 6, 4], ![0, 3, 1, 5, 6, 4], ![0, 2, 1, 6, 5, 4], ![5, 0, 6, 1, 2, 3], ![4, 0, 1, 2, 6, 3], ![0, 4, 1, 2, 5, 3]], proof := .tail 137 }

theorem namedLeaf076_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1356)) namedLeaf076 = true :=
  by decide +kernel

def namedLeaf077 : LeafData := { rows := ![![1, 2, 3, 5, 4, 6], ![0, 3, 2, 5, 6, 4], ![0, 3, 1, 6, 5, 4], ![0, 2, 1, 6, 5, 4], ![5, 0, 6, 1, 2, 3], ![4, 0, 1, 6, 2, 3], ![0, 4, 1, 5, 2, 3]], proof := .tail 166 }

theorem namedLeaf077_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1357)) namedLeaf077 = true :=
  by decide +kernel

def namedLeaf078 : LeafData := { rows := ![![1, 2, 3, 5, 4, 6], ![0, 3, 2, 6, 5, 4], ![0, 3, 1, 6, 5, 4], ![0, 2, 1, 6, 5, 4], ![5, 0, 6, 1, 2, 3], ![4, 0, 6, 1, 2, 3], ![0, 4, 5, 1, 2, 3]], proof := .tail 22 }

theorem namedLeaf078_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1358)) namedLeaf078 = true :=
  by decide +kernel

def namedLeaf079 : LeafData := { rows := ![![1, 2, 3, 5, 4, 6], ![0, 3, 6, 2, 5, 4], ![0, 3, 6, 1, 5, 4], ![0, 2, 1, 6, 5, 4], ![5, 0, 6, 1, 2, 3], ![4, 0, 6, 1, 2, 3], ![0, 4, 5, 2, 1, 3]], proof := .tail 1 }

theorem namedLeaf079_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1359)) namedLeaf079 = true :=
  by decide +kernel

def namedLeaf080 : LeafData := { rows := ![![1, 2, 3, 5, 4, 6], ![0, 6, 3, 2, 5, 4], ![0, 3, 6, 1, 5, 4], ![0, 2, 6, 1, 5, 4], ![5, 0, 6, 1, 2, 3], ![4, 0, 6, 1, 2, 3], ![0, 4, 5, 2, 3, 1]], proof := .tail 154 }

theorem namedLeaf080_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1360)) namedLeaf080 = true :=
  by decide +kernel

def namedLeaf081 : LeafData := { rows := ![![1, 2, 3, 5, 4, 6], ![0, 6, 3, 2, 5, 4], ![0, 6, 3, 1, 5, 4], ![0, 6, 2, 1, 5, 4], ![5, 0, 6, 1, 2, 3], ![4, 0, 6, 1, 2, 3], ![0, 4, 5, 3, 2, 1]], proof := .tail 29 }

theorem namedLeaf081_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1361)) namedLeaf081 = true :=
  by decide +kernel

def namedLeaf082 : LeafData := { rows := ![![1, 2, 3, 5, 4, 6], ![0, 2, 5, 3, 4, 6], ![0, 1, 5, 3, 4, 6], ![0, 5, 1, 2, 4, 6], ![5, 0, 1, 2, 3, 6], ![4, 0, 3, 1, 2, 6], ![0, 1, 2, 3, 4, 5]], proof := .tail 123 }

theorem namedLeaf082_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1362)) namedLeaf082 = true :=
  by decide +kernel

def namedLeaf083 : LeafData := { rows := ![![1, 2, 3, 5, 4, 6], ![0, 2, 5, 3, 4, 6], ![0, 1, 5, 3, 4, 6], ![0, 5, 1, 2, 6, 4], ![5, 0, 1, 2, 6, 3], ![4, 0, 3, 1, 2, 6], ![0, 1, 2, 4, 3, 5]], proof := .tail 100 }

theorem namedLeaf083_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1363)) namedLeaf083 = true :=
  by decide +kernel

def namedLeaf084 : LeafData := { rows := ![![1, 2, 3, 5, 4, 6], ![0, 2, 5, 3, 4, 6], ![0, 1, 5, 3, 6, 4], ![0, 5, 1, 2, 6, 4], ![5, 0, 1, 6, 2, 3], ![4, 0, 3, 1, 2, 6], ![0, 1, 4, 2, 3, 5]], proof := .tail 156 }

theorem namedLeaf084_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1364)) namedLeaf084 = true :=
  by decide +kernel

def namedLeaf085 : LeafData := { rows := ![![1, 2, 3, 5, 4, 6], ![0, 2, 5, 3, 4, 6], ![0, 1, 5, 6, 3, 4], ![0, 5, 1, 6, 2, 4], ![5, 0, 1, 6, 2, 3], ![4, 0, 3, 1, 2, 6], ![0, 1, 4, 3, 2, 5]], proof := .tail 101 }

theorem namedLeaf085_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1365)) namedLeaf085 = true :=
  by decide +kernel

def namedLeaf086 : LeafData := { rows := ![![1, 2, 3, 5, 4, 6], ![0, 2, 5, 3, 4, 6], ![0, 1, 6, 5, 3, 4], ![0, 5, 1, 6, 2, 4], ![5, 0, 1, 6, 2, 3], ![4, 0, 3, 1, 6, 2], ![0, 1, 4, 3, 5, 2]], proof := .tail 23 }

theorem namedLeaf086_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1366)) namedLeaf086 = true :=
  by decide +kernel

def namedLeaf087 : LeafData := { rows := ![![1, 2, 3, 5, 4, 6], ![0, 2, 5, 3, 6, 4], ![0, 1, 5, 3, 6, 4], ![0, 5, 1, 2, 6, 4], ![5, 0, 6, 1, 2, 3], ![4, 0, 3, 1, 2, 6], ![0, 4, 1, 2, 3, 5]], proof := .tail 91 }

theorem namedLeaf087_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1367)) namedLeaf087 = true :=
  by decide +kernel

def namedLeaf088 : LeafData := { rows := ![![1, 2, 3, 5, 4, 6], ![0, 2, 5, 3, 6, 4], ![0, 1, 5, 6, 3, 4], ![0, 5, 1, 6, 2, 4], ![5, 0, 6, 1, 2, 3], ![4, 0, 3, 1, 2, 6], ![0, 4, 1, 3, 2, 5]], proof := .tail 159 }

theorem namedLeaf088_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1368)) namedLeaf088 = true :=
  by decide +kernel

def namedLeaf089 : LeafData := { rows := ![![1, 2, 3, 5, 4, 6], ![0, 2, 5, 3, 6, 4], ![0, 1, 6, 5, 3, 4], ![0, 5, 1, 6, 2, 4], ![5, 0, 6, 1, 2, 3], ![4, 0, 3, 1, 6, 2], ![0, 4, 1, 3, 5, 2]], proof := .tail 23 }

theorem namedLeaf089_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1369)) namedLeaf089 = true :=
  by decide +kernel

def namedLeaf090 : LeafData := { rows := ![![1, 2, 3, 5, 4, 6], ![0, 2, 5, 6, 3, 4], ![0, 1, 5, 6, 3, 4], ![0, 5, 6, 1, 2, 4], ![5, 0, 6, 1, 2, 3], ![4, 0, 3, 1, 2, 6], ![0, 4, 3, 1, 2, 5]], proof := .tail 21 }

theorem namedLeaf090_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1370)) namedLeaf090 = true :=
  by decide +kernel

def namedLeaf091 : LeafData := { rows := ![![1, 2, 3, 5, 4, 6], ![0, 2, 5, 6, 3, 4], ![0, 1, 6, 5, 3, 4], ![0, 5, 6, 1, 2, 4], ![5, 0, 6, 1, 2, 3], ![4, 0, 3, 1, 6, 2], ![0, 4, 3, 1, 5, 2]], proof := .tail 118 }

theorem namedLeaf091_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1371)) namedLeaf091 = true :=
  by decide +kernel

def namedLeaf092 : LeafData := { rows := ![![1, 2, 3, 5, 4, 6], ![0, 2, 6, 5, 3, 4], ![0, 1, 6, 5, 3, 4], ![0, 5, 6, 1, 2, 4], ![5, 0, 6, 1, 2, 3], ![4, 0, 3, 6, 1, 2], ![0, 4, 3, 5, 1, 2]], proof := .tail 171 }

theorem namedLeaf092_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1372)) namedLeaf092 = true :=
  by decide +kernel

def namedLeaf093 : LeafData := { rows := ![![1, 2, 3, 5, 4, 6], ![0, 2, 6, 5, 3, 4], ![0, 1, 6, 5, 3, 4], ![0, 6, 5, 1, 2, 4], ![5, 0, 6, 1, 2, 3], ![4, 0, 6, 3, 1, 2], ![0, 4, 5, 3, 1, 2]], proof := .tail 35 }

theorem namedLeaf093_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1373)) namedLeaf093 = true :=
  by decide +kernel

def namedLeaf094 : LeafData := { rows := ![![1, 2, 3, 5, 4, 6], ![0, 6, 2, 5, 3, 4], ![0, 6, 1, 5, 3, 4], ![0, 5, 6, 1, 2, 4], ![5, 0, 6, 1, 2, 3], ![4, 0, 3, 6, 1, 2], ![0, 4, 3, 5, 2, 1]], proof := .tail 143 }

theorem namedLeaf094_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1374)) namedLeaf094 = true :=
  by decide +kernel

def namedLeaf095 : LeafData := { rows := ![![1, 2, 3, 5, 4, 6], ![0, 6, 2, 5, 3, 4], ![0, 6, 1, 5, 3, 4], ![0, 6, 5, 1, 2, 4], ![5, 0, 6, 1, 2, 3], ![4, 0, 6, 3, 1, 2], ![0, 4, 5, 3, 2, 1]], proof := .tail 35 }

theorem namedLeaf095_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1375)) namedLeaf095 = true :=
  by decide +kernel

def namedLeaf096 : LeafData := { rows := ![![1, 2, 3, 5, 4, 6], ![0, 2, 5, 3, 4, 6], ![0, 1, 5, 4, 3, 6], ![0, 5, 1, 4, 2, 6], ![5, 0, 1, 3, 2, 6], ![4, 0, 3, 1, 2, 6], ![0, 1, 2, 3, 4, 5]], proof := .tail 88 }

theorem namedLeaf096_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1376)) namedLeaf096 = true :=
  by decide +kernel

def namedLeaf097 : LeafData := { rows := ![![1, 2, 3, 5, 4, 6], ![0, 2, 5, 3, 4, 6], ![0, 1, 5, 4, 6, 3], ![0, 5, 1, 4, 6, 2], ![5, 0, 1, 3, 2, 6], ![4, 0, 3, 1, 2, 6], ![0, 1, 3, 2, 4, 5]], proof := .tail 40 }

theorem namedLeaf097_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1377)) namedLeaf097 = true :=
  by decide +kernel

def namedLeaf098 : LeafData := { rows := ![![1, 2, 3, 5, 4, 6], ![0, 2, 5, 3, 4, 6], ![0, 1, 5, 6, 4, 3], ![0, 5, 1, 4, 6, 2], ![5, 0, 1, 3, 6, 2], ![4, 0, 3, 1, 2, 6], ![0, 1, 3, 4, 2, 5]], proof := .tail 44 }

theorem namedLeaf098_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1378)) namedLeaf098 = true :=
  by decide +kernel

def namedLeaf099 : LeafData := { rows := ![![1, 2, 3, 5, 4, 6], ![0, 2, 5, 3, 4, 6], ![0, 1, 5, 6, 4, 3], ![0, 5, 1, 6, 4, 2], ![5, 0, 1, 6, 3, 2], ![4, 0, 3, 1, 2, 6], ![0, 1, 4, 3, 2, 5]], proof := .tail 102 }

theorem namedLeaf099_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1379)) namedLeaf099 = true :=
  by decide +kernel

def namedLeaf100 : LeafData := { rows := ![![1, 2, 3, 5, 4, 6], ![0, 2, 5, 3, 4, 6], ![0, 1, 6, 5, 4, 3], ![0, 5, 1, 4, 6, 2], ![5, 0, 1, 3, 6, 2], ![4, 0, 3, 1, 6, 2], ![0, 1, 3, 4, 5, 2]], proof := .tail 109 }

theorem namedLeaf100_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1380)) namedLeaf100 = true :=
  by decide +kernel

def namedLeaf101 : LeafData := { rows := ![![1, 2, 3, 5, 4, 6], ![0, 2, 5, 3, 4, 6], ![0, 1, 6, 5, 4, 3], ![0, 5, 1, 6, 4, 2], ![5, 0, 1, 6, 3, 2], ![4, 0, 3, 1, 6, 2], ![0, 1, 4, 3, 5, 2]], proof := .tail 102 }

theorem namedLeaf101_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1381)) namedLeaf101 = true :=
  by decide +kernel

def namedLeaf102 : LeafData := { rows := ![![1, 2, 3, 5, 4, 6], ![0, 2, 5, 3, 6, 4], ![0, 1, 5, 6, 4, 3], ![0, 5, 1, 6, 4, 2], ![5, 0, 6, 1, 3, 2], ![4, 0, 3, 1, 2, 6], ![0, 4, 1, 3, 2, 5]], proof := .tail 68 }

theorem namedLeaf102_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1382)) namedLeaf102 = true :=
  by decide +kernel

def namedLeaf103 : LeafData := { rows := ![![1, 2, 3, 5, 4, 6], ![0, 2, 5, 3, 6, 4], ![0, 1, 6, 5, 4, 3], ![0, 5, 1, 6, 4, 2], ![5, 0, 6, 1, 3, 2], ![4, 0, 3, 1, 6, 2], ![0, 4, 1, 3, 5, 2]], proof := .tail 68 }

theorem namedLeaf103_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1383)) namedLeaf103 = true :=
  by decide +kernel

def namedLeaf104 : LeafData := { rows := ![![1, 2, 3, 5, 4, 6], ![0, 2, 5, 6, 3, 4], ![0, 1, 5, 6, 4, 3], ![0, 5, 6, 1, 4, 2], ![5, 0, 6, 1, 3, 2], ![4, 0, 3, 1, 2, 6], ![0, 4, 3, 1, 2, 5]], proof := .tail 152 }

theorem namedLeaf104_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1384)) namedLeaf104 = true :=
  by decide +kernel

def namedLeaf105 : LeafData := { rows := ![![1, 2, 3, 5, 4, 6], ![0, 2, 5, 6, 3, 4], ![0, 1, 6, 5, 4, 3], ![0, 5, 6, 1, 4, 2], ![5, 0, 6, 1, 3, 2], ![4, 0, 3, 1, 6, 2], ![0, 4, 3, 1, 5, 2]], proof := .tail 152 }

theorem namedLeaf105_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1385)) namedLeaf105 = true :=
  by decide +kernel

def namedLeaf106 : LeafData := { rows := ![![1, 2, 3, 5, 4, 6], ![0, 2, 6, 5, 3, 4], ![0, 1, 6, 5, 4, 3], ![0, 5, 6, 1, 4, 2], ![5, 0, 6, 1, 3, 2], ![4, 0, 3, 6, 1, 2], ![0, 4, 3, 5, 1, 2]], proof := .tail 93 }

theorem namedLeaf106_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1386)) namedLeaf106 = true :=
  by decide +kernel

def namedLeaf107 : LeafData := { rows := ![![1, 2, 3, 5, 4, 6], ![0, 2, 6, 5, 3, 4], ![0, 1, 6, 5, 4, 3], ![0, 6, 5, 1, 4, 2], ![5, 0, 6, 1, 3, 2], ![4, 0, 6, 3, 1, 2], ![0, 4, 5, 3, 1, 2]], proof := .tail 19 }

theorem namedLeaf107_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1387)) namedLeaf107 = true :=
  by decide +kernel

def namedLeaf108 : LeafData := { rows := ![![1, 2, 3, 5, 4, 6], ![0, 6, 2, 5, 3, 4], ![0, 6, 1, 5, 4, 3], ![0, 5, 6, 1, 4, 2], ![5, 0, 6, 1, 3, 2], ![4, 0, 3, 6, 1, 2], ![0, 4, 3, 5, 2, 1]], proof := .tail 93 }

theorem namedLeaf108_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1388)) namedLeaf108 = true :=
  by decide +kernel

def namedLeaf109 : LeafData := { rows := ![![1, 2, 3, 5, 4, 6], ![0, 6, 2, 5, 3, 4], ![0, 6, 1, 5, 4, 3], ![0, 6, 5, 1, 4, 2], ![5, 0, 6, 1, 3, 2], ![4, 0, 6, 3, 1, 2], ![0, 4, 5, 3, 2, 1]], proof := .tail 19 }

theorem namedLeaf109_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1389)) namedLeaf109 = true :=
  by decide +kernel

def namedLeaf110 : LeafData := { rows := ![![1, 2, 3, 5, 4, 6], ![0, 2, 5, 4, 3, 6], ![0, 1, 5, 4, 3, 6], ![0, 5, 4, 1, 2, 6], ![5, 0, 3, 1, 2, 6], ![4, 0, 3, 1, 2, 6], ![0, 1, 2, 3, 4, 5]], proof := .low (![70, 39, 76, 78, 108, 5, 58, 31, 140, 33, 83, 148, 65, 139, 32, 116, 112, 73, 110, 121, 50, 133, 90, 67, 111, 26, 15, 127]) }

theorem namedLeaf110_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1390)) namedLeaf110 = true :=
  by decide +kernel

def namedLeaf111 : LeafData := { rows := ![![1, 2, 3, 5, 4, 6], ![0, 2, 5, 4, 3, 6], ![0, 1, 5, 4, 6, 3], ![0, 5, 4, 1, 6, 2], ![5, 0, 3, 1, 2, 6], ![4, 0, 3, 1, 2, 6], ![0, 1, 3, 2, 4, 5]], proof := .tail 147 }

theorem namedLeaf111_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1391)) namedLeaf111 = true :=
  by decide +kernel

def namedLeaf112 : LeafData := { rows := ![![1, 2, 3, 5, 4, 6], ![0, 2, 5, 4, 3, 6], ![0, 1, 5, 6, 4, 3], ![0, 5, 4, 1, 6, 2], ![5, 0, 3, 1, 6, 2], ![4, 0, 3, 1, 2, 6], ![0, 1, 3, 4, 2, 5]], proof := .tail 115 }

theorem namedLeaf112_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1392)) namedLeaf112 = true :=
  by decide +kernel

def namedLeaf113 : LeafData := { rows := ![![1, 2, 3, 5, 4, 6], ![0, 2, 5, 4, 3, 6], ![0, 1, 6, 5, 4, 3], ![0, 5, 4, 1, 6, 2], ![5, 0, 3, 1, 6, 2], ![4, 0, 3, 1, 6, 2], ![0, 1, 3, 4, 5, 2]], proof := .tail 56 }

theorem namedLeaf113_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1393)) namedLeaf113 = true :=
  by decide +kernel

def namedLeaf114 : LeafData := { rows := ![![1, 2, 3, 5, 4, 6], ![0, 2, 5, 4, 6, 3], ![0, 1, 5, 4, 6, 3], ![0, 5, 4, 6, 1, 2], ![5, 0, 3, 1, 2, 6], ![4, 0, 3, 1, 2, 6], ![0, 3, 1, 2, 4, 5]], proof := .low (![144, 77, 76, 117, 162, 161, 169, 42, 140, 98, 167, 60, 146, 139, 150, 96, 170, 17, 110, 145, 61, 133, 18, 13, 103, 4, 120, 135]) }

theorem namedLeaf114_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1394)) namedLeaf114 = true :=
  by decide +kernel

def namedLeaf115 : LeafData := { rows := ![![1, 2, 3, 5, 4, 6], ![0, 2, 5, 4, 6, 3], ![0, 1, 5, 6, 4, 3], ![0, 5, 4, 6, 1, 2], ![5, 0, 3, 1, 6, 2], ![4, 0, 3, 1, 2, 6], ![0, 3, 1, 4, 2, 5]], proof := .tail 79 }

theorem namedLeaf115_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1395)) namedLeaf115 = true :=
  by decide +kernel

def namedLeaf116 : LeafData := { rows := ![![1, 2, 3, 5, 4, 6], ![0, 2, 5, 4, 6, 3], ![0, 1, 6, 5, 4, 3], ![0, 5, 4, 6, 1, 2], ![5, 0, 3, 1, 6, 2], ![4, 0, 3, 1, 6, 2], ![0, 3, 1, 4, 5, 2]], proof := .tail 165 }

theorem namedLeaf116_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1396)) namedLeaf116 = true :=
  by decide +kernel

def namedLeaf117 : LeafData := { rows := ![![1, 2, 3, 5, 4, 6], ![0, 2, 5, 6, 4, 3], ![0, 1, 5, 6, 4, 3], ![0, 5, 4, 6, 1, 2], ![5, 0, 3, 6, 1, 2], ![4, 0, 3, 1, 2, 6], ![0, 3, 4, 1, 2, 5]], proof := .tail 27 }

theorem namedLeaf117_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1397)) namedLeaf117 = true :=
  by decide +kernel

def namedLeaf118 : LeafData := { rows := ![![1, 2, 3, 5, 4, 6], ![0, 2, 5, 6, 4, 3], ![0, 1, 6, 5, 4, 3], ![0, 5, 4, 6, 1, 2], ![5, 0, 3, 6, 1, 2], ![4, 0, 3, 1, 6, 2], ![0, 3, 4, 1, 5, 2]], proof := .tail 130 }

theorem namedLeaf118_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1398)) namedLeaf118 = true :=
  by decide +kernel

def namedLeaf119 : LeafData := { rows := ![![1, 2, 3, 5, 4, 6], ![0, 2, 6, 5, 4, 3], ![0, 1, 6, 5, 4, 3], ![0, 5, 4, 6, 1, 2], ![5, 0, 3, 6, 1, 2], ![4, 0, 3, 6, 1, 2], ![0, 3, 4, 5, 1, 2]], proof := .tail 64 }

theorem namedLeaf119_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1399)) namedLeaf119 = true :=
  by decide +kernel

def namedLeaf120 : LeafData := { rows := ![![1, 2, 3, 5, 4, 6], ![0, 6, 2, 5, 4, 3], ![0, 6, 1, 5, 4, 3], ![0, 5, 4, 6, 1, 2], ![5, 0, 3, 6, 1, 2], ![4, 0, 3, 6, 1, 2], ![0, 3, 4, 5, 2, 1]], proof := .tail 113 }

theorem namedLeaf120_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1400)) namedLeaf120 = true :=
  by decide +kernel

def namedLeaf121 : LeafData := { rows := ![![1, 2, 3, 5, 4, 6], ![0, 2, 5, 6, 4, 3], ![0, 1, 5, 6, 4, 3], ![0, 5, 6, 4, 1, 2], ![5, 0, 6, 3, 1, 2], ![4, 0, 3, 1, 2, 6], ![0, 4, 3, 1, 2, 5]], proof := .tail 37 }

theorem namedLeaf121_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1401)) namedLeaf121 = true :=
  by decide +kernel

def namedLeaf122 : LeafData := { rows := ![![1, 2, 3, 5, 4, 6], ![0, 2, 5, 6, 4, 3], ![0, 1, 6, 5, 4, 3], ![0, 5, 6, 4, 1, 2], ![5, 0, 6, 3, 1, 2], ![4, 0, 3, 1, 6, 2], ![0, 4, 3, 1, 5, 2]], proof := .tail 37 }

theorem namedLeaf122_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1402)) namedLeaf122 = true :=
  by decide +kernel

def namedLeaf123 : LeafData := { rows := ![![1, 2, 3, 5, 4, 6], ![0, 2, 6, 5, 4, 3], ![0, 1, 6, 5, 4, 3], ![0, 5, 6, 4, 1, 2], ![5, 0, 6, 3, 1, 2], ![4, 0, 3, 6, 1, 2], ![0, 4, 3, 5, 1, 2]], proof := .tail 37 }

theorem namedLeaf123_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1403)) namedLeaf123 = true :=
  by decide +kernel

def namedLeaf124 : LeafData := { rows := ![![1, 2, 3, 5, 4, 6], ![0, 2, 6, 5, 4, 3], ![0, 1, 6, 5, 4, 3], ![0, 6, 5, 4, 1, 2], ![5, 0, 6, 3, 1, 2], ![4, 0, 6, 3, 1, 2], ![0, 4, 5, 3, 1, 2]], proof := .tail 2 }

theorem namedLeaf124_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1404)) namedLeaf124 = true :=
  by decide +kernel

def namedLeaf125 : LeafData := { rows := ![![1, 2, 3, 5, 4, 6], ![0, 6, 2, 5, 4, 3], ![0, 6, 1, 5, 4, 3], ![0, 5, 6, 4, 1, 2], ![5, 0, 6, 3, 1, 2], ![4, 0, 3, 6, 1, 2], ![0, 4, 3, 5, 2, 1]], proof := .tail 87 }

theorem namedLeaf125_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1405)) namedLeaf125 = true :=
  by decide +kernel

def namedLeaf126 : LeafData := { rows := ![![1, 2, 3, 5, 4, 6], ![0, 6, 2, 5, 4, 3], ![0, 6, 1, 5, 4, 3], ![0, 6, 5, 4, 1, 2], ![5, 0, 6, 3, 1, 2], ![4, 0, 6, 3, 1, 2], ![0, 4, 5, 3, 2, 1]], proof := .tail 2 }

theorem namedLeaf126_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1406)) namedLeaf126 = true :=
  by decide +kernel

def namedLeaf127 : LeafData := { rows := ![![1, 2, 3, 5, 4, 6], ![0, 3, 5, 2, 4, 6], ![0, 3, 5, 1, 4, 6], ![0, 2, 1, 5, 4, 6], ![5, 0, 1, 2, 3, 6], ![4, 0, 2, 1, 3, 6], ![0, 1, 2, 3, 4, 5]], proof := .tail 12 }

theorem namedLeaf127_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1407)) namedLeaf127 = true :=
  by decide +kernel

def fallback : LeafData := { rows := fun _ _ => 0, proof := .tail 0 }
def lookup (offset : ℕ) : LeafData :=
  if offset < 128 then (if offset < 64 then (if offset < 32 then (if offset < 16 then (if offset < 8 then (if offset < 4 then (if offset < 2 then (if offset < 1 then (namedLeaf000) else (namedLeaf001)) else (if offset < 3 then (namedLeaf002) else (namedLeaf003))) else (if offset < 6 then (if offset < 5 then (namedLeaf004) else (namedLeaf005)) else (if offset < 7 then (namedLeaf006) else (namedLeaf007)))) else (if offset < 12 then (if offset < 10 then (if offset < 9 then (namedLeaf008) else (namedLeaf009)) else (if offset < 11 then (namedLeaf010) else (namedLeaf011))) else (if offset < 14 then (if offset < 13 then (namedLeaf012) else (namedLeaf013)) else (if offset < 15 then (namedLeaf014) else (namedLeaf015))))) else (if offset < 24 then (if offset < 20 then (if offset < 18 then (if offset < 17 then (namedLeaf016) else (namedLeaf017)) else (if offset < 19 then (namedLeaf018) else (namedLeaf019))) else (if offset < 22 then (if offset < 21 then (namedLeaf020) else (namedLeaf021)) else (if offset < 23 then (namedLeaf022) else (namedLeaf023)))) else (if offset < 28 then (if offset < 26 then (if offset < 25 then (namedLeaf024) else (namedLeaf025)) else (if offset < 27 then (namedLeaf026) else (namedLeaf027))) else (if offset < 30 then (if offset < 29 then (namedLeaf028) else (namedLeaf029)) else (if offset < 31 then (namedLeaf030) else (namedLeaf031)))))) else (if offset < 48 then (if offset < 40 then (if offset < 36 then (if offset < 34 then (if offset < 33 then (namedLeaf032) else (namedLeaf033)) else (if offset < 35 then (namedLeaf034) else (namedLeaf035))) else (if offset < 38 then (if offset < 37 then (namedLeaf036) else (namedLeaf037)) else (if offset < 39 then (namedLeaf038) else (namedLeaf039)))) else (if offset < 44 then (if offset < 42 then (if offset < 41 then (namedLeaf040) else (namedLeaf041)) else (if offset < 43 then (namedLeaf042) else (namedLeaf043))) else (if offset < 46 then (if offset < 45 then (namedLeaf044) else (namedLeaf045)) else (if offset < 47 then (namedLeaf046) else (namedLeaf047))))) else (if offset < 56 then (if offset < 52 then (if offset < 50 then (if offset < 49 then (namedLeaf048) else (namedLeaf049)) else (if offset < 51 then (namedLeaf050) else (namedLeaf051))) else (if offset < 54 then (if offset < 53 then (namedLeaf052) else (namedLeaf053)) else (if offset < 55 then (namedLeaf054) else (namedLeaf055)))) else (if offset < 60 then (if offset < 58 then (if offset < 57 then (namedLeaf056) else (namedLeaf057)) else (if offset < 59 then (namedLeaf058) else (namedLeaf059))) else (if offset < 62 then (if offset < 61 then (namedLeaf060) else (namedLeaf061)) else (if offset < 63 then (namedLeaf062) else (namedLeaf063))))))) else (if offset < 96 then (if offset < 80 then (if offset < 72 then (if offset < 68 then (if offset < 66 then (if offset < 65 then (namedLeaf064) else (namedLeaf065)) else (if offset < 67 then (namedLeaf066) else (namedLeaf067))) else (if offset < 70 then (if offset < 69 then (namedLeaf068) else (namedLeaf069)) else (if offset < 71 then (namedLeaf070) else (namedLeaf071)))) else (if offset < 76 then (if offset < 74 then (if offset < 73 then (namedLeaf072) else (namedLeaf073)) else (if offset < 75 then (namedLeaf074) else (namedLeaf075))) else (if offset < 78 then (if offset < 77 then (namedLeaf076) else (namedLeaf077)) else (if offset < 79 then (namedLeaf078) else (namedLeaf079))))) else (if offset < 88 then (if offset < 84 then (if offset < 82 then (if offset < 81 then (namedLeaf080) else (namedLeaf081)) else (if offset < 83 then (namedLeaf082) else (namedLeaf083))) else (if offset < 86 then (if offset < 85 then (namedLeaf084) else (namedLeaf085)) else (if offset < 87 then (namedLeaf086) else (namedLeaf087)))) else (if offset < 92 then (if offset < 90 then (if offset < 89 then (namedLeaf088) else (namedLeaf089)) else (if offset < 91 then (namedLeaf090) else (namedLeaf091))) else (if offset < 94 then (if offset < 93 then (namedLeaf092) else (namedLeaf093)) else (if offset < 95 then (namedLeaf094) else (namedLeaf095)))))) else (if offset < 112 then (if offset < 104 then (if offset < 100 then (if offset < 98 then (if offset < 97 then (namedLeaf096) else (namedLeaf097)) else (if offset < 99 then (namedLeaf098) else (namedLeaf099))) else (if offset < 102 then (if offset < 101 then (namedLeaf100) else (namedLeaf101)) else (if offset < 103 then (namedLeaf102) else (namedLeaf103)))) else (if offset < 108 then (if offset < 106 then (if offset < 105 then (namedLeaf104) else (namedLeaf105)) else (if offset < 107 then (namedLeaf106) else (namedLeaf107))) else (if offset < 110 then (if offset < 109 then (namedLeaf108) else (namedLeaf109)) else (if offset < 111 then (namedLeaf110) else (namedLeaf111))))) else (if offset < 120 then (if offset < 116 then (if offset < 114 then (if offset < 113 then (namedLeaf112) else (namedLeaf113)) else (if offset < 115 then (namedLeaf114) else (namedLeaf115))) else (if offset < 118 then (if offset < 117 then (namedLeaf116) else (namedLeaf117)) else (if offset < 119 then (namedLeaf118) else (namedLeaf119)))) else (if offset < 124 then (if offset < 122 then (if offset < 121 then (namedLeaf120) else (namedLeaf121)) else (if offset < 123 then (namedLeaf122) else (namedLeaf123))) else (if offset < 126 then (if offset < 125 then (namedLeaf124) else (namedLeaf125)) else (if offset < 127 then (namedLeaf126) else (namedLeaf127)))))))) else fallback

theorem point_checked (j : Fin 128) :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 (1280 + j.val))) (lookup j.val) = true := by
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

theorem correct (id : Fin 24698) (hlow : 1280 ≤ id.val) (hhigh : id.val < 1408) :
    leafCheck library (N4R2WordTree.catalog id) (lookup (id.val - 1280)) = true := by
  let j : Fin 128 := ⟨id.val - 1280, by omega⟩
  have hsum : 1280 + j.val = id.val := by dsimp [j]; omega
  have hindex : Fin.ofNat 24698 (1280 + j.val) = id := by
    apply Fin.ext
    simp only [Fin.ofNat, hsum, Nat.mod_eq_of_lt id.isLt]
  have hh := point_checked j
  rw [hindex] at hh
  exact hh

#print axioms point_checked
#print axioms correct
end Jsp404.N4R2OuterLeftData.LeafShard010
