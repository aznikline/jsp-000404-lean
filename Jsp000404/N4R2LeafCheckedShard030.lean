import Jsp000404.N4R2RowDataReplay
import Jsp000404.N4R2WordCatalog

set_option autoImplicit false
set_option pp.fullNames true
set_option maxRecDepth 8192
set_option maxHeartbeats 0

set_option Elab.async false

namespace Jsp404.N4R2ReplayData.LeafShard030
open N4R2RowDataReplay

-- Original cycle 004700f1bbc0e11966ea55f805fc6a92cb927007a74696aab6cbe928668fc10b; original global index 27.
def localCycle00000 : Cycle where
  length := 10
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 2, .distance 1 4, .distance 1 5, .distance 5 6, .distance 2 5, .distance 0 2, .distance 2 4, .distance 3 4, .theta 3]
    constant := ![3, -1, 0, 0, -1, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, false, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 0, .triangle 16 2, .triangle 22 2, .triangle 24 0, .triangle 30 0, .triangle 7 0, .triangle 6 0, .triangle 25 1, .corridorLower 3 4]

-- Original cycle 00532da2351c3b629ca85a37fa3c749cfe257bfd5103875283dcddf0e9af1eb6; original global index 31.
def localCycle00001 : Cycle where
  length := 5
  data := {
    node := ![.theta 3, .distance 2 3, .distance 0 2, .distance 2 6, .distance 3 6, .theta 3]
    constant := ![4, -1, -1, -2, -1]
    coefficient := ![1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false] }
  origin := ![.gapLower 3 6, .triangle 5 0, .triangle 8 0, .gapLower 6 2, .corridorLower 3 6]

-- Original cycle 006f4d17408a9903e4ffb5b1d036f017d2c47e3c668c3738da4ef8565725e35e; original global index 38.
def localCycle00002 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 2, .distance 0 2, .distance 2 6, .distance 3 6, .theta 6, .theta 5, .theta 4, .theta 3]
    constant := ![3, -1, 0, -1, 0, -2, 0, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, true, true, true] }
  origin := ![.corridorUpper 2 3, .triangle 15 0, .triangle 0 2, .triangle 8 0, .triangle 27 1, .gapLower 6 0, .thetaNext 5, .thetaNext 4, .thetaNext 3]

-- Original cycle 01054b0b46bf2fc811513642ea947eb9df0ffa3b8f1dbb903060b7f44d71d5c0; original global index 88.
def localCycle00003 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 0 3, .distance 0 5, .distance 0 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, 0, -1, -2, 0, 0, -2, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, true, true, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 11 0, .gapLower 0 4, .triangle 7 1, .triangle 0 1, .gapLower 0 0, .thetaLower 0]

-- Original cycle 02158ec39f60a45cbfb18d2d30387e66e4a2bdd223daf2fa879bd33376a0d780; original global index 170.
def localCycle00004 : Cycle where
  length := 8
  data := {
    node := ![.theta 5, .distance 4 5, .distance 2 5, .distance 0 2, .distance 0 6, .distance 2 6, .distance 3 6, .distance 5 6, .theta 5]
    constant := ![4, 0, -1, 0, -2, 0, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, true, false, false] }
  origin := ![.gapLower 5 6, .triangle 28 2, .triangle 7 0, .triangle 8 2, .gapLower 6 3, .triangle 27 1, .gapLower 6 1, .corridorLower 5 6]

-- Original cycle 0350a68a59e50ef306939f508f10d60c3f6d93f7685d52f1cc3ea7e53b8000cf; original global index 269.
def localCycle00005 : Cycle where
  length := 8
  data := {
    node := ![.theta 0, .distance 0 3, .distance 0 6, .distance 0 2, .distance 2 5, .distance 2 4, .theta 2, .theta 1, .theta 0]
    constant := ![2, 0, -2, -1, 0, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, false, true, true] }
  origin := ![.gapLower 0 6, .triangle 11 2, .gapLower 0 4, .triangle 7 0, .triangle 28 1, .corridorLower 2 4, .thetaNext 1, .thetaNext 0]

-- Original cycle 042884d5f59ef95284e265f760327336a46cb91f29f97d6cf532b75e6967a909; original global index 327.
def localCycle00006 : Cycle where
  length := 7
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 5, .distance 1 4, .distance 0 1, .theta 0, .zero]
    constant := ![0, 1, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 34 0, .triangle 22 0, .triangle 2 0, .corridorLower 0 1, .thetaLower 0]

-- Original cycle 044594e16d14629c3e77898154c5d50c30bc4f49c3d56d093ecaf6c1d869d223; original global index 336.
def localCycle00007 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 2 6, .distance 1 6, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, -2, 0, -2, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .gapLower 6 5, .triangle 29 2, .gapLower 6 3, .triangle 4 0, .corridorLower 0 1, .thetaLower 0]

-- Original cycle 072cb93e78baee4ee87b62d77404b3ba68eb48cb6d4b5843aac7d631bac59aac; original global index 594.
def localCycle00008 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 3, .distance 1 6, .distance 0 6, .distance 3 6, .distance 3 5, .distance 3 4, .theta 3]
    constant := ![3, 0, 0, -2, -2, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, true, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 2, .triangle 21 2, .gapLower 6 2, .gapLower 6 1, .triangle 33 1, .triangle 31 1, .corridorLower 3 4]

-- Original cycle 099db61be3001d672572f11df9f4870ea4a08a788b6b6f0b647d03792eed0c0a; original global index 766.
def localCycle00009 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 3, .distance 1 6, .distance 0 6, .distance 0 5, .distance 0 2, .distance 2 4, .distance 3 4, .theta 3]
    constant := ![3, 0, 0, -2, 0, 0, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, true, false, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 2, .triangle 21 2, .gapLower 6 2, .triangle 14 1, .triangle 7 1, .triangle 6 0, .triangle 25 1, .corridorLower 3 4]

-- Original cycle 09a4b9ed323886aa5eeb8a4528d0976dfc445dd2932b72ed8140d390c62328c0; original global index 769.
def localCycle00010 : Cycle where
  length := 6
  data := {
    node := ![.zero, .theta 0, .distance 0 3, .distance 3 5, .distance 5 6, .theta 5, .zero]
    constant := ![0, 1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.thetaUpper 0, .gapLower 0 6, .triangle 10 0, .triangle 33 0, .corridorLower 5 6, .thetaLower 5]

-- Original cycle 09c36ba8041788030b1f0443979f03cd6f2b2184207943993ef671de1abbcc1c; original global index 782.
def localCycle00011 : Cycle where
  length := 10
  data := {
    node := ![.theta 0, .distance 0 3, .distance 0 5, .distance 0 6, .distance 0 2, .distance 2 4, .distance 3 4, .theta 3, .theta 2, .theta 1, .theta 0]
    constant := ![2, 0, 0, -2, -1, 0, -1, 0, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, true, false, true, true, true] }
  origin := ![.gapLower 0 6, .triangle 10 2, .triangle 14 2, .gapLower 0 3, .triangle 6 0, .triangle 25 1, .corridorLower 3 4, .thetaNext 2, .thetaNext 1, .thetaNext 0]

-- Original cycle 0c41d1b8d27ab375f1927ec2f5b201dd23e873a219296372c7e5410f476c7141; original global index 967.
def localCycle00012 : Cycle where
  length := 10
  data := {
    node := ![.theta 3, .distance 3 6, .distance 2 3, .distance 1 2, .distance 1 4, .distance 4 5, .distance 2 5, .distance 0 2, .distance 2 4, .distance 3 4, .theta 3]
    constant := ![4, -1, -1, 0, -1, 0, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true, false, false, true, false] }
  origin := ![.gapLower 3 6, .triangle 27 0, .triangle 15 0, .triangle 16 2, .triangle 22 0, .triangle 28 2, .triangle 7 0, .triangle 6 0, .triangle 25 1, .corridorLower 3 4]

-- Original cycle 0c76cefa88b8ad236148f1cbfc10c8bca5ea361acac8b9048cb41ee58a90fe9a; original global index 987.
def localCycle00013 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 2 3, .distance 0 2, .distance 0 5, .distance 0 4, .distance 4 6, .distance 3 4, .theta 3]
    constant := ![3, -1, 0, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 5 0, .triangle 7 2, .triangle 12 1, .triangle 13 0, .triangle 32 0, .corridorLower 3 4]

-- Original cycle 0ceead8a80a7fcc29d87dcd9bd561e2c20c15754524458f25027e6c3aa284030; original global index 1018.
def localCycle00014 : Cycle where
  length := 8
  data := {
    node := ![.theta 5, .distance 4 5, .distance 2 5, .distance 0 2, .distance 2 6, .distance 3 6, .distance 5 6, .theta 6, .theta 5]
    constant := ![3, 0, -1, -1, 0, 0, -2, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, true, false, true] }
  origin := ![.corridorUpper 4 5, .triangle 28 2, .triangle 7 0, .triangle 8 0, .triangle 27 1, .triangle 33 1, .gapLower 6 0, .thetaNext 5]

-- Original cycle 0d45a6143f79a0bdb1b9134c819d72f9aa4e986dbec25421be8440a6776d55b3; original global index 1050.
def localCycle00015 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 2, .distance 1 6, .distance 0 6, .distance 2 6, .distance 3 6, .theta 3]
    constant := ![4, -1, 0, -2, 0, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false] }
  origin := ![.gapLower 3 6, .triangle 15 0, .triangle 18 2, .gapLower 6 3, .triangle 8 1, .gapLower 6 1, .corridorLower 3 6]

-- Original cycle 0ea91a5f57c7c55437bb56b2b561f869eabd4d48c599bcbaad32e4f76007ffa1; original global index 1158.
def localCycle00016 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 2, .distance 1 4, .distance 4 6, .distance 2 6, .distance 5 6, .distance 3 5, .distance 3 4, .theta 3]
    constant := ![3, -1, 0, -1, 0, 0, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, true, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 0, .triangle 16 2, .triangle 23 0, .triangle 29 2, .triangle 30 1, .triangle 33 0, .gapLower 3 1, .corridorLower 3 4]

-- Original cycle 0fedceaeeeb7d6467649b845eb439552cd023f71201014fb69ecfed14add1bdc; original global index 1270.
def localCycle00017 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 2, .distance 0 5, .distance 2 5, .distance 3 5, .distance 0 3, .distance 0 2]
    constant := ![-2, 0, 0, 2, -2]
    coefficient := ![0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false] }
  origin := ![.gapLower 0 3, .gapLower 5 2, .triangle 26 1, .gapUpper 3 2, .gapLower 0 4]

-- Original cycle 104f986533abe7e4c62105726070bc7e317ccd3db353f63c98d39ca6cb2e862b; original global index 1312.
def localCycle00018 : Cycle where
  length := 6
  data := {
    node := ![.theta 3, .distance 2 3, .distance 0 2, .distance 2 6, .distance 3 6, .distance 3 4, .theta 3]
    constant := ![3, -1, -1, -3, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 5 0, .triangle 8 0, .gapLower 6 2, .triangle 32 1, .corridorLower 3 4]

-- Original cycle 106b818db01f92421483719b258efe546ad9a83f04d4d114528d8c7d9010ee33; original global index 1318.
def localCycle00019 : Cycle where
  length := 4
  data := {
    node := ![.distance 1 4, .distance 4 6, .distance 5 6, .distance 1 6, .distance 1 4]
    constant := ![2, -2, -2, 0]
    coefficient := ![0, 0, 0, 0]
    strict := ![true, false, false, true] }
  origin := ![.gapUpper 4 4, .gapLower 6 5, .gapLower 6 4, .triangle 23 1]

-- Original cycle 10ec6f1e937d34eb73a5abed77b10132fb7a5e7f064560d4945c7d1fe5bd6cb3; original global index 1358.
def localCycle00020 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 2 3, .distance 0 2, .distance 0 5, .distance 0 4, .theta 0, .zero]
    constant := ![0, 3, 0, 0, -1, -1, -2, -2, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 27 0, .triangle 5 0, .gapLower 0 3, .gapLower 0 2, .corridorLower 0 4, .thetaLower 0]

-- Original cycle 158425e14f1803757b68c96a99eacef2a8debdba2864f133d1ce7ba41d832f94; original global index 1705.
def localCycle00021 : Cycle where
  length := 5
  data := {
    node := ![.theta 3, .distance 2 3, .distance 0 2, .distance 2 6, .distance 3 6, .theta 3]
    constant := ![3, -1, -1, -2, -1]
    coefficient := ![1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 5 0, .triangle 8 0, .gapLower 6 2, .corridorLower 3 6]

-- Original cycle 15c826fd164c9202afdce712074a2d14dda88169e6a6b3785755d572cb2eeeb6; original global index 1730.
def localCycle00022 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 3 6, .distance 2 3, .distance 1 2, .distance 2 5, .distance 0 2, .distance 2 4, .distance 3 4, .theta 3]
    constant := ![4, -1, -1, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, false] }
  origin := ![.gapLower 3 6, .triangle 27 0, .triangle 15 0, .triangle 17 0, .triangle 7 0, .triangle 6 0, .triangle 25 1, .corridorLower 3 4]

-- Original cycle 169d69347696d31d7fe1d36b8aa9023e590e34f386d482f3bccfcf14596a2120; original global index 1773.
def localCycle00023 : Cycle where
  length := 12
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 2, .distance 1 4, .distance 4 5, .distance 2 5, .distance 5 6, .distance 3 5, .distance 0 3, .distance 0 2, .distance 2 4, .distance 3 4, .theta 3]
    constant := ![3, -1, 0, -1, 0, -1, -1, -1, 0, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false, false, true, false, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 0, .triangle 16 2, .triangle 22 0, .triangle 28 2, .triangle 30 0, .triangle 33 0, .triangle 10 0, .triangle 5 1, .triangle 6 0, .triangle 25 1, .corridorLower 3 4]

-- Original cycle 170089a41121d67233e352fea47ed3f2938f7d9704c75bb7472b1a8307445dec; original global index 1810.
def localCycle00024 : Cycle where
  length := 8
  data := {
    node := ![.theta 5, .distance 4 5, .distance 2 5, .distance 0 2, .distance 2 6, .distance 3 6, .distance 5 6, .theta 6, .theta 5]
    constant := ![3, 0, -1, -1, -2, 0, -2, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, true, false, true] }
  origin := ![.corridorUpper 4 5, .triangle 28 2, .triangle 7 0, .triangle 8 0, .gapLower 6 2, .triangle 33 1, .gapLower 6 0, .thetaNext 5]

-- Original cycle 1720a4d2e856b6ee3ed82df6be05cb22efeb2e54213981cacb76d113e0513cd2; original global index 1816.
def localCycle00025 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 2 3, .distance 0 2, .distance 0 4, .theta 0, .zero]
    constant := ![0, 3, 0, 0, -1, -1, -2, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 27 0, .triangle 5 0, .gapLower 0 2, .corridorLower 0 4, .thetaLower 0]

-- Original cycle 17271d23212215a5aec942963ea36c72e11b36c6f3b70eaed6df7d515c264a63; original global index 1819.
def localCycle00026 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 2 6, .distance 1 2, .distance 0 2, .distance 2 5, .distance 3 5, .distance 3 4, .theta 3, .zero]
    constant := ![0, 2, 0, -2, -1, 0, -1, 0, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, false, true, true, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 34 2, .gapLower 6 4, .triangle 18 0, .triangle 0 2, .triangle 7 0, .triangle 26 1, .triangle 31 1, .corridorLower 3 4, .thetaLower 3]

-- Original cycle 1758d953c2ca99ce9d15f538661ff5bb982362b247b984c7fb614b378bf4ab64; original global index 1833.
def localCycle00027 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 2, .distance 0 2, .distance 2 6, .distance 3 6, .theta 6, .theta 5, .theta 4, .theta 3]
    constant := ![3, -1, 0, -1, 0, -3, 0, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, true, true, true] }
  origin := ![.corridorUpper 2 3, .triangle 15 0, .triangle 0 2, .triangle 8 0, .triangle 27 1, .gapLower 6 0, .thetaNext 5, .thetaNext 4, .thetaNext 3]

-- Original cycle 17a30ecf554450e52e9419f5e83d679aeb88e96636b8da6bc9e29f02bb3c9e85; original global index 1848.
def localCycle00028 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 0 3, .distance 0 5, .distance 0 2, .distance 2 4, .distance 3 4, .theta 3, .zero]
    constant := ![0, 3, 0, 0, -1, -2, -2, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, false, true, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 11 0, .gapLower 0 4, .gapLower 0 3, .triangle 6 0, .triangle 25 1, .corridorLower 3 4, .thetaLower 3]

-- Original cycle 1880874a7d61d393315dd08452a7512be95b1020859c8ea969f0ac154bba1ec5; original global index 1918.
def localCycle00029 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 2, .distance 1 6, .distance 0 6, .distance 2 6, .distance 3 6, .theta 3]
    constant := ![4, -1, 0, -2, 0, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false] }
  origin := ![.gapLower 3 6, .triangle 15 0, .triangle 18 2, .gapLower 6 4, .triangle 8 1, .gapLower 6 2, .corridorLower 3 6]

-- Original cycle 18f6e5ba495f20ae1b6f1fd70b5e0570dfff0912923b99cebd5b2114c1e6799b; original global index 1949.
def localCycle00030 : Cycle where
  length := 11
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 3, .distance 1 5, .distance 5 6, .distance 3 6, .distance 0 3, .distance 0 5, .distance 0 2, .distance 2 4, .distance 3 4, .theta 3]
    constant := ![3, 0, 0, -1, 0, -1, 0, 0, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, true, true, false, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 2, .triangle 20 2, .triangle 24 0, .triangle 33 2, .triangle 11 0, .triangle 10 2, .triangle 7 1, .triangle 6 0, .triangle 25 1, .corridorLower 3 4]

-- Original cycle 19972c3ed238ffa8064bb2224fbc7b9d13a43c9fd2d0bd5ff01e9ac2bf4c2a34; original global index 1998.
def localCycle00031 : Cycle where
  length := 6
  data := {
    node := ![.theta 3, .distance 2 3, .distance 0 2, .distance 0 6, .distance 2 6, .distance 3 6, .theta 3]
    constant := ![4, -1, 0, -2, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false] }
  origin := ![.gapLower 3 6, .triangle 5 0, .triangle 8 2, .gapLower 6 3, .gapLower 6 2, .corridorLower 3 6]

-- Original cycle 19a1f24e9cbf10dacf099fa784239836654b92f049e9885a42465bbcf2cd9c82; original global index 2004.
def localCycle00032 : Cycle where
  length := 14
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 2 6, .distance 1 6, .distance 0 6, .distance 0 3, .distance 0 2, .distance 2 4, .distance 3 4, .theta 3, .theta 2, .zero]
    constant := ![0, 3, 0, 0, 0, 0, 0, -3, 0, -1, 0, -1, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, true, true, true, false, true, false, true, false, true, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 27 2, .triangle 18 2, .triangle 4 2, .gapLower 0 5, .triangle 5 1, .triangle 6 0, .triangle 25 1, .corridorLower 3 4, .thetaNext 2, .thetaLower 2]

-- Original cycle 1a76b7da30322802c0cd843a4e381ccaba485a5d971f129786c78e5b312744b6; original global index 2059.
def localCycle00033 : Cycle where
  length := 9
  data := {
    node := ![.theta 0, .distance 0 3, .distance 0 5, .distance 0 2, .distance 2 4, .distance 3 4, .theta 3, .theta 2, .theta 1, .theta 0]
    constant := ![2, -2, 0, -1, 0, -1, 0, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, true, true, true] }
  origin := ![.gapLower 0 6, .gapLower 0 5, .triangle 7 1, .triangle 6 0, .triangle 25 1, .corridorLower 3 4, .thetaNext 2, .thetaNext 1, .thetaNext 0]

-- Original cycle 1a8150f8ae60cbb920f5924a6a824d107662c2284ca32c1ade963a3306c80072; original global index 2063.
def localCycle00034 : Cycle where
  length := 4
  data := {
    node := ![.distance 0 2, .distance 2 5, .distance 3 5, .distance 0 3, .distance 0 2]
    constant := ![0, 0, 2, -3]
    coefficient := ![0, 0, 0, 0]
    strict := ![false, false, true, false] }
  origin := ![.gapLower 2 2, .gapLower 5 1, .gapUpper 3 2, .gapLower 0 4]

-- Original cycle 1aed3ed4c3b59975938f8ed1c3c138e302253cd7a6805524b1526fc2c836b498; original global index 2088.
def localCycle00035 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 3, .distance 1 6, .distance 0 6, .distance 0 2, .distance 2 5, .distance 3 5, .distance 3 4, .theta 3]
    constant := ![3, 0, 0, -3, 0, -1, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, true, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 2, .triangle 21 2, .gapLower 6 2, .triangle 8 1, .triangle 7 0, .triangle 26 1, .triangle 31 1, .corridorLower 3 4]

-- Original cycle 1b1a9d2845df446e9c58cbf5d774fa8041aa5d257436c75dfa0aa4b5eb56415d; original global index 2095.
def localCycle00036 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 2, .distance 1 4, .distance 4 5, .distance 0 4, .distance 4 6, .distance 3 4, .theta 3]
    constant := ![3, -1, 0, -1, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 0, .triangle 16 2, .triangle 22 0, .triangle 12 0, .triangle 13 0, .triangle 32 0, .corridorLower 3 4]

-- Original cycle 1cf1d400b05b58659818efdf5489916756ac8d984ddf6fc309c3e83b0c31affc; original global index 2232.
def localCycle00037 : Cycle where
  length := 7
  data := {
    node := ![.theta 6, .distance 5 6, .distance 4 6, .distance 2 6, .distance 1 6, .distance 0 6, .distance 3 6, .theta 6]
    constant := ![3, 0, 0, 0, -2, 0, -2]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, true, false] }
  origin := ![.corridorUpper 5 6, .triangle 34 2, .triangle 29 2, .triangle 18 2, .gapLower 6 2, .triangle 11 1, .gapLower 6 0]

-- Original cycle 1d7ec35059c3f93fdb6419adb6724f638728d658f0ed107ba62ccdb351ca52fe; original global index 2270.
def localCycle00038 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 3, .distance 0 3, .distance 0 6, .distance 0 2, .distance 2 5, .distance 3 5, .distance 3 4, .theta 3]
    constant := ![3, 0, 0, 0, -3, -1, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, false, true, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 2, .triangle 1 2, .triangle 11 2, .gapLower 0 4, .triangle 7 0, .triangle 26 1, .triangle 31 1, .corridorLower 3 4]

-- Original cycle 1ddbc3ac83ef2889f9e436ae0414e751fa4383b11246320960b3a7ffdcd0402c; original global index 2292.
def localCycle00039 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 0 2, .distance 0 4, .distance 4 6, .distance 2 6, .distance 5 6, .distance 3 5, .distance 3 4, .theta 3]
    constant := ![3, -1, 0, -1, 0, 0, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, true, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 5 0, .triangle 6 2, .triangle 13 0, .triangle 29 2, .triangle 30 1, .triangle 33 0, .gapLower 3 1, .corridorLower 3 4]

-- Original cycle 205eb4e6b00eacae66ee47db95855bd1c2689f009271c158f72c2f2e4cbd2067; original global index 2484.
def localCycle00040 : Cycle where
  length := 8
  data := {
    node := ![.theta 0, .distance 0 6, .distance 0 3, .distance 0 2, .distance 2 5, .distance 2 4, .theta 2, .theta 1, .theta 0]
    constant := ![2, -2, 0, -1, 0, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, true, true] }
  origin := ![.gapLower 0 6, .gapLower 0 5, .triangle 5 1, .triangle 7 0, .triangle 28 1, .corridorLower 2 4, .thetaNext 1, .thetaNext 0]

-- Original cycle 21cbb5236a391de8c73af50b759953ef2cb65e3667e65ef80a37a92d2c328d7c; original global index 2592.
def localCycle00041 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 3, .distance 0 3, .distance 0 6, .distance 0 2, .distance 2 5, .distance 3 5, .distance 3 4, .theta 3]
    constant := ![3, 0, 0, -2, -2, -1, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, false, true, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 2, .triangle 1 2, .gapLower 0 5, .gapLower 0 4, .triangle 7 0, .triangle 26 1, .triangle 31 1, .corridorLower 3 4]

-- Original cycle 22b2a17829db1f8c1187d53aed8488eaa38e698b7a3f6c81ca65965e2a64cd3d; original global index 2660.
def localCycle00042 : Cycle where
  length := 6
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 2, .distance 1 4, .distance 4 6, .distance 3 4, .theta 3]
    constant := ![3, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 0, .triangle 16 2, .triangle 23 0, .triangle 32 0, .corridorLower 3 4]

-- Original cycle 23a879058e0980002ddcb77046bcf57acc69e4e47c5fc40b659af2fe4b280596; original global index 2734.
def localCycle00043 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 2, .distance 1 4, .distance 4 6, .distance 2 6, .distance 0 2, .distance 2 4, .distance 3 4, .theta 3]
    constant := ![3, -1, 0, -1, 0, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 0, .triangle 16 2, .triangle 23 0, .triangle 29 2, .triangle 8 0, .triangle 6 0, .triangle 25 1, .corridorLower 3 4]

-- Original cycle 24372931e98539573ab15fdc21b84d2402350a9a7032255beb23635733ba93a6; original global index 2776.
def localCycle00044 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 0 2, .distance 2 6, .distance 3 6, .theta 6, .distance 5 6, .distance 4 6, .theta 4, .theta 3]
    constant := ![3, -1, -1, 0, -2, 3, -2, -2, 0]
    coefficient := ![1, 0, 0, 0, 0, 1, 0, -1, 0]
    strict := ![false, false, false, true, false, false, false, true, true] }
  origin := ![.corridorUpper 2 3, .triangle 5 0, .triangle 8 0, .triangle 27 1, .gapLower 6 0, .corridorUpper 5 6, .gapLower 6 5, .gapUpper 4 6, .thetaNext 3]

-- Original cycle 2445a959791e37d927413fbb7d556e42a3d04cb3be8d14ce961d3b83f87b4774; original global index 2781.
def localCycle00045 : Cycle where
  length := 5
  data := {
    node := ![.theta 3, .distance 2 3, .distance 0 2, .distance 2 6, .distance 3 6, .theta 3]
    constant := ![3, -1, -1, -2, -1]
    coefficient := ![1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 5 0, .triangle 8 0, .gapLower 6 1, .corridorLower 3 6]

-- Original cycle 24d35c5c4c5a275ead90bf0767966da06ea40449039329e40fd39dbcfa0e9ed1; original global index 2824.
def localCycle00046 : Cycle where
  length := 7
  data := {
    node := ![.zero, .theta 3, .distance 2 3, .distance 0 2, .distance 0 4, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, -1, -2, -2, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 3, .corridorUpper 2 3, .triangle 5 0, .gapLower 0 2, .gapLower 0 1, .corridorLower 0 1, .thetaLower 0]

-- Original cycle 26c09d81e705c60d1649f6c6e63dafabebf41213ac49899d10b13b9b9a3f6550; original global index 2969.
def localCycle00047 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 2 3, .distance 0 2, .distance 0 5, .distance 5 6, .distance 3 5, .distance 3 4, .theta 3]
    constant := ![3, -1, 0, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 5 0, .triangle 7 2, .triangle 14 0, .triangle 33 0, .gapLower 3 1, .corridorLower 3 4]

-- Original cycle 271b541ecf3783c8097e5bc7c12312575db7b8ae76f134d5881f7ee438c35dca; original global index 2996.
def localCycle00048 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 2 3, .distance 0 2, .distance 0 5, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, 0, -1, -1, -2, 0, -2, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, true, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 27 0, .triangle 5 0, .gapLower 0 3, .triangle 3 1, .gapLower 0 0, .thetaLower 0]

-- Original cycle 299c772ac87eae3815d53008f653608209f713e349a2e6a3bc221c7edfadc84a; original global index 3178.
def localCycle00049 : Cycle where
  length := 3
  data := {
    node := ![.distance 0 3, .distance 0 6, .distance 3 6, .distance 0 3]
    constant := ![-2, 0, 2]
    coefficient := ![0, 0, 0]
    strict := ![false, true, true] }
  origin := ![.gapLower 0 5, .triangle 11 1, .gapUpper 3 3]

-- Original cycle 2b54750b76dddcdb8a3bfb854ab2b19505022b17d52079f9e3b6ef0e7fe97ed5; original global index 3312.
def localCycle00050 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 2 3, .distance 0 2, .distance 0 4, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, 0, -1, -1, -2, 0, -2, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, true, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 27 0, .triangle 5 0, .gapLower 0 2, .triangle 2 1, .gapLower 0 0, .thetaLower 0]

-- Original cycle 2bc035707a4f47c9e1625f22e3d94e7720da394db022dc50f6b0e14212f33821; original global index 3343.
def localCycle00051 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 2 3, .distance 0 2, .distance 0 5, .distance 0 4, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, 0, -1, -1, 0, -2, 0, -2, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, true, false, true, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 27 0, .triangle 5 0, .triangle 7 2, .gapLower 0 2, .triangle 2 1, .gapLower 0 0, .thetaLower 0]

-- Original cycle 2c54a36db1b539a0d9d03a8239e0905ea9b91276406b6a439e563d35faf6c15f; original global index 3389.
def localCycle00052 : Cycle where
  length := 10
  data := {
    node := ![.theta 0, .distance 0 3, .distance 0 5, .distance 0 6, .distance 0 2, .distance 2 4, .distance 3 4, .theta 3, .theta 2, .theta 1, .theta 0]
    constant := ![2, 0, -2, 0, -1, 0, -1, 0, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, true, false, true, true, true] }
  origin := ![.gapLower 0 6, .triangle 10 2, .gapLower 0 4, .triangle 8 1, .triangle 6 0, .triangle 25 1, .corridorLower 3 4, .thetaNext 2, .thetaNext 1, .thetaNext 0]

-- Original cycle 2cf293a803041109e3e835453d340fa97188d54ad94b3e58005ce2b328ea1634; original global index 3433.
def localCycle00053 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 2 6, .distance 1 6, .distance 0 6, .distance 0 2, .distance 2 4, .distance 3 4, .theta 3]
    constant := ![3, 0, -3, 0, 0, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, true, false, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 27 2, .gapLower 6 3, .triangle 4 2, .triangle 8 1, .triangle 6 0, .triangle 25 1, .corridorLower 3 4]

-- Original cycle 2eb4dc88f13e6f2ccdec9b2b150860b4a282f26d14dba249c1ca4ffc22d562ea; original global index 3574.
def localCycle00054 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 2 3, .distance 0 2, .distance 0 5, .theta 0, .zero]
    constant := ![0, 3, 0, 0, -1, -1, -2, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 27 0, .triangle 5 0, .gapLower 0 3, .corridorLower 0 5, .thetaLower 0]

-- Original cycle 30874a802b0febf9c838bf844e07b6f4c48edb524a4a34e5950f02684bdc35af; original global index 3695.
def localCycle00055 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 2, .distance 2 4, .distance 3 4, .distance 3 5, .distance 0 5, .distance 0 2]
    constant := ![-1, 0, 2, 2, -3]
    coefficient := ![0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false] }
  origin := ![.triangle 6 0, .triangle 25 1, .gapUpper 3 1, .gapUpper 5 1, .gapLower 0 3]

-- Original cycle 31a4541670779029f23ec38daf441ffac7289bdac63c8e6178db5de9439d347b; original global index 3793.
def localCycle00056 : Cycle where
  length := 14
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 5 6, .distance 3 6, .distance 2 3, .distance 1 2, .distance 0 2, .distance 2 4, .distance 3 4, .theta 3, .theta 2, .theta 1, .theta 0, .zero]
    constant := ![0, 3, -1, 0, -1, -1, 0, -1, 0, -1, 0, 0, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, true, false, true, false, true, true, true, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 34 0, .triangle 33 2, .triangle 27 0, .triangle 15 0, .triangle 0 2, .triangle 6 0, .triangle 25 1, .corridorLower 3 4, .thetaNext 2, .thetaNext 1, .thetaNext 0, .thetaLower 0]

-- Original cycle 31cb04dda61c0e92e4b4f807b7749c1f4c360c7668d462c8bc5e408d8023d721; original global index 3803.
def localCycle00057 : Cycle where
  length := 7
  data := {
    node := ![.theta 6, .distance 5 6, .distance 4 6, .distance 2 6, .distance 1 6, .distance 0 6, .distance 3 6, .theta 6]
    constant := ![3, 0, 0, -2, 0, 0, -2]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, true, false] }
  origin := ![.corridorUpper 5 6, .triangle 34 2, .triangle 29 2, .gapLower 6 3, .triangle 4 2, .triangle 11 1, .gapLower 6 0]

-- Original cycle 331edeec07565b3c43ea839a6a97c2125e6f158d569d34cb8edef5e3fd7014df; original global index 3913.
def localCycle00058 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 2, .distance 2 5, .distance 0 2, .distance 0 4, .distance 4 6, .distance 3 4, .theta 3]
    constant := ![3, -1, -1, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 0, .triangle 17 0, .triangle 7 0, .triangle 6 2, .triangle 13 0, .triangle 32 0, .corridorLower 3 4]

-- Original cycle 344d1fab058faf1f14b5db863d2537e416c15f3c5d877ca9adfe2719b7e9f3b4; original global index 4011.
def localCycle00059 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 2, .distance 2 5, .distance 0 2, .distance 2 6, .distance 5 6, .distance 3 5, .distance 3 4, .theta 3]
    constant := ![3, -1, -1, -1, -1, 0, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 0, .triangle 17 0, .triangle 7 0, .triangle 8 0, .triangle 30 1, .triangle 33 0, .gapLower 3 1, .corridorLower 3 4]

-- Original cycle 3497e095e04ba7a318eec98c8b59c230c242bc9c8d8d955c0c451a7d5bcbddb4; original global index 4027.
def localCycle00060 : Cycle where
  length := 11
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 2, .distance 1 4, .distance 4 6, .distance 2 6, .distance 5 6, .distance 0 5, .distance 0 2, .distance 2 4, .distance 3 4, .theta 3]
    constant := ![3, -1, 0, -1, 0, 0, -1, 0, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, true, false, true, false, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 0, .triangle 16 2, .triangle 23 0, .triangle 29 2, .triangle 30 1, .triangle 14 0, .triangle 7 1, .triangle 6 0, .triangle 25 1, .corridorLower 3 4]

-- Original cycle 34f6ffc5e5e897bb5f36aca05fb0417ee8116226c461834ef719d3d1d9aa5ba1; original global index 4053.
def localCycle00061 : Cycle where
  length := 13
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 3, .distance 0 3, .distance 3 6, .theta 6, .distance 5 6, .distance 4 6, .distance 2 6, .distance 0 2, .distance 2 5, .distance 3 5, .distance 3 4, .theta 3]
    constant := ![3, 0, 0, -1, -2, 3, -2, 0, -1, -1, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, false, false, true, false, false, true, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 2, .triangle 1 2, .triangle 11 0, .gapLower 6 0, .corridorUpper 5 6, .gapLower 6 5, .triangle 29 2, .triangle 8 0, .triangle 7 0, .triangle 26 1, .triangle 31 1, .corridorLower 3 4]

-- Original cycle 376affd7a3ccf530612b69f6903b19c90faad80fb616b20a5f6dda801de324c7; original global index 4258.
def localCycle00062 : Cycle where
  length := 9
  data := {
    node := ![.theta 5, .distance 4 5, .distance 2 5, .distance 1 2, .distance 1 6, .distance 0 6, .distance 2 6, .distance 3 6, .distance 5 6, .theta 5]
    constant := ![4, 0, -1, 0, -2, 0, 0, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, true, true, false, false] }
  origin := ![.gapLower 5 6, .triangle 28 2, .triangle 17 0, .triangle 18 2, .gapLower 6 4, .triangle 8 1, .triangle 27 1, .gapLower 6 1, .corridorLower 5 6]

-- Original cycle 3855b8f8cc1ce8fdd72394704f282a8b83ece8ee67ecb6fd5f7626a5848e640c; original global index 4328.
def localCycle00063 : Cycle where
  length := 4
  data := {
    node := ![.distance 0 2, .distance 2 5, .distance 3 5, .distance 0 3, .distance 0 2]
    constant := ![-1, 0, 2, -2]
    coefficient := ![0, 0, 0, 0]
    strict := ![false, true, true, false] }
  origin := ![.triangle 7 0, .triangle 26 1, .gapUpper 3 2, .gapLower 0 4]

-- Original cycle 38762fa6742ca3cf57f9f6104c68ec2c510d65e3e7205f9704fc6bfa6bc8b483; original global index 4346.
def localCycle00064 : Cycle where
  length := 11
  data := {
    node := ![.theta 3, .distance 2 3, .distance 2 5, .distance 5 6, .distance 3 6, .distance 1 3, .distance 0 3, .distance 0 5, .distance 0 2, .distance 2 4, .distance 3 4, .theta 3]
    constant := ![3, 0, -1, 0, -1, 0, 0, 0, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, true, true, true, false, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 26 2, .triangle 30 0, .triangle 33 2, .triangle 21 0, .triangle 1 2, .triangle 10 2, .triangle 7 1, .triangle 6 0, .triangle 25 1, .corridorLower 3 4]

-- Original cycle 393655b19280e35bb2f95eea8dd8ccfad106af15456e9d90907c7b97eeed583c; original global index 4402.
def localCycle00065 : Cycle where
  length := 6
  data := {
    node := ![.zero, .theta 6, .distance 4 6, .distance 1 4, .distance 0 1, .theta 0, .zero]
    constant := ![0, 1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 23 0, .triangle 2 0, .corridorLower 0 1, .thetaLower 0]

-- Original cycle 393f5dce4c35096d60baa06bd8dfa71374b39ca36f6518231c17a82160d4651c; original global index 4404.
def localCycle00066 : Cycle where
  length := 3
  data := {
    node := ![.distance 4 5, .distance 5 6, .distance 4 6, .distance 4 5]
    constant := ![2, -3, 0]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.gapUpper 5 5, .gapLower 6 5, .triangle 34 1]

-- Original cycle 3be1738c091ede30b9c3be14e9ac957e0bdf29e57a726e7d79980bfbff96e6c3; original global index 4637.
def localCycle00067 : Cycle where
  length := 7
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 0 5, .distance 0 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, -1, -2, 0, -2, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 14 0, .gapLower 0 3, .triangle 0 1, .gapLower 0 0, .thetaLower 0]

-- Original cycle 3bfb26902e72f2fe3fa475d0cbb270d8e6a2169c620b9b051a08dcf468bd26d4; original global index 4648.
def localCycle00068 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 1 6, .distance 1 5, .distance 1 4, .distance 0 1, .theta 0, .zero]
    constant := ![0, 2, 0, -2, 0, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, true, false, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 34 2, .gapLower 6 4, .triangle 24 1, .triangle 22 1, .triangle 2 0, .corridorLower 0 1, .thetaLower 0]

-- Original cycle 3c254f0afacdd19d26d4ffaa20169019d095a3cdc671f42cd75f9886c4904235; original global index 4663.
def localCycle00069 : Cycle where
  length := 11
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 2, .distance 1 4, .distance 4 5, .distance 2 5, .distance 0 2, .distance 2 6, .distance 5 6, .distance 3 5, .distance 3 4, .theta 3]
    constant := ![3, -1, 0, -1, 0, -1, -1, 0, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false, true, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 0, .triangle 16 2, .triangle 22 0, .triangle 28 2, .triangle 7 0, .triangle 8 0, .triangle 30 1, .triangle 33 0, .gapLower 3 1, .corridorLower 3 4]

-- Original cycle 3c41e8b4f243079cef5dc76bd253b325808b695c71cd880761417ed98fe0ccda; original global index 4674.
def localCycle00070 : Cycle where
  length := 3
  data := {
    node := ![.distance 0 3, .distance 0 6, .distance 3 6, .distance 0 3]
    constant := ![-3, 0, 2]
    coefficient := ![0, 0, 0]
    strict := ![false, true, true] }
  origin := ![.gapLower 0 5, .triangle 11 1, .gapUpper 3 3]

-- Original cycle 3cd3c012eab829b213370bfbd01f8840304647e5f51644a82d6ccaaa9fa7920b; original global index 4716.
def localCycle00071 : Cycle where
  length := 13
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 2 6, .distance 1 6, .distance 0 6, .distance 0 3, .distance 0 2, .distance 0 5, .distance 0 4, .theta 0, .zero]
    constant := ![0, 3, 0, 0, 0, 0, 0, -2, 0, 0, -2, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, true, true, true, false, true, true, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 27 2, .triangle 18 2, .triangle 4 2, .gapLower 0 5, .triangle 5 1, .triangle 7 2, .gapLower 0 2, .corridorLower 0 4, .thetaLower 0]

-- Original cycle 3df61a2bd23dbcad60b3740e70c41c2216543cd8bd994eef111ca881e3194663; original global index 4793.
def localCycle00072 : Cycle where
  length := 10
  data := {
    node := ![.theta 3, .distance 2 3, .distance 2 5, .distance 5 6, .distance 3 6, .distance 0 3, .distance 0 5, .distance 0 2, .distance 2 4, .distance 3 4, .theta 3]
    constant := ![3, 0, -1, 0, -1, 0, 0, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, true, true, false, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 26 2, .triangle 30 0, .triangle 33 2, .triangle 11 0, .triangle 10 2, .triangle 7 1, .triangle 6 0, .triangle 25 1, .corridorLower 3 4]

-- Original cycle 408f7cf91562663b109835922df9e8289ce5f894d075ee9c67de86ddd939bc20; original global index 4987.
def localCycle00073 : Cycle where
  length := 11
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 2, .distance 2 5, .distance 0 2, .distance 2 4, .distance 3 4, .distance 4 6, .distance 5 6, .theta 5, .theta 4, .theta 3]
    constant := ![3, -1, -1, -1, -1, 0, -1, 0, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, true, false, true, true] }
  origin := ![.corridorUpper 2 3, .triangle 15 0, .triangle 17 0, .triangle 7 0, .triangle 6 0, .triangle 25 1, .triangle 32 0, .triangle 34 1, .corridorLower 5 6, .thetaNext 4, .thetaNext 3]

-- Original cycle 40f04ae98cf859b62c89b587270503289162bb9f891f9c5bac742a76f277e42e; original global index 5012.
def localCycle00074 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 3, .distance 3 6, .distance 0 3, .distance 0 5, .distance 0 2, .distance 2 4, .distance 3 4, .theta 3]
    constant := ![3, 0, -1, -1, 0, 0, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, true, false, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 2, .triangle 21 0, .triangle 11 0, .triangle 10 2, .triangle 7 1, .triangle 6 0, .triangle 25 1, .corridorLower 3 4]

-- Original cycle 41b3cd6ddb8c4a1f50d5327d75a9c9f5a96075c321b56ba6eb25a3a031654eed; original global index 5068.
def localCycle00075 : Cycle where
  length := 10
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 3, .distance 0 3, .distance 0 6, .distance 0 2, .distance 0 5, .distance 2 5, .distance 3 5, .distance 3 4, .theta 3]
    constant := ![3, 0, 0, 0, -2, -2, 0, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, false, false, true, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 2, .triangle 1 2, .triangle 11 2, .gapLower 0 4, .gapLower 0 3, .gapLower 5 2, .triangle 26 1, .triangle 31 1, .corridorLower 3 4]

-- Original cycle 4271bdb1725b4b27c78e03848a76b926773846d7f4ed27d35fc541d94b71e26f; original global index 5122.
def localCycle00076 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 3, .distance 0 3, .distance 0 5, .distance 0 6, .distance 0 2, .distance 2 4, .distance 3 4, .theta 3]
    constant := ![3, 0, 0, 0, -2, 0, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, true, false, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 2, .triangle 1 2, .triangle 10 2, .gapLower 0 4, .triangle 8 1, .triangle 6 0, .triangle 25 1, .corridorLower 3 4]

-- Original cycle 43c47425309d14aa199f681d9313dfb3b6a41e0d0c01a7cf5850145fe55b7f46; original global index 5243.
def localCycle00077 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 3, .distance 0 3, .distance 0 5, .distance 0 2, .distance 0 4, .distance 2 4, .distance 3 4, .theta 3]
    constant := ![3, 0, 0, -2, 0, -2, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, false, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 2, .triangle 1 2, .gapLower 0 5, .triangle 7 1, .gapLower 0 2, .gapLower 4 2, .triangle 25 1, .corridorLower 3 4]

-- Original cycle 43c8fd6f91b535c5a0de7bea14994da8252829ad59774f52ce1c1bbd9175e168; original global index 5245.
def localCycle00078 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 3, .distance 1 6, .distance 0 6, .distance 0 2, .distance 2 5, .distance 3 5, .distance 3 4, .theta 3]
    constant := ![3, 0, 0, -2, 0, -1, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, true, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 2, .triangle 21 2, .gapLower 6 2, .triangle 8 1, .triangle 7 0, .triangle 26 1, .triangle 31 1, .corridorLower 3 4]

-- Original cycle 445b708c05a60c2ff38fcab7b4f4c2de1685d0a890bbc3b15612acb2bd530900; original global index 5293.
def localCycle00079 : Cycle where
  length := 7
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 0 6, .distance 2 6, .theta 2, .zero]
    constant := ![0, 3, -2, 0, -2, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .gapLower 6 5, .triangle 13 2, .gapLower 6 2, .corridorLower 2 6, .thetaLower 2]

-- Original cycle 452929d5c271369ed933afd23eb6456db371c551277e7aa806e4565c3dca1c9f; original global index 5348.
def localCycle00080 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 2, .distance 2 6, .distance 2 5, .distance 0 2, .distance 2 4, .distance 3 4, .theta 3]
    constant := ![3, -1, -1, 0, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 0, .triangle 18 0, .triangle 30 1, .triangle 7 0, .triangle 6 0, .triangle 25 1, .corridorLower 3 4]

-- Original cycle 459072b78f61275c5ac33ceac24d49890c139bf72a27a228da009f08dc87dc66; original global index 5381.
def localCycle00081 : Cycle where
  length := 10
  data := {
    node := ![.theta 3, .distance 2 3, .distance 0 2, .distance 2 5, .distance 3 5, .distance 3 4, .distance 4 6, .distance 5 6, .theta 5, .theta 4, .theta 3]
    constant := ![3, -1, -1, 0, 0, -1, 0, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false, true, false, true, true] }
  origin := ![.corridorUpper 2 3, .triangle 5 0, .triangle 7 0, .triangle 26 1, .triangle 31 1, .triangle 32 0, .triangle 34 1, .corridorLower 5 6, .thetaNext 4, .thetaNext 3]

-- Original cycle 459e5e69b28acbba7328d9031d609d071d448edd91802133ac93aa832749192a; original global index 5384.
def localCycle00082 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 2 6, .distance 0 2, .distance 2 5, .distance 3 5, .distance 3 4, .theta 3, .zero]
    constant := ![0, 3, 0, -2, -1, -1, 0, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, true, true, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .gapLower 6 4, .triangle 8 0, .triangle 7 0, .triangle 26 1, .triangle 31 1, .corridorLower 3 4, .thetaLower 3]

-- Original cycle 4655c73893072a603450b4ff470b1260f86c9962eafdd55c9dc92d46e970723c; original global index 5439.
def localCycle00083 : Cycle where
  length := 7
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 5 6, .distance 1 6, .distance 0 6, .theta 0, .zero]
    constant := ![0, 3, -1, -2, -2, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 34 0, .gapLower 6 4, .gapLower 6 3, .corridorLower 0 6, .thetaLower 0]

-- Original cycle 4666e7afb91bb060803e0749b7e6c6c36368aa17d2596c334157542eb38f38a9; original global index 5443.
def localCycle00084 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 2, .distance 2 6, .distance 0 2, .distance 2 5, .distance 3 5, .distance 3 4, .theta 3]
    constant := ![3, -1, -1, -1, -1, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 0, .triangle 18 0, .triangle 8 0, .triangle 7 0, .triangle 26 1, .triangle 31 1, .corridorLower 3 4]

-- Original cycle 487ab7940241b45e3e2568c734ee8b361e5ae8abc58df459744da5e698252334; original global index 5617.
def localCycle00085 : Cycle where
  length := 8
  data := {
    node := ![.theta 5, .distance 4 5, .distance 5 6, .distance 1 6, .distance 0 6, .distance 2 6, .distance 3 6, .theta 6, .theta 5]
    constant := ![3, -1, -2, 0, 0, 0, -2, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, true, false, true] }
  origin := ![.corridorUpper 4 5, .triangle 34 0, .gapLower 6 4, .triangle 4 2, .triangle 8 1, .triangle 27 1, .gapLower 6 0, .thetaNext 5]

-- Original cycle 48c63b2f8588d4bf32a7632fe0fe92c99ae4fe0b17cf615e1169e563bec743e3; original global index 5637.
def localCycle00086 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 3, .distance 0 3, .distance 0 6, .distance 0 5, .distance 0 4, .distance 2 4, .distance 3 4, .theta 3]
    constant := ![3, 0, 0, -2, 0, -2, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, false, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 2, .triangle 1 2, .gapLower 0 5, .triangle 14 1, .gapLower 0 2, .gapLower 4 2, .triangle 25 1, .corridorLower 3 4]

-- Original cycle 4916241f43b3e2110c27b354a8e4c9306cd795f98860beb5541c327fb0fb7f2e; original global index 5659.
def localCycle00087 : Cycle where
  length := 8
  data := {
    node := ![.theta 5, .distance 4 5, .distance 4 6, .distance 1 6, .distance 0 6, .distance 2 6, .distance 3 6, .distance 5 6, .theta 5]
    constant := ![3, 0, -2, -2, 0, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, true, true, false] }
  origin := ![.corridorUpper 4 5, .triangle 34 2, .gapLower 6 5, .gapLower 6 4, .triangle 8 1, .triangle 27 1, .triangle 33 1, .corridorLower 5 6]

-- Original cycle 4b5ca96af27c3ec799f74ba3282d6a615d5fd059e292286518a3d78e6e206290; original global index 5838.
def localCycle00088 : Cycle where
  length := 7
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 5 6, .distance 0 5, .distance 0 4, .theta 0, .zero]
    constant := ![0, 3, -1, -1, -2, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 34 0, .triangle 14 0, .gapLower 0 2, .corridorLower 0 4, .thetaLower 0]

-- Original cycle 4cae979a7274d132d375144cb424a94c31cbd2dfc0567fecfacd487859567b4b; original global index 5951.
def localCycle00089 : Cycle where
  length := 4
  data := {
    node := ![.distance 0 3, .distance 0 5, .distance 5 6, .distance 3 6, .distance 0 3]
    constant := ![-2, -1, 0, 2]
    coefficient := ![0, 0, 0, 0]
    strict := ![false, false, true, true] }
  origin := ![.gapLower 0 5, .triangle 14 0, .triangle 33 2, .gapUpper 3 3]

-- Original cycle 4d5586814823a5200276b18031eb24ffc3df1b7970ca50374d9387ccc72d9e27; original global index 6007.
def localCycle00090 : Cycle where
  length := 3
  data := {
    node := ![.distance 0 3, .distance 0 5, .distance 3 5, .distance 0 3]
    constant := ![-3, 0, 2]
    coefficient := ![0, 0, 0]
    strict := ![false, false, true] }
  origin := ![.gapLower 0 4, .gapLower 5 1, .gapUpper 3 2]

-- Original cycle 4e9451ba2af53c94b76ff4d0e792779f0bab314233cc39004ec4a7f49cc46c74; original global index 6105.
def localCycle00091 : Cycle where
  length := 3
  data := {
    node := ![.distance 0 2, .distance 0 6, .distance 2 6, .distance 0 2]
    constant := ![0, -3, 2]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.triangle 8 2, .gapLower 6 2, .gapUpper 2 3]

-- Original cycle 4f2c695a2cede6a4c7c3b7575feb476124a89426b6ead7ec553a1d2ede10f194; original global index 6153.
def localCycle00092 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 0 2, .distance 2 4, .distance 3 4, .distance 4 6, .distance 5 6, .theta 5, .theta 4, .theta 3]
    constant := ![3, -1, -1, 0, -1, 0, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true, false, true, true] }
  origin := ![.corridorUpper 2 3, .triangle 5 0, .triangle 6 0, .triangle 25 1, .triangle 32 0, .triangle 34 1, .corridorLower 5 6, .thetaNext 4, .thetaNext 3]

-- Original cycle 50a112ce3145b95bf4176674184524a096da2aa1fe6af76ea2951e93e58d2e6c; original global index 6260.
def localCycle00093 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 2 3, .distance 1 2, .distance 1 5, .distance 1 4, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, 0, -1, -1, 0, 0, -1, -3, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, true, true, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 27 0, .triangle 15 0, .triangle 17 2, .triangle 22 1, .triangle 2 0, .gapLower 0 0, .thetaLower 0]

-- Original cycle 513f0eb7a92de791d94a1667968b2a75cb250b32cf8684fcc8e11cd0c2574e45; original global index 6316.
def localCycle00094 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 5 6, .distance 1 5, .distance 1 4, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, -1, -1, 0, -1, -2, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 34 0, .triangle 24 0, .gapLower 1 2, .triangle 2 0, .gapLower 0 0, .thetaLower 0]

-- Original cycle 5180b3e7377db9f990b26e797dc9c476ad1b0091c22b3bb3cebeefc490d69558; original global index 6340.
def localCycle00095 : Cycle where
  length := 10
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 2, .distance 1 5, .distance 1 4, .distance 4 6, .distance 5 6, .distance 2 5, .distance 3 5, .distance 3 4, .theta 3]
    constant := ![3, -1, 0, 0, -1, 0, -1, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, true, false, true, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 0, .triangle 17 2, .triangle 22 1, .triangle 23 0, .triangle 34 1, .triangle 30 0, .triangle 26 1, .triangle 31 1, .corridorLower 3 4]

-- Original cycle 5252c7f8505752c0fa2b25adb2cdfe4a738585897d2d3769ebeb1d87e77acc7e; original global index 6399.
def localCycle00096 : Cycle where
  length := 6
  data := {
    node := ![.distance 1 2, .distance 1 4, .distance 4 5, .distance 5 6, .distance 4 6, .distance 2 6, .distance 1 2]
    constant := ![0, 2, 2, -2, -2, -1]
    coefficient := ![0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, false] }
  origin := ![.gapLower 1 2, .gapUpper 4 4, .gapUpper 5 5, .gapLower 6 5, .gapLower 6 4, .triangle 18 0]

-- Original cycle 532aa438ebd866a9370fcf3be32bceb5e4a3ad3e95c5ec0830b01f6a39523c31; original global index 6471.
def localCycle00097 : Cycle where
  length := 7
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 1 6, .distance 0 6, .theta 0, .zero]
    constant := ![0, 3, 0, -2, -2, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .gapLower 6 4, .gapLower 6 3, .corridorLower 0 6, .thetaLower 0]

-- Original cycle 54e421790493f1d3eba6181d4beeecd9d13d09a524af86ba04efb82c276b75c0; original global index 6574.
def localCycle00098 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 2, .distance 1 6, .distance 0 6, .distance 2 6, .distance 3 6, .distance 3 4, .theta 3]
    constant := ![3, -1, 0, -2, -2, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 0, .triangle 18 2, .gapLower 6 4, .gapLower 6 3, .triangle 27 1, .triangle 32 1, .corridorLower 3 4]

-- Original cycle 56a3483dc5f46155ae7011d7efe34e700f91907c1c8fbd16e72ca1c0c6e60f7a; original global index 6716.
def localCycle00099 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 3, .distance 1 5, .distance 1 6, .distance 0 6, .distance 0 2, .distance 2 4, .distance 3 4, .theta 3]
    constant := ![3, 0, 0, 0, 0, -2, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, true, false, false, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 2, .triangle 20 2, .triangle 24 2, .triangle 4 2, .gapLower 0 3, .triangle 6 0, .triangle 25 1, .corridorLower 3 4]

-- Original cycle 584c082871109e6e83bbf10583409ace696aa836b833f1d5b2385af5fe246f66; original global index 6853.
def localCycle00100 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 3, .distance 1 5, .distance 1 6, .distance 0 6, .distance 0 2, .distance 2 4, .distance 3 4, .theta 3]
    constant := ![3, 0, 0, 0, 0, -3, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, true, false, false, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 2, .triangle 20 2, .triangle 24 2, .triangle 4 2, .gapLower 0 3, .triangle 6 0, .triangle 25 1, .corridorLower 3 4]

-- Original cycle 58be04e7a159b38d7ae59fcb0f2d9b15166ea9ee7120b48b8e989565da3a7e21; original global index 6886.
def localCycle00101 : Cycle where
  length := 3
  data := {
    node := ![.distance 0 3, .distance 0 5, .distance 3 5, .distance 0 3]
    constant := ![-3, 0, 2]
    coefficient := ![0, 0, 0]
    strict := ![false, false, true] }
  origin := ![.gapLower 0 5, .gapLower 5 2, .gapUpper 3 3]

-- Original cycle 5a44bf134757bd85e0d0a4f53e2461d511431a13bc7a91aa346f0a99418bfdea; original global index 7023.
def localCycle00102 : Cycle where
  length := 5
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .theta 4, .zero]
    constant := ![0, 2, -2, -2, 0]
    coefficient := ![1, 1, 0, -1, 0]
    strict := ![false, false, false, true, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .gapLower 6 5, .gapUpper 4 6, .thetaLower 4]

-- Original cycle 5ce4281899aa163d320de36a8b921bfcb28e5ab4880d8997b36a7598e1332fdf; original global index 7230.
def localCycle00103 : Cycle where
  length := 10
  data := {
    node := ![.theta 0, .distance 0 3, .distance 0 5, .distance 0 6, .distance 5 6, .distance 3 5, .distance 3 4, .theta 3, .theta 2, .theta 1, .theta 0]
    constant := ![2, 0, -2, 0, -1, 0, -1, 0, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, false, true, true, true] }
  origin := ![.gapLower 0 6, .triangle 10 2, .gapLower 0 4, .triangle 14 1, .triangle 33 0, .gapLower 3 1, .corridorLower 3 4, .thetaNext 2, .thetaNext 1, .thetaNext 0]

-- Original cycle 5d1666de489c0158fd2a99942fe9b29b5bc134f0ac7faa65e481aa5012bedb17; original global index 7244.
def localCycle00104 : Cycle where
  length := 11
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 6, .distance 1 3, .distance 1 2, .distance 1 4, .distance 4 5, .distance 2 5, .distance 0 2, .distance 2 4, .distance 3 4, .theta 3]
    constant := ![3, -1, -1, 0, 0, -1, 0, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, true, false, false, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 27 0, .triangle 21 0, .gapLower 1 4, .triangle 16 2, .triangle 22 0, .triangle 28 2, .triangle 7 0, .triangle 6 0, .triangle 25 1, .corridorLower 3 4]

-- Original cycle 5ecbf0edc9a28b17b47a9ae58063598c53e6026802b318a9637714e57db61d74; original global index 7381.
def localCycle00105 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 0 3, .distance 0 5, .distance 0 2, .distance 0 4, .theta 0, .zero]
    constant := ![0, 3, 0, 0, -1, 0, -2, -2, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, true, false, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 11 0, .triangle 10 2, .gapLower 0 3, .gapLower 0 2, .corridorLower 0 4, .thetaLower 0]

-- Original cycle 6017a6194dd8bba5c936ba702097d41c9c98741ff8da3927c38bc665f8745669; original global index 7488.
def localCycle00106 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 5 6, .distance 0 6, .distance 0 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, -1, 0, -2, 0, -2, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 34 0, .triangle 14 2, .gapLower 0 4, .triangle 0 1, .gapLower 0 0, .thetaLower 0]

-- Original cycle 6114d1375fa9486704d5d877254251891e9b05dea050b946849b42a125fffd2b; original global index 7573.
def localCycle00107 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 2, .distance 1 5, .distance 1 4, .distance 4 6, .distance 2 4, .distance 3 4, .theta 3]
    constant := ![3, -1, 0, 0, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 0, .triangle 17 2, .triangle 22 1, .triangle 23 0, .triangle 29 0, .triangle 25 1, .corridorLower 3 4]

-- Original cycle 624678021bce8b1d7477b148fab80f0b4c271add3d642197f3054e7974b106db; original global index 7670.
def localCycle00108 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 2, .distance 1 5, .distance 5 6, .distance 3 5, .distance 3 4, .theta 3]
    constant := ![3, -1, 0, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 0, .triangle 17 2, .triangle 24 0, .triangle 33 0, .triangle 31 1, .corridorLower 3 4]

-- Original cycle 632c11f07efad50715a8bf27fed62c6d2eaa251cc4ed0e486d2a884220cd1915; original global index 7735.
def localCycle00109 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 2 6, .distance 1 6, .distance 0 6, .distance 0 3, .distance 0 2, .distance 0 5, .theta 0, .zero]
    constant := ![0, 3, 0, 0, 0, 0, 0, -2, 0, -2, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, true, true, true, false, true, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 27 2, .triangle 18 2, .triangle 4 2, .gapLower 0 5, .triangle 5 1, .gapLower 0 3, .corridorLower 0 5, .thetaLower 0]

-- Original cycle 63c118d2df633515347b2f52586c50492c071c0147c7d9d85c6bb2dcad2a45b3; original global index 7775.
def localCycle00110 : Cycle where
  length := 6
  data := {
    node := ![.theta 3, .distance 2 3, .distance 0 2, .distance 2 6, .distance 3 6, .distance 3 4, .theta 3]
    constant := ![3, -1, -1, -2, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 5 0, .triangle 8 0, .gapLower 6 2, .triangle 32 1, .corridorLower 3 4]

-- Original cycle 6664b624a06db7c91dfdfa25bd776836099b575b357a9770d2e773e53e2361f1; original global index 7962.
def localCycle00111 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 2, .distance 1 5, .distance 5 6, .distance 3 5, .distance 3 4, .theta 3]
    constant := ![3, -1, 0, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 0, .triangle 17 2, .triangle 24 0, .triangle 33 0, .gapLower 3 1, .corridorLower 3 4]

-- Original cycle 6833321d56ad812f31023eb420040cb336a304eeebdb4a04694d8bbf8343394f; original global index 8100.
def localCycle00112 : Cycle where
  length := 7
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 1 6, .distance 0 6, .theta 0, .zero]
    constant := ![0, 3, -2, 0, -2, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .gapLower 6 5, .triangle 23 2, .gapLower 6 3, .corridorLower 0 6, .thetaLower 0]

-- Original cycle 69f0c9d3d97e31f1e8b06f36a4744d307ae97a8fe3e25b89cb707108b275a9a0; original global index 8246.
def localCycle00113 : Cycle where
  length := 13
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 3, .distance 0 3, .distance 3 6, .theta 6, .distance 5 6, .distance 4 5, .distance 2 5, .distance 1 2, .distance 0 2, .distance 2 4, .distance 3 4, .theta 3]
    constant := ![3, 0, 0, -1, -2, 2, -1, 0, -1, 0, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, false, false, true, false, true, false, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 2, .triangle 1 2, .triangle 11 0, .gapLower 6 0, .gapLower 6 6, .triangle 34 0, .triangle 28 2, .triangle 17 0, .triangle 0 2, .triangle 6 0, .triangle 25 1, .corridorLower 3 4]

-- Original cycle 700bd1893dd179620333d6da115486426dceb9a6dc6ae0cdac99b60c4bfbf7de; original global index 8684.
def localCycle00114 : Cycle where
  length := 9
  data := {
    node := ![.theta 5, .distance 4 5, .distance 2 5, .distance 0 2, .distance 0 6, .distance 2 6, .distance 3 6, .distance 5 6, .theta 6, .theta 5]
    constant := ![3, 0, -1, 0, -2, 0, 0, -2, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, true, true, false, true] }
  origin := ![.corridorUpper 4 5, .triangle 28 2, .triangle 7 0, .triangle 8 2, .gapLower 6 3, .triangle 27 1, .triangle 33 1, .gapLower 6 0, .thetaNext 5]

-- Original cycle 70bba30de177614fd786012efffbe4f3efb3b3a66c371c055490c2615c494e0b; original global index 8738.
def localCycle00115 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 5 6, .distance 1 5, .distance 1 4, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, -1, -1, 0, -1, -3, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 34 0, .triangle 24 0, .gapLower 1 2, .triangle 2 0, .gapLower 0 0, .thetaLower 0]

-- Original cycle 70dc4c64dcd8345c12e74689eae12b91dc360652e4ad06243ee8a828625da85d; original global index 8745.
def localCycle00116 : Cycle where
  length := 3
  data := {
    node := ![.distance 0 1, .distance 1 4, .distance 0 4, .distance 0 1]
    constant := ![2, 0, -2]
    coefficient := ![0, 0, 0]
    strict := ![true, false, false] }
  origin := ![.gapUpper 1 1, .gapLower 4 3, .gapLower 0 1]

-- Original cycle 70df3d5923dfb6fc8a8e2b780a8de722f08877916431ef70ca459147fc064534; original global index 8748.
def localCycle00117 : Cycle where
  length := 8
  data := {
    node := ![.theta 0, .distance 0 6, .distance 0 2, .distance 2 4, .distance 3 4, .theta 3, .theta 2, .theta 1, .theta 0]
    constant := ![1, 0, -1, 0, -1, 0, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, true, true, true] }
  origin := ![.gapLower 0 6, .triangle 8 1, .triangle 6 0, .triangle 25 1, .corridorLower 3 4, .thetaNext 2, .thetaNext 1, .thetaNext 0]

-- Original cycle 716a931515484d7e5282e61005e27a6f2115452ee48d3f6f702415b6bf4262fb; original global index 8801.
def localCycle00118 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 2, .distance 1 6, .distance 0 6, .distance 2 6, .distance 3 6, .distance 3 4, .theta 3]
    constant := ![3, -1, 0, -2, 0, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, true, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 0, .triangle 18 2, .gapLower 6 4, .triangle 8 1, .triangle 27 1, .triangle 32 1, .corridorLower 3 4]

-- Original cycle 742caac0707637802acfb17805c47e0e0dd6ac6597344907815f142a51380679; original global index 9013.
def localCycle00119 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 3, .distance 0 3, .distance 0 5, .distance 0 6, .distance 0 2, .distance 2 4, .distance 3 4, .theta 3]
    constant := ![3, 0, 0, 0, -3, 0, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, true, false, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 2, .triangle 1 2, .triangle 10 2, .gapLower 0 4, .triangle 8 1, .triangle 6 0, .triangle 25 1, .corridorLower 3 4]

-- Original cycle 747880c24ac313d9c7b5691bc302d0cc3f856fc67c19f2bf434ee88282cb05f1; original global index 9030.
def localCycle00120 : Cycle where
  length := 10
  data := {
    node := ![.theta 0, .distance 0 3, .distance 0 5, .distance 5 6, .distance 3 5, .distance 3 4, .theta 3, .distance 2 3, .distance 1 2, .distance 0 1, .theta 0]
    constant := ![2, 0, -1, -1, 0, -1, 3, -1, -1, -2]
    coefficient := ![1, 0, 0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![false, true, false, false, true, false, false, false, false, false] }
  origin := ![.gapLower 0 6, .triangle 10 2, .triangle 14 0, .triangle 33 0, .triangle 31 1, .corridorLower 3 4, .corridorUpper 2 3, .triangle 15 0, .triangle 0 0, .gapLower 0 0]

-- Original cycle 77d8e93a7bba8f0fdb5184527c20e1b7061fc62f05a72bbd716b3539f557dbdb; original global index 9267.
def localCycle00121 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 2, .distance 1 4, .distance 4 5, .distance 2 4, .distance 4 6, .distance 3 4, .theta 3]
    constant := ![4, -1, 0, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false] }
  origin := ![.gapLower 3 6, .triangle 15 0, .triangle 16 2, .triangle 22 0, .triangle 28 0, .triangle 29 0, .triangle 32 0, .gapLower 3 0]

-- Original cycle 785cd029a18350e40ee330a4108db1b5a16e4263b060ca3b1be9ad75a2c37ecf; original global index 9305.
def localCycle00122 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 2 6, .distance 0 2, .distance 2 4, .distance 3 4, .theta 3, .zero]
    constant := ![0, 3, 0, -3, -1, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, true, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .gapLower 6 4, .triangle 8 0, .triangle 6 0, .triangle 25 1, .corridorLower 3 4, .thetaLower 3]

-- Original cycle 788b755a2698afb4dffff1edd4028bff209bb0122c2bc6949413693a1a8febc2; original global index 9326.
def localCycle00123 : Cycle where
  length := 8
  data := {
    node := ![.theta 5, .distance 4 5, .distance 4 6, .distance 1 6, .distance 0 6, .distance 2 6, .distance 3 6, .distance 5 6, .theta 5]
    constant := ![3, 0, -2, 0, -2, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, true, true, false] }
  origin := ![.corridorUpper 4 5, .triangle 34 2, .gapLower 6 5, .triangle 4 2, .gapLower 6 3, .triangle 27 1, .triangle 33 1, .corridorLower 5 6]

-- Original cycle 7928a56c4567a5baac9c97ef7a01dbb513593b334c30d4eb1f64a4c64322c8b0; original global index 9377.
def localCycle00124 : Cycle where
  length := 7
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 1 6, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, -3, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .gapLower 6 4, .triangle 4 0, .corridorLower 0 1, .thetaLower 0]

-- Original cycle 7ad06453d8fed01ef25cbfbfa14c04b7d55ff753c331ad8885fa42d33ff4194c; original global index 9508.
def localCycle00125 : Cycle where
  length := 6
  data := {
    node := ![.theta 3, .distance 2 3, .distance 0 2, .distance 2 4, .distance 4 6, .distance 3 4, .theta 3]
    constant := ![3, -1, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 5 0, .triangle 6 0, .triangle 29 0, .triangle 32 0, .corridorLower 3 4]

-- Original cycle 7c29a7ee0e4c52ebde24fcbd432d19ec2494a46ab60075556bcfd65d42798ef4; original global index 9607.
def localCycle00126 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 1 6, .distance 0 6, .distance 2 6, .theta 2, .zero]
    constant := ![0, 3, 0, -2, 0, -2, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .gapLower 6 4, .triangle 4 2, .gapLower 6 2, .corridorLower 2 6, .thetaLower 2]

-- Original cycle 7c48de03b044ec38f708a5811d696b39b2a4639ce0590b9483ad7bd9dab80666; original global index 9619.
def localCycle00127 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 5, .distance 2 5, .distance 1 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 2, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 34 0, .triangle 28 2, .triangle 17 0, .triangle 0 0, .corridorLower 0 1, .thetaLower 0]

-- Original cycle 7cb31b341caa93af2cd1805c17687aec7654acde55aab1b7d4191fdf6b9bf4f0; original global index 9657.
def localCycle00128 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 2 5, .distance 0 2, .distance 2 4, .distance 3 4, .theta 3, .zero]
    constant := ![0, 1, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 30 0, .triangle 7 0, .triangle 6 0, .triangle 25 1, .corridorLower 3 4, .thetaLower 3]

-- Original cycle 7ece5ab88ca835fd1e77c4e4e0743b0b09bd2a89687e71f67930dab3d7cccaca; original global index 9848.
def localCycle00129 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 0 2, .distance 2 6, .distance 3 6, .theta 6, .distance 5 6, .distance 4 5, .distance 3 4, .theta 3]
    constant := ![3, -1, -1, 0, -2, 2, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 5 0, .triangle 8 0, .triangle 27 1, .gapLower 6 0, .gapLower 6 6, .triangle 34 0, .triangle 31 0, .corridorLower 3 4]

-- Original cycle 7f6e22f8f4fe911460be322a622b276c505f4e8bcc26a95a26c7708d314a518a; original global index 9882.
def localCycle00130 : Cycle where
  length := 7
  data := {
    node := ![.zero, .theta 3, .distance 2 3, .distance 0 2, .distance 0 4, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, -1, -2, 0, -2, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false] }
  origin := ![.thetaUpper 3, .corridorUpper 2 3, .triangle 5 0, .gapLower 0 2, .triangle 2 1, .gapLower 0 0, .thetaLower 0]

-- Original cycle 7fbd5f13daa75566b6136a55fb88bdb4adfbb4a3a51529777c2fba8550c5e1cc; original global index 9906.
def localCycle00131 : Cycle where
  length := 4
  data := {
    node := ![.theta 0, .distance 0 3, .distance 0 2, .distance 0 4, .theta 0]
    constant := ![2, 0, -2, -1]
    coefficient := ![1, 0, 0, 0]
    strict := ![false, true, false, false] }
  origin := ![.gapLower 0 6, .triangle 5 1, .gapLower 0 2, .corridorLower 0 4]

-- Original cycle 80402e368fc36732c46f1e45cff9f1269bed52fbb55d3e28b985cf1132702526; original global index 9950.
def localCycle00132 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 2 3, .distance 0 2, .distance 2 6, .distance 3 6, .distance 3 5, .distance 3 4, .theta 3]
    constant := ![3, -1, -1, -3, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 5 0, .triangle 8 0, .gapLower 6 1, .triangle 33 1, .triangle 31 1, .corridorLower 3 4]

-- Original cycle 822104e78a1f1c3372d313665bece4afe151d689207d4d692a23f68c7d9b2574; original global index 10103.
def localCycle00133 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 3, .distance 0 3, .distance 0 5, .distance 3 5, .distance 5 6, .theta 5, .theta 4, .theta 3]
    constant := ![3, 0, 0, -2, 0, -1, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, false, false, true, true] }
  origin := ![.corridorUpper 2 3, .triangle 15 2, .triangle 1 2, .gapLower 0 5, .gapLower 5 2, .triangle 33 0, .corridorLower 5 6, .thetaNext 4, .thetaNext 3]

-- Original cycle 828a1cac9ed8bb76e94000cf168fa918a9da91ec5b9d068c0832343eeacb3a09; original global index 10131.
def localCycle00134 : Cycle where
  length := 3
  data := {
    node := ![.distance 0 2, .distance 0 5, .distance 2 5, .distance 0 2]
    constant := ![-3, 0, 2]
    coefficient := ![0, 0, 0]
    strict := ![false, false, true] }
  origin := ![.gapLower 0 3, .gapLower 5 2, .gapUpper 2 2]

-- Original cycle 83510377f97f3e0156a16ecc08f6957f60ea605def898bac3cf2c1f6ec602b72; original global index 10180.
def localCycle00135 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 2, .distance 0 2, .distance 2 5, .distance 3 5, .distance 5 6, .theta 5, .theta 4, .theta 3]
    constant := ![3, -1, 0, -1, 0, -1, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false, true, true] }
  origin := ![.corridorUpper 2 3, .triangle 15 0, .triangle 0 2, .triangle 7 0, .triangle 26 1, .triangle 33 0, .corridorLower 5 6, .thetaNext 4, .thetaNext 3]

-- Original cycle 83e9460b4c32df83c11139502a9dc2b6452c53aa09bce851c657c7e79b45210d; original global index 10240.
def localCycle00136 : Cycle where
  length := 8
  data := {
    node := ![.theta 5, .distance 4 5, .distance 5 6, .distance 3 6, .distance 2 3, .distance 0 2, .distance 2 5, .distance 3 5, .theta 5]
    constant := ![3, -1, 0, -1, -1, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, true, false] }
  origin := ![.corridorUpper 4 5, .triangle 34 0, .triangle 33 2, .triangle 27 0, .triangle 5 0, .triangle 7 0, .triangle 26 1, .gapLower 5 0]

-- Original cycle 892dedf6d91b791d27c63135a9c711238ac48852016f7d4e02a94c132ed995eb; original global index 10614.
def localCycle00137 : Cycle where
  length := 10
  data := {
    node := ![.theta 0, .distance 0 3, .distance 0 6, .distance 0 2, .distance 2 5, .distance 3 5, .distance 3 4, .theta 3, .theta 2, .theta 1, .theta 0]
    constant := ![2, -2, 0, -1, 0, 0, -1, 0, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, true, false, true, true, true] }
  origin := ![.gapLower 0 6, .gapLower 0 5, .triangle 8 1, .triangle 7 0, .triangle 26 1, .triangle 31 1, .corridorLower 3 4, .thetaNext 2, .thetaNext 1, .thetaNext 0]

-- Original cycle 89bdea91bf2aba8c2f99cee4fe45e43c64f477f9356ac2662ad82ee71e31f810; original global index 10672.
def localCycle00138 : Cycle where
  length := 10
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 2, .distance 1 4, .distance 4 5, .distance 2 5, .distance 0 2, .distance 2 6, .distance 3 6, .distance 3 4, .theta 3]
    constant := ![3, -1, 0, -1, 0, -1, -1, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false, true, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 0, .triangle 16 2, .triangle 22 0, .triangle 28 2, .triangle 7 0, .triangle 8 0, .triangle 27 1, .triangle 32 1, .corridorLower 3 4]

-- Original cycle 89c096972344b6198ef675eb1314d7c42582b7ef55a6c55005424604676e99a6; original global index 10673.
def localCycle00139 : Cycle where
  length := 11
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 2, .distance 1 4, .distance 4 5, .distance 2 5, .distance 5 6, .distance 0 5, .distance 0 2, .distance 2 4, .distance 3 4, .theta 3]
    constant := ![3, -1, 0, -1, 0, -1, -1, 0, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false, true, false, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 0, .triangle 16 2, .triangle 22 0, .triangle 28 2, .triangle 30 0, .triangle 14 0, .triangle 7 1, .triangle 6 0, .triangle 25 1, .corridorLower 3 4]

-- Original cycle 89ca4b4a82348c64a96849ffe7e455af1960fe12692fb6054ef4a2045bd1831e; original global index 10675.
def localCycle00140 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 2 6, .distance 2 5, .distance 1 2, .distance 0 2, .distance 2 4, .distance 3 4, .theta 3, .zero]
    constant := ![0, 2, 0, -2, 0, -1, 0, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, true, false, true, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 34 2, .gapLower 6 4, .triangle 30 1, .triangle 17 0, .triangle 0 2, .triangle 6 0, .triangle 25 1, .corridorLower 3 4, .thetaLower 3]

-- Original cycle 8ad5957dd19a8faf6c24a54a0d0fffc745a4fd26fdd7d0cc3af165dacff30835; original global index 10757.
def localCycle00141 : Cycle where
  length := 11
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 3, .distance 0 3, .distance 3 6, .theta 6, .distance 5 6, .distance 2 5, .distance 0 2, .distance 2 4, .distance 3 4, .theta 3]
    constant := ![3, 0, 0, -1, -3, 3, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, false, false, false, false, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 2, .triangle 1 2, .triangle 11 0, .gapLower 6 0, .corridorUpper 5 6, .triangle 30 0, .triangle 7 0, .triangle 6 0, .triangle 25 1, .corridorLower 3 4]

-- Original cycle 8c287d878985c221f2581914defeed8512005f68b4a3ccc9e8054cae4eda2fcb; original global index 10848.
def localCycle00142 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 0 3, .distance 0 5, .distance 0 2, .distance 0 4, .theta 0, .zero]
    constant := ![0, 3, 0, 0, -1, -2, 0, -2, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, true, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 11 0, .gapLower 0 4, .triangle 7 1, .gapLower 0 2, .corridorLower 0 4, .thetaLower 0]

-- Original cycle 8d875ed7094eb9bb93a8edd91d6524c8a298d167b8cd9dea9ea1cd08ad2f894e; original global index 10943.
def localCycle00143 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 2, .distance 1 6, .distance 1 4, .distance 4 5, .distance 2 4, .distance 3 4, .theta 3]
    constant := ![3, -1, 0, 0, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 0, .triangle 18 2, .triangle 23 1, .triangle 22 0, .triangle 28 0, .triangle 25 1, .corridorLower 3 4]

-- Original cycle 8dafe81d24aa4b058238605e25123861851a1185416b1dd7d89cdb9ace227121; original global index 10960.
def localCycle00144 : Cycle where
  length := 6
  data := {
    node := ![.zero, .theta 6, .distance 4 6, .distance 1 6, .distance 0 1, .theta 0, .zero]
    constant := ![0, 2, -2, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .gapLower 6 5, .triangle 4 0, .corridorLower 0 1, .thetaLower 0]

-- Original cycle 8db6ed7abf5810efdbbe27cb7eea1059969fc355f0a929df74b2a281f0404e29; original global index 10963.
def localCycle00145 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 2 3, .distance 1 2, .distance 1 4, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, 0, -1, -1, 0, -1, -3, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, true, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 27 0, .triangle 15 0, .triangle 16 2, .triangle 2 0, .gapLower 0 0, .thetaLower 0]

-- Original cycle 8dfe0628f144d77c646414352f6091d3df110dff09647b5c1c50afb6dc14070a; original global index 10995.
def localCycle00146 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 2, .distance 1 6, .distance 0 6, .distance 2 6, .distance 3 6, .distance 3 4, .theta 3]
    constant := ![3, -1, 0, 0, -2, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, true, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 0, .triangle 18 2, .triangle 4 2, .gapLower 6 2, .triangle 27 1, .triangle 32 1, .corridorLower 3 4]

-- Original cycle 8e4b66bfabf9f3949a9de74b873c3a5bcdaeb24adbc7edc9dd1d92275088fb71; original global index 11016.
def localCycle00147 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 2 6, .distance 0 2, .distance 2 5, .distance 3 5, .distance 3 4, .theta 3, .zero]
    constant := ![0, 3, 0, -3, -1, -1, 0, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, true, true, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .gapLower 6 4, .triangle 8 0, .triangle 7 0, .triangle 26 1, .triangle 31 1, .corridorLower 3 4, .thetaLower 3]

-- Original cycle 928a672a66a4cea977a2fcd38fe221d5bed65e70253946dc5053b7a98debb241; original global index 11353.
def localCycle00148 : Cycle where
  length := 7
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 5 6, .distance 0 5, .distance 0 4, .theta 0, .zero]
    constant := ![0, 3, -1, -1, -3, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 34 0, .triangle 14 0, .gapLower 0 2, .corridorLower 0 4, .thetaLower 0]

-- Original cycle 9343f0018610fd7da1c98b729459ab53c4632cf337c0707ae929fcdc70552b6a; original global index 11421.
def localCycle00149 : Cycle where
  length := 9
  data := {
    node := ![.theta 0, .distance 0 3, .distance 3 5, .distance 5 6, .theta 5, .distance 4 5, .distance 2 5, .distance 1 2, .distance 0 1, .theta 0]
    constant := ![2, -1, -1, -1, 3, 0, -1, -1, -2]
    coefficient := ![1, 0, 0, 0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, false, false] }
  origin := ![.gapLower 0 6, .triangle 10 0, .triangle 33 0, .corridorLower 5 6, .corridorUpper 4 5, .triangle 28 2, .triangle 17 0, .triangle 0 0, .gapLower 0 0]

-- Original cycle 94fb809ce04f286a363eedc78549a676ab2363676a671d7ef3025563e8fe9c42; original global index 11563.
def localCycle00150 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 3, .distance 1 6, .distance 0 6, .distance 0 2, .distance 2 4, .distance 3 4, .theta 3]
    constant := ![3, 0, 0, -3, 0, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 2, .triangle 21 2, .gapLower 6 2, .triangle 8 1, .triangle 6 0, .triangle 25 1, .corridorLower 3 4]

-- Original cycle 952fa698d6711d0ea2925cefa14d2fc003eee705947c57f3e17dbaec935957ad; original global index 11589.
def localCycle00151 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 6, .distance 1 3, .distance 1 2, .distance 2 5, .distance 0 2, .distance 2 4, .distance 3 4, .theta 3]
    constant := ![3, -1, -1, 0, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 27 0, .triangle 21 0, .gapLower 1 4, .triangle 17 0, .triangle 7 0, .triangle 6 0, .triangle 25 1, .corridorLower 3 4]

-- Original cycle 95577d2c78ccc9667d0f5c15edceb8c172256d89fe813a45f803a3f92de6b04d; original global index 11604.
def localCycle00152 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 6, .distance 1 3, .distance 0 3, .distance 0 2, .distance 2 5, .distance 3 5, .distance 3 4, .theta 3]
    constant := ![3, -1, -1, 0, 0, -1, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false, true, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 27 0, .triangle 21 0, .triangle 1 2, .triangle 5 1, .triangle 7 0, .triangle 26 1, .triangle 31 1, .corridorLower 3 4]

-- Original cycle 96ab70f24a5cf79c633a5a6ead5763726717e8039bd9860bfab8b688b2d26c9d; original global index 11713.
def localCycle00153 : Cycle where
  length := 4
  data := {
    node := ![.zero, .theta 1, .distance 0 1, .theta 0, .zero]
    constant := ![0, 2, -3, 0]
    coefficient := ![1, 0, 0, 0]
    strict := ![false, true, false, false] }
  origin := ![.thetaUpper 1, .gapUpper 1 0, .gapLower 0 0, .thetaLower 0]

-- Original cycle 96b1b122bc8901aebac6594f8c2960157696ee9011527778b27586bd99a2e71d; original global index 11717.
def localCycle00154 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 2 6, .distance 1 6, .distance 0 6, .distance 0 2, .distance 2 5, .distance 3 5, .distance 3 4, .theta 3]
    constant := ![3, 0, -2, -2, 0, -1, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, false, true, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 27 2, .gapLower 6 3, .gapLower 6 2, .triangle 8 1, .triangle 7 0, .triangle 26 1, .triangle 31 1, .corridorLower 3 4]

-- Original cycle 99faae56dbc280be34d763b6726f5a2ad7dc795b6f83e9e10eb84c4911472390; original global index 11955.
def localCycle00155 : Cycle where
  length := 7
  data := {
    node := ![.theta 5, .distance 4 5, .distance 2 5, .distance 0 2, .distance 2 6, .distance 3 6, .distance 5 6, .theta 5]
    constant := ![3, 0, -1, -1, 0, -3, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, false, false] }
  origin := ![.corridorUpper 4 5, .triangle 28 2, .triangle 7 0, .triangle 8 0, .triangle 27 1, .gapLower 6 1, .corridorLower 5 6]

-- Original cycle 9a36a2d11f9d62217ef379677c9e236024dd7f18f4f876e9cd879bc3dfcba2f8; original global index 11982.
def localCycle00156 : Cycle where
  length := 6
  data := {
    node := ![.distance 1 2, .distance 1 5, .distance 4 5, .distance 5 6, .distance 4 6, .distance 2 6, .distance 1 2]
    constant := ![0, 2, 2, -2, -2, -1]
    coefficient := ![0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, false] }
  origin := ![.gapLower 1 3, .gapUpper 5 4, .gapUpper 5 5, .gapLower 6 5, .gapLower 6 4, .triangle 18 0]

-- Original cycle 9c2081f1663b2aa3457109ebcef33abc848c80bd19dbe409ca95f5fa38216661; original global index 12146.
def localCycle00157 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 5 6, .distance 2 5, .distance 1 2, .distance 0 2, .distance 2 4, .distance 3 4, .theta 3, .zero]
    constant := ![0, 3, -1, -1, -1, 0, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, true, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 34 0, .triangle 30 0, .triangle 17 0, .triangle 0 2, .triangle 6 0, .triangle 25 1, .corridorLower 3 4, .thetaLower 3]

-- Original cycle 9da53168e00efe313bbd3032f5d4926f14717a74c41541e2e2a2b7f64c89a015; original global index 12260.
def localCycle00158 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 2 6, .distance 1 6, .distance 0 6, .distance 0 5, .distance 0 2, .distance 2 4, .distance 3 4, .theta 3]
    constant := ![3, 0, -2, -2, 0, 0, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, true, false, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 27 2, .gapLower 6 3, .gapLower 6 2, .triangle 14 1, .triangle 7 1, .triangle 6 0, .triangle 25 1, .corridorLower 3 4]

-- Original cycle 9e1468d9fe7d975d09b84d611edfc5eb18f335ded17aebd0f77ceaf25c93ab00; original global index 12303.
def localCycle00159 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 2, .distance 2 5, .distance 2 6, .distance 0 2, .distance 2 4, .distance 3 4, .theta 3]
    constant := ![3, -1, -1, 0, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 0, .triangle 17 0, .triangle 30 2, .triangle 8 0, .triangle 6 0, .triangle 25 1, .corridorLower 3 4]

-- Original cycle 9f1183b34d645314587f4ebcd7c3a687c40fa24019b75d5d1a4858c2372252c0; original global index 12386.
def localCycle00160 : Cycle where
  length := 14
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 2 6, .distance 1 6, .distance 0 6, .distance 0 3, .distance 0 5, .distance 0 2, .distance 2 4, .distance 3 4, .theta 3, .zero]
    constant := ![0, 3, 0, 0, 0, 0, 0, -2, 0, -2, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, true, true, true, false, true, false, false, true, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 27 2, .triangle 18 2, .triangle 4 2, .gapLower 0 5, .triangle 10 2, .gapLower 0 3, .triangle 6 0, .triangle 25 1, .corridorLower 3 4, .thetaLower 3]

-- Original cycle a0508e980e536bb2f2f26c31dc31ced0eab36edffd580660e888b1b2efb7e2f6; original global index 12475.
def localCycle00161 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 3, .distance 1 5, .distance 5 6, .distance 0 5, .distance 0 2, .distance 2 4, .distance 3 4, .theta 3]
    constant := ![3, 0, 0, -1, -1, 0, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, true, false, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 2, .triangle 20 2, .triangle 24 0, .triangle 14 0, .triangle 7 1, .triangle 6 0, .triangle 25 1, .corridorLower 3 4]

-- Original cycle a109bff811a4e0113a0376553922ef298e875700311cf0ecf105715e83239dd6; original global index 12523.
def localCycle00162 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 2 6, .distance 1 6, .distance 0 6, .distance 0 5, .distance 0 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, -2, 0, -2, 0, 0, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, true, true, true, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .gapLower 6 4, .triangle 18 2, .gapLower 6 2, .triangle 14 1, .triangle 7 1, .triangle 0 1, .corridorLower 0 1, .thetaLower 0]

-- Original cycle a318eb944a599b898f241c93ffb85053ad92074609e0769506a2f0447f9806b0; original global index 12681.
def localCycle00163 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 2, .distance 1 4, .distance 4 5, .distance 2 4, .distance 3 4, .theta 3]
    constant := ![3, -1, 0, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 0, .triangle 16 2, .triangle 22 0, .triangle 28 0, .triangle 25 1, .corridorLower 3 4]

-- Original cycle a5c21775a421c2a1f2bb086941097a143b603c3a9bb294d553e8d802b161ffe1; original global index 12877.
def localCycle00164 : Cycle where
  length := 10
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 2, .distance 1 4, .distance 4 5, .distance 5 6, .distance 2 5, .distance 0 2, .distance 2 4, .distance 3 4, .theta 3]
    constant := ![3, -1, 0, -1, -1, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 0, .triangle 16 2, .triangle 22 0, .triangle 34 0, .triangle 30 0, .triangle 7 0, .triangle 6 0, .triangle 25 1, .corridorLower 3 4]

-- Original cycle a68f16984df829ca2a97496dce25681f2d3005aa53aca508c71ea1a86d62a01c; original global index 12937.
def localCycle00165 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 3, .distance 0 3, .distance 0 5, .distance 0 6, .distance 0 2, .distance 2 4, .distance 3 4, .theta 3]
    constant := ![3, 0, 0, 0, -2, -2, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, false, false, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 2, .triangle 1 2, .triangle 10 2, .gapLower 0 4, .gapLower 0 3, .triangle 6 0, .triangle 25 1, .corridorLower 3 4]

-- Original cycle a6996948072bef7239077ced9da1db4ae3e0206caa9ca3631895f81444273b2a; original global index 12941.
def localCycle00166 : Cycle where
  length := 7
  data := {
    node := ![.theta 6, .distance 5 6, .distance 4 6, .distance 1 6, .distance 0 6, .distance 2 6, .distance 3 6, .theta 6]
    constant := ![3, 0, -2, 0, 0, 0, -2]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, true, true, false] }
  origin := ![.corridorUpper 5 6, .triangle 34 2, .gapLower 6 4, .triangle 4 2, .triangle 8 1, .triangle 27 1, .gapLower 6 0]

-- Original cycle a6f71c0edcf70bf979ea9b19046a129d73f6469dd11c93b29c61983871a7a74c; original global index 12973.
def localCycle00167 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 6, .distance 1 3, .distance 0 3, .distance 0 5, .distance 0 2, .distance 2 4, .distance 3 4, .theta 3]
    constant := ![3, -1, -1, 0, 0, 0, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, true, false, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 27 0, .triangle 21 0, .triangle 1 2, .triangle 10 2, .triangle 7 1, .triangle 6 0, .triangle 25 1, .corridorLower 3 4]

-- Original cycle a8de35ee4192120725974ee49779bb0f07c07d40fecdb49e8d6e25376ba830d8; original global index 13145.
def localCycle00168 : Cycle where
  length := 7
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 0 6, .distance 3 6, .theta 3, .zero]
    constant := ![0, 3, -2, 0, -2, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .gapLower 6 5, .triangle 13 2, .gapLower 6 1, .corridorLower 3 6, .thetaLower 3]

-- Original cycle a9b33030286cdfc6f0153fbe6fe23dcada307c8cdc8fb4f4488d70023b48d47e; original global index 13210.
def localCycle00169 : Cycle where
  length := 7
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 5, .distance 1 4, .distance 0 1, .theta 0, .zero]
    constant := ![0, 2, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 34 0, .triangle 22 0, .triangle 2 0, .corridorLower 0 1, .thetaLower 0]

-- Original cycle aa1913b317ac6d7198c5f2cd447c8e394067bcaa8bbb3bb440236abbaea50cc6; original global index 13243.
def localCycle00170 : Cycle where
  length := 7
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 2 6, .distance 1 6, .distance 0 1, .theta 0, .zero]
    constant := ![0, 2, 0, -2, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 30 2, .gapLower 6 3, .triangle 4 0, .corridorLower 0 1, .thetaLower 0]

-- Original cycle abfd62c7673ad3d9042633d0e307cf0c0a1f4a8c88640a2bca81df6e14554c49; original global index 13399.
def localCycle00171 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 2 3, .distance 0 2, .distance 2 6, .distance 5 6, .distance 3 5, .distance 3 4, .theta 3]
    constant := ![3, -1, -1, 0, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 5 0, .triangle 8 0, .triangle 30 1, .triangle 33 0, .gapLower 3 1, .corridorLower 3 4]

-- Original cycle ac98cff8e277aa6c42eb77c073a2403fa6aba563f95081194d978d3512bc0022; original global index 13450.
def localCycle00172 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 2 3, .distance 1 2, .distance 1 5, .distance 1 4, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, 0, -1, -1, 0, 0, -1, -2, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, true, true, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 27 0, .triangle 15 0, .triangle 17 2, .triangle 22 1, .triangle 2 0, .gapLower 0 0, .thetaLower 0]

-- Original cycle acd9c85c2089f89671d1f56fdb2a8c4836113316bfafef415336a976117a4e32; original global index 13475.
def localCycle00173 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 3, .distance 2 3, .distance 0 2, .distance 0 5, .distance 0 4, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, -1, 0, -2, -2, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, false] }
  origin := ![.thetaUpper 3, .corridorUpper 2 3, .triangle 5 0, .triangle 7 2, .gapLower 0 2, .gapLower 0 1, .corridorLower 0 1, .thetaLower 0]

-- Original cycle ad0b31f83c1e7b5df89240b87543635c350d3f55a02a3874639c342e62b15c86; original global index 13488.
def localCycle00174 : Cycle where
  length := 6
  data := {
    node := ![.theta 3, .distance 2 3, .distance 0 2, .distance 0 4, .distance 4 6, .distance 3 4, .theta 3]
    constant := ![3, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 5 0, .triangle 6 2, .triangle 13 0, .triangle 32 0, .corridorLower 3 4]

-- Original cycle ad693a68ec168212bd179249b6dd12dd1d863b3ed01c4ae7746674b2f25a5b7f; original global index 13527.
def localCycle00175 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 2, .distance 1 6, .distance 0 6, .distance 2 6, .distance 3 6, .distance 3 4, .theta 3]
    constant := ![3, -1, 0, -2, -2, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 0, .triangle 18 2, .gapLower 6 3, .gapLower 6 2, .triangle 27 1, .triangle 32 1, .corridorLower 3 4]

-- Original cycle ae1e7825f010d1bacecd64198f28ec53c2c601ccb1496939c5c5e9f3c645adcd; original global index 13585.
def localCycle00176 : Cycle where
  length := 7
  data := {
    node := ![.theta 6, .distance 5 6, .distance 4 6, .distance 2 6, .distance 1 6, .distance 0 6, .distance 3 6, .theta 6]
    constant := ![3, 0, -2, 0, 0, 0, -2]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, true, true, false] }
  origin := ![.corridorUpper 5 6, .triangle 34 2, .gapLower 6 4, .triangle 18 2, .triangle 4 2, .triangle 11 1, .gapLower 6 0]

-- Original cycle ae43c9700e9af830336c85fc4948782c28ae65cea8171b2ae22978ff09be3910; original global index 13598.
def localCycle00177 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 2 3, .distance 0 2, .distance 2 5, .distance 5 6, .distance 3 5, .distance 3 4, .theta 3]
    constant := ![3, -1, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 5 0, .triangle 7 0, .triangle 30 0, .triangle 33 0, .gapLower 3 1, .corridorLower 3 4]

-- Original cycle aec46a622c1cfd8c6fce819860935025bf8929c9e15d7c9357836b62f84d2079; original global index 13642.
def localCycle00178 : Cycle where
  length := 10
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 3, .distance 0 3, .distance 0 5, .distance 0 6, .distance 0 2, .distance 0 4, .distance 2 4, .distance 3 4, .theta 3]
    constant := ![3, 0, 0, 0, -2, 0, -2, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, true, false, false, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 2, .triangle 1 2, .triangle 10 2, .gapLower 0 4, .triangle 8 1, .gapLower 0 2, .gapLower 4 2, .triangle 25 1, .corridorLower 3 4]

-- Original cycle afa442cc84c3f3d1cc0f24e46d5a1b0fd44dd897bf31c24d4fd717970c419286; original global index 13721.
def localCycle00179 : Cycle where
  length := 7
  data := {
    node := ![.theta 0, .distance 0 6, .distance 0 3, .distance 0 2, .distance 2 4, .theta 2, .theta 1, .theta 0]
    constant := ![2, -2, 0, -1, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, true] }
  origin := ![.gapLower 0 6, .gapLower 0 5, .triangle 5 1, .triangle 6 0, .corridorLower 2 4, .thetaNext 1, .thetaNext 0]

-- Original cycle b01b201444fcce6e0a70a6362cc912e1fc25d6227538cedbd78bba464a7418c0; original global index 13750.
def localCycle00180 : Cycle where
  length := 9
  data := {
    node := ![.theta 0, .distance 0 6, .distance 0 2, .distance 2 5, .distance 3 5, .distance 3 4, .theta 3, .theta 2, .theta 1, .theta 0]
    constant := ![1, 0, -1, 0, 0, -1, 0, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, true, false, true, true, true] }
  origin := ![.gapLower 0 6, .triangle 8 1, .triangle 7 0, .triangle 26 1, .triangle 31 1, .corridorLower 3 4, .thetaNext 2, .thetaNext 1, .thetaNext 0]

-- Original cycle b096fb36b45dd24af79c12198ea3718e6f54fa38eb6ec84e3a0a1ec873a97d71; original global index 13788.
def localCycle00181 : Cycle where
  length := 10
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 3, .distance 0 3, .distance 0 5, .distance 0 6, .distance 0 2, .distance 0 4, .distance 2 4, .distance 3 4, .theta 3]
    constant := ![3, 0, 0, 0, 0, -2, -2, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, true, false, false, false, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 2, .triangle 1 2, .triangle 10 2, .triangle 14 2, .gapLower 0 3, .gapLower 0 2, .gapLower 4 2, .triangle 25 1, .corridorLower 3 4]

-- Original cycle b0e8030c42a7d099e2134bfd2ebd8e181e1e0787be83667ea43205f9c83dc297; original global index 13812.
def localCycle00182 : Cycle where
  length := 7
  data := {
    node := ![.theta 6, .distance 5 6, .distance 4 6, .distance 2 6, .distance 1 6, .distance 0 6, .distance 3 6, .theta 6]
    constant := ![3, 0, 0, 0, 0, -2, -2]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, true, false, false] }
  origin := ![.corridorUpper 5 6, .triangle 34 2, .triangle 29 2, .triangle 18 2, .triangle 4 2, .gapLower 6 1, .gapLower 6 0]

-- Original cycle b50b9817fab86ca9fbe391cb3146b52b7ccf7f649f5e507950025e445a036e48; original global index 14140.
def localCycle00183 : Cycle where
  length := 6
  data := {
    node := ![.theta 3, .distance 2 3, .distance 2 6, .distance 1 6, .distance 0 6, .distance 3 6, .theta 3]
    constant := ![3, 0, -2, 0, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 27 2, .gapLower 6 3, .triangle 4 2, .gapLower 6 1, .corridorLower 3 6]

-- Original cycle b5419bdd2ad315fdf09a1b3688802cc41927bb45953433ba0bf58375aae61431; original global index 14162.
def localCycle00184 : Cycle where
  length := 4
  data := {
    node := ![.distance 1 4, .distance 4 6, .distance 5 6, .distance 1 5, .distance 1 4]
    constant := ![2, -2, -1, 0]
    coefficient := ![0, 0, 0, 0]
    strict := ![true, false, false, false] }
  origin := ![.gapUpper 4 4, .gapLower 6 5, .triangle 24 0, .gapLower 1 2]

-- Original cycle b5833d5eeabe7c11a6f1ecea0fa8389e71c6b2d500b91d5268f8d0c8d597667a; original global index 14185.
def localCycle00185 : Cycle where
  length := 10
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 3, .distance 0 3, .distance 0 6, .distance 0 2, .distance 0 5, .distance 2 5, .distance 3 5, .distance 3 4, .theta 3]
    constant := ![3, 0, 0, -2, 0, -2, 0, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, false, true, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 2, .triangle 1 2, .gapLower 0 5, .triangle 8 1, .gapLower 0 3, .gapLower 5 2, .triangle 26 1, .triangle 31 1, .corridorLower 3 4]

-- Original cycle b63e402108b95723568f73191cfeeb728652b8602dfa86b667c08c2e9acae9ac; original global index 14236.
def localCycle00186 : Cycle where
  length := 6
  data := {
    node := ![.theta 3, .distance 2 3, .distance 0 2, .distance 0 6, .distance 2 6, .distance 3 6, .theta 3]
    constant := ![4, -1, 0, -2, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false] }
  origin := ![.gapLower 3 6, .triangle 5 0, .triangle 8 2, .gapLower 6 2, .gapLower 6 1, .corridorLower 3 6]

-- Original cycle b6556736558e6d5337cc03a87fc63b613c539c5f5f14773cfb762892f3f71215; original global index 14250.
def localCycle00187 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 2, .distance 2 5, .distance 0 2, .distance 2 4, .distance 4 6, .distance 3 4, .theta 3]
    constant := ![3, -1, -1, -1, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 0, .triangle 17 0, .triangle 7 0, .triangle 6 0, .triangle 29 0, .triangle 32 0, .corridorLower 3 4]

-- Original cycle b6aaf03dcd33c2a26507667e6a177a21ca39024d04e76d4b34b1cc3454a53d91; original global index 14277.
def localCycle00188 : Cycle where
  length := 4
  data := {
    node := ![.distance 0 3, .distance 0 5, .distance 5 6, .distance 3 6, .distance 0 3]
    constant := ![-3, 0, 0, 2]
    coefficient := ![0, 0, 0, 0]
    strict := ![false, false, true, true] }
  origin := ![.gapLower 0 5, .gapLower 5 2, .triangle 33 2, .gapUpper 3 3]

-- Original cycle b74c9386eb346ad39843360c34bb7a21afc46c8b34226861234c1aa92aa44806; original global index 14309.
def localCycle00189 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 3, .distance 2 3, .distance 0 2, .distance 0 5, .distance 0 4, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, -1, -2, 0, 0, -2, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, false, false] }
  origin := ![.thetaUpper 3, .corridorUpper 2 3, .triangle 5 0, .gapLower 0 3, .triangle 12 1, .triangle 2 1, .gapLower 0 0, .thetaLower 0]

-- Original cycle b76ebf9fb0d46428e98504b422b471dd870c8255d6fc0e9f1c582c08d92f5b0b; original global index 14317.
def localCycle00190 : Cycle where
  length := 3
  data := {
    node := ![.distance 0 1, .distance 1 4, .distance 0 4, .distance 0 1]
    constant := ![2, 0, -3]
    coefficient := ![0, 0, 0]
    strict := ![true, false, false] }
  origin := ![.gapUpper 1 1, .gapLower 4 3, .gapLower 0 1]

-- Original cycle b8babf067d176dc8a46a626560631023a932f17ec563ba1bef3936dbde0ad615; original global index 14416.
def localCycle00191 : Cycle where
  length := 7
  data := {
    node := ![.theta 5, .distance 4 5, .distance 2 5, .distance 0 2, .distance 2 6, .distance 3 6, .distance 5 6, .theta 5]
    constant := ![3, 0, -1, -1, 0, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, false, false] }
  origin := ![.corridorUpper 4 5, .triangle 28 2, .triangle 7 0, .triangle 8 0, .triangle 27 1, .gapLower 6 1, .corridorLower 5 6]

-- Original cycle b99286821305703d2874dd3e982fad85a79574b7e74df1162a94f62c536136bb; original global index 14480.
def localCycle00192 : Cycle where
  length := 13
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 2 6, .distance 1 6, .distance 0 6, .distance 0 3, .distance 0 5, .distance 0 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, 0, 0, 0, 0, -2, -2, 0, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, true, true, true, false, false, true, true, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 27 2, .triangle 18 2, .triangle 4 2, .gapLower 0 5, .gapLower 0 4, .triangle 7 1, .triangle 0 1, .corridorLower 0 1, .thetaLower 0]

-- Original cycle ba3107f4c7d9e17173eb7544a95f499a9fd77a31cfce157fb886236510450c6e; original global index 14537.
def localCycle00193 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 2 5, .distance 5 6, .distance 1 5, .distance 0 5, .distance 0 2, .distance 2 4, .distance 3 4, .theta 3]
    constant := ![3, 0, -1, -1, 0, 0, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, true, false, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 26 2, .triangle 30 0, .triangle 24 0, .triangle 3 2, .triangle 7 1, .triangle 6 0, .triangle 25 1, .corridorLower 3 4]

-- Original cycle ba9b20c7078ccae5867427e4fa5ced641c4a045f175be69973de5481ba0bb6ce; original global index 14570.
def localCycle00194 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 2 3, .distance 0 2, .distance 0 5, .distance 0 4, .theta 0, .zero]
    constant := ![0, 3, 0, 0, -1, -1, 0, -2, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, true, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 27 0, .triangle 5 0, .triangle 7 2, .gapLower 0 2, .corridorLower 0 4, .thetaLower 0]

-- Original cycle bb73012a495425a643877428927ba2ba32c70ba7e63ec9c6507b9b583f6a5447; original global index 14631.
def localCycle00195 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 6, .distance 4 6, .distance 5 6, .distance 1 5, .distance 1 4, .distance 0 1, .theta 0, .zero]
    constant := ![0, 1, 0, -1, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 34 1, .triangle 24 0, .triangle 22 1, .triangle 2 0, .corridorLower 0 1, .thetaLower 0]

-- Original cycle bd01f8d573269d17c37c6096ab71efed79aad72613a349b4b24bfa8e9ffd3c5c; original global index 14744.
def localCycle00196 : Cycle where
  length := 3
  data := {
    node := ![.distance 0 5, .distance 0 6, .distance 5 6, .distance 0 5]
    constant := ![-2, 0, 2]
    coefficient := ![0, 0, 0]
    strict := ![false, true, true] }
  origin := ![.gapLower 0 4, .triangle 14 1, .gapUpper 5 2]

-- Original cycle bd7e9656b5159af002e0b04971df3863b0745475f2cf91e7fb82e4424a9c9ffc; original global index 14781.
def localCycle00197 : Cycle where
  length := 3
  data := {
    node := ![.distance 1 2, .distance 2 6, .distance 1 6, .distance 1 2]
    constant := ![2, -3, 0]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.gapUpper 2 4, .gapLower 6 3, .triangle 18 1]

-- Original cycle be492b6bbcb6ad7741e46d5b2f0c21d422edc5df529f9563887eea2b91780994; original global index 14842.
def localCycle00198 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 0 5, .distance 0 2, .distance 2 4, .distance 3 4, .theta 3, .zero]
    constant := ![0, 3, -1, -2, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 14 0, .gapLower 0 3, .triangle 6 0, .triangle 25 1, .corridorLower 3 4, .thetaLower 3]

-- Original cycle be778862b44d8b25f369eb3124860de0583ec45632d7e07b246754205417b6d4; original global index 14859.
def localCycle00199 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 2, .distance 1 5, .distance 1 4, .distance 4 6, .distance 3 4, .theta 3]
    constant := ![3, -1, 0, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 0, .triangle 17 2, .triangle 22 1, .triangle 23 0, .triangle 32 0, .corridorLower 3 4]

-- Original cycle bfb454078e219972b52b6b3b77b35032ddc2b11c4090aa48b115b5d63825bd14; original global index 14955.
def localCycle00200 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 2, .distance 1 5, .distance 5 6, .distance 2 5, .distance 0 2, .distance 2 4, .distance 3 4, .theta 3]
    constant := ![3, -1, 0, -1, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 0, .triangle 17 2, .triangle 24 0, .triangle 30 0, .triangle 7 0, .triangle 6 0, .triangle 25 1, .corridorLower 3 4]

-- Original cycle c09a8407e18fa3f3779196e8db32493a43f757e1cae2e7ebbf5b5d6ce1c089a6; original global index 15036.
def localCycle00201 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 2 6, .distance 1 6, .distance 0 6, .distance 0 3, .distance 0 2, .distance 0 4, .theta 0, .zero]
    constant := ![0, 3, 0, 0, 0, 0, 0, -2, 0, -2, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, true, true, true, false, true, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 27 2, .triangle 18 2, .triangle 4 2, .gapLower 0 5, .triangle 5 1, .gapLower 0 2, .corridorLower 0 4, .thetaLower 0]

-- Original cycle c2e6aca958a3169557f548f7ee2ba836e8fa8d5040455a437eb61eadc131180a; original global index 15209.
def localCycle00202 : Cycle where
  length := 3
  data := {
    node := ![.distance 1 4, .distance 4 6, .distance 1 6, .distance 1 4]
    constant := ![2, -3, 0]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.gapUpper 4 4, .gapLower 6 5, .triangle 23 1]

-- Original cycle c33f48574f654c67eceea522e4fd443c11020034ae9f4b1998daf854a4b2848a; original global index 15233.
def localCycle00203 : Cycle where
  length := 11
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 2, .distance 1 5, .distance 1 4, .distance 4 6, .distance 5 6, .distance 2 5, .distance 0 2, .distance 2 4, .distance 3 4, .theta 3]
    constant := ![3, -1, 0, 0, -1, 0, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, true, false, false, false, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 0, .triangle 17 2, .triangle 22 1, .triangle 23 0, .triangle 34 1, .triangle 30 0, .triangle 7 0, .triangle 6 0, .triangle 25 1, .corridorLower 3 4]

-- Original cycle c3fbfb05410ba08c02a096f8364a84549a167bd2a1535cff9f1f5785b12e1848; original global index 15287.
def localCycle00204 : Cycle where
  length := 10
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 3, .distance 0 3, .distance 0 6, .distance 0 2, .distance 0 5, .distance 0 4, .distance 2 4, .distance 3 4, .theta 3]
    constant := ![3, 0, 0, 0, -2, 0, -2, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, true, false, false, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 2, .triangle 1 2, .triangle 11 2, .gapLower 0 4, .triangle 7 2, .gapLower 0 2, .gapLower 4 2, .triangle 25 1, .corridorLower 3 4]

-- Original cycle c5fcb047a2d4733780997b6509f1e6cb801873bf916044519471a1b721549bde; original global index 15442.
def localCycle00205 : Cycle where
  length := 9
  data := {
    node := ![.theta 0, .distance 0 3, .distance 0 2, .distance 2 5, .distance 3 5, .distance 3 4, .theta 3, .theta 2, .theta 1, .theta 0]
    constant := ![1, 0, -1, 0, 0, -1, 0, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, true, false, true, true, true] }
  origin := ![.gapLower 0 6, .triangle 5 1, .triangle 7 0, .triangle 26 1, .triangle 31 1, .corridorLower 3 4, .thetaNext 2, .thetaNext 1, .thetaNext 0]

-- Original cycle c60faa0d9d01e952cbc17b216106cb45009a9fc2c92f0bc0e70459bb2603089e; original global index 15447.
def localCycle00206 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 2 3, .distance 0 2, .distance 2 5, .distance 2 4, .distance 4 6, .distance 3 4, .theta 3]
    constant := ![3, -1, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 5 0, .triangle 7 0, .triangle 28 1, .triangle 29 0, .triangle 32 0, .corridorLower 3 4]

-- Original cycle c8d4e0184c4643d8ac937e884ee3206b112e9fad5f8fe585f7516ea73be994eb; original global index 15686.
def localCycle00207 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 2, .distance 1 6, .distance 0 6, .distance 2 6, .distance 3 6, .distance 3 4, .theta 3]
    constant := ![3, -1, 0, -2, 0, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, true, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 0, .triangle 18 2, .gapLower 6 3, .triangle 8 1, .triangle 27 1, .triangle 32 1, .corridorLower 3 4]

-- Original cycle c965e99ea79d58053244c5abcc0db1ecea1780c2e89350a31cb44a66e54c531f; original global index 15743.
def localCycle00208 : Cycle where
  length := 3
  data := {
    node := ![.distance 0 3, .distance 0 6, .distance 3 6, .distance 0 3]
    constant := ![0, -3, 2]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.triangle 11 2, .gapLower 6 1, .gapUpper 3 3]

-- Original cycle ca012fc96290984c31eeca5546a9ff27c291496ff099891bb21e8b7d3ceeaac1; original global index 15788.
def localCycle00209 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 2 6, .distance 1 6, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, -2, -2, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .gapLower 6 4, .gapLower 6 3, .triangle 4 0, .corridorLower 0 1, .thetaLower 0]

-- Original cycle cb67f0b5735f8930f646a9e2a1daa9168b9b01ae4d71a020a43532639f9a3fbb; original global index 15891.
def localCycle00210 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 2 3, .distance 0 2, .distance 0 5, .distance 0 4, .distance 2 4, .distance 3 4, .theta 3]
    constant := ![3, -1, -2, -2, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 5 0, .gapLower 0 3, .gapLower 0 2, .gapLower 4 2, .triangle 25 1, .corridorLower 3 4]

-- Original cycle cb990df9b37e871f876601ae572a457de57216e76391d3fb7f496aadc2679724; original global index 15908.
def localCycle00211 : Cycle where
  length := 13
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 5 6, .distance 2 5, .distance 1 2, .distance 0 2, .distance 2 4, .distance 3 4, .theta 3, .theta 2, .theta 1, .theta 0, .zero]
    constant := ![0, 3, -1, -1, -1, 0, -1, 0, -1, 0, 0, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, true, false, true, true, true, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 34 0, .triangle 30 0, .triangle 17 0, .triangle 0 2, .triangle 6 0, .triangle 25 1, .corridorLower 3 4, .thetaNext 2, .thetaNext 1, .thetaNext 0, .thetaLower 0]

-- Original cycle cc8b9285f583bdc3bfe55af4d1a923ec3d38c7de177b7ed6df153e7dcfcc0f30; original global index 15986.
def localCycle00212 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 2, .distance 2 5, .distance 5 6, .distance 3 5, .distance 3 4, .theta 3]
    constant := ![3, -1, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 0, .triangle 17 0, .triangle 30 0, .triangle 33 0, .gapLower 3 1, .corridorLower 3 4]

-- Original cycle ccd90f706a10b739347092a917953470297560bc7e3d71a795c251f31b46c238; original global index 16011.
def localCycle00213 : Cycle where
  length := 9
  data := {
    node := ![.theta 0, .distance 0 3, .distance 0 5, .distance 5 6, .distance 3 5, .distance 3 4, .theta 3, .theta 2, .theta 1, .theta 0]
    constant := ![1, 0, -1, -1, 0, -1, 0, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, true, true, true] }
  origin := ![.gapLower 0 6, .triangle 10 2, .triangle 14 0, .triangle 33 0, .gapLower 3 1, .corridorLower 3 4, .thetaNext 2, .thetaNext 1, .thetaNext 0]

-- Original cycle d1644c500199380502a8de72189497c0e77bc45beabae4ca49927aad89d48461; original global index 16343.
def localCycle00214 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 2, .distance 2 5, .distance 0 2, .distance 2 6, .distance 3 6, .distance 3 4, .theta 3]
    constant := ![3, -1, -1, -1, -1, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 0, .triangle 17 0, .triangle 7 0, .triangle 8 0, .triangle 27 1, .triangle 32 1, .corridorLower 3 4]

-- Original cycle d3279752e75b8b5e6fce4c50f8dea3ac3df5f0325feffb7a16d2efbd7a678c4d; original global index 16470.
def localCycle00215 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 2, .distance 2 5, .distance 0 2, .distance 2 4, .distance 3 4, .theta 3]
    constant := ![3, -1, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 0, .triangle 17 0, .triangle 7 0, .triangle 6 0, .triangle 25 1, .corridorLower 3 4]

-- Original cycle d33db5f3f4b727344de65bcf56af875e74da6dd79c3a6c11087c3ededd55bc90; original global index 16478.
def localCycle00216 : Cycle where
  length := 7
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 5 6, .distance 1 6, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, -1, -2, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 34 0, .gapLower 6 4, .triangle 4 0, .corridorLower 0 1, .thetaLower 0]

-- Original cycle d3754e39a8c7591290fa6f2f4e15bc16a31c261454bdd814ccebc8a42022b9cb; original global index 16496.
def localCycle00217 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 2, .distance 1 4, .distance 4 6, .distance 4 5, .distance 2 4, .distance 3 4, .theta 3]
    constant := ![3, -1, 0, -1, 0, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 0, .triangle 16 2, .triangle 23 0, .triangle 34 1, .triangle 28 0, .triangle 25 1, .corridorLower 3 4]

-- Original cycle d497c24147d3f224b221fad8a8507fb88ef0e0352a96d678f49da83bbeaedae1; original global index 16586.
def localCycle00218 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 2, .distance 1 6, .distance 0 6, .distance 2 6, .distance 3 6, .distance 3 4, .theta 3]
    constant := ![3, -1, 0, -3, 0, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, true, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 0, .triangle 18 2, .gapLower 6 3, .triangle 8 1, .triangle 27 1, .triangle 32 1, .corridorLower 3 4]

-- Original cycle d645f60bbb2d6f4f2847d8f34406e7d826b2a992909b568c75d8cb2f9994a75e; original global index 16728.
def localCycle00219 : Cycle where
  length := 8
  data := {
    node := ![.theta 5, .distance 4 5, .distance 2 5, .distance 0 2, .distance 2 6, .distance 3 6, .distance 5 6, .theta 6, .theta 5]
    constant := ![3, 0, -1, -1, 0, 0, -3, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, true, false, true] }
  origin := ![.corridorUpper 4 5, .triangle 28 2, .triangle 7 0, .triangle 8 0, .triangle 27 1, .triangle 33 1, .gapLower 6 0, .thetaNext 5]

-- Original cycle d7869479b2841a34d41d02292df33e6a75f6ef99642e28e32dee0fb266228511; original global index 16819.
def localCycle00220 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 2 3, .distance 0 2, .distance 2 6, .distance 3 6, .distance 3 5, .distance 3 4, .theta 3]
    constant := ![3, -1, -1, -2, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 5 0, .triangle 8 0, .gapLower 6 1, .triangle 33 1, .triangle 31 1, .corridorLower 3 4]

-- Original cycle da6d3a330a87f035eac15e0d7fa0b65980703609567e7e436d74a87f68494aaf; original global index 17070.
def localCycle00221 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 2, .distance 1 4, .distance 4 6, .distance 2 4, .distance 3 4, .theta 3]
    constant := ![3, -1, 0, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 0, .triangle 16 2, .triangle 23 0, .triangle 29 0, .triangle 25 1, .corridorLower 3 4]

-- Original cycle da8580001325260e7a2f8ea58fdfefb439e390becea4079f42c36ca44727fc66; original global index 17077.
def localCycle00222 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 2 3, .distance 1 2, .distance 1 4, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, 0, -1, -1, 0, -1, -2, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, true, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 27 0, .triangle 15 0, .triangle 16 2, .triangle 2 0, .gapLower 0 0, .thetaLower 0]

-- Original cycle da988cc2338e70dd022ac6ab3c69bf35ad8ad06bb54ca4f34a53e6a30b4179c6; original global index 17083.
def localCycle00223 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 2 3, .distance 0 2, .distance 0 5, .distance 0 4, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, 0, -1, -1, 0, -2, -2, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, true, false, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 27 0, .triangle 5 0, .triangle 7 2, .gapLower 0 2, .gapLower 0 1, .corridorLower 0 1, .thetaLower 0]

-- Original cycle dc04151c255f5e963a12de3afbf5188f325eebb29798c219fdea9b7ab1e4e796; original global index 17198.
def localCycle00224 : Cycle where
  length := 3
  data := {
    node := ![.distance 0 5, .distance 0 6, .distance 5 6, .distance 0 5]
    constant := ![-3, 0, 2]
    coefficient := ![0, 0, 0]
    strict := ![false, true, true] }
  origin := ![.gapLower 0 4, .triangle 14 1, .gapUpper 5 2]

-- Original cycle dc587b273d721a85f151e29f53cd534d7245a9e2dc79079eb61da9090f60add0; original global index 17221.
def localCycle00225 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 2 6, .distance 0 2, .distance 2 4, .distance 3 4, .theta 3, .theta 2, .zero]
    constant := ![0, 3, 0, -2, -1, -1, 0, -1, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, true, false, true, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .gapLower 6 4, .triangle 8 0, .triangle 6 0, .triangle 25 1, .corridorLower 3 4, .thetaNext 2, .thetaLower 2]

-- Original cycle dc6e51796ee35445802a9493c897a74a70aeb9244fed31ddfca4b3474374f7db; original global index 17226.
def localCycle00226 : Cycle where
  length := 8
  data := {
    node := ![.theta 5, .distance 4 5, .distance 2 5, .distance 0 2, .distance 2 6, .distance 3 6, .distance 5 6, .theta 6, .theta 5]
    constant := ![3, 0, -1, -1, 0, -2, -2, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, false, false, true] }
  origin := ![.corridorUpper 4 5, .triangle 28 2, .triangle 7 0, .triangle 8 0, .triangle 27 1, .gapLower 6 1, .gapLower 6 0, .thetaNext 5]

-- Original cycle dd0b59912d36fd28d0377fdb7d7ea1eaaa52cf888c07884ab20b273e48ccd960; original global index 17279.
def localCycle00227 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 2 3, .distance 0 2, .distance 0 5, .distance 0 4, .theta 0, .zero]
    constant := ![0, 3, 0, 0, -1, -1, 0, -3, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, true, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 27 0, .triangle 5 0, .triangle 7 2, .gapLower 0 2, .corridorLower 0 4, .thetaLower 0]

-- Original cycle dfe29c603dae67e669cd9a7132d7975dddb8147e4f221d4f5f103d697199ceaa; original global index 17496.
def localCycle00228 : Cycle where
  length := 7
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 1 6, .distance 0 6, .theta 0, .zero]
    constant := ![0, 3, -2, 0, -2, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .gapLower 6 5, .triangle 23 2, .gapLower 6 2, .corridorLower 0 6, .thetaLower 0]

-- Original cycle e1b18af4ab64c08e6e63c8839a11cc78f306156c4569ffb85ee604caa501d49d; original global index 17648.
def localCycle00229 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 4 6, .distance 3 6, .distance 2 3, .distance 1 2, .distance 2 5, .distance 0 2, .distance 2 4, .distance 3 4, .theta 3, .zero]
    constant := ![0, 3, 0, 0, -1, -1, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, false, false, true, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 34 2, .triangle 32 2, .triangle 27 0, .triangle 15 0, .triangle 17 0, .triangle 7 0, .triangle 6 0, .triangle 25 1, .corridorLower 3 4, .thetaLower 3]

-- Original cycle e1cc5e7b771e89f89b543602778e7b0e6384609091eca1adadeb784d093e66a4; original global index 17656.
def localCycle00230 : Cycle where
  length := 15
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 2 6, .distance 1 6, .distance 0 6, .distance 0 3, .distance 0 2, .distance 2 5, .distance 3 5, .distance 3 4, .theta 3, .theta 2, .zero]
    constant := ![0, 3, 0, 0, 0, 0, 0, -3, 0, -1, 0, 0, -1, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, true, true, true, false, true, false, true, true, false, true, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 27 2, .triangle 18 2, .triangle 4 2, .gapLower 0 5, .triangle 5 1, .triangle 7 0, .triangle 26 1, .triangle 31 1, .corridorLower 3 4, .thetaNext 2, .thetaLower 2]

-- Original cycle e2dbed1a731a786231988387cab8e4a0e68ef00e1541e12b68a7bb4aea1dc813; original global index 17745.
def localCycle00231 : Cycle where
  length := 4
  data := {
    node := ![.theta 0, .distance 0 3, .distance 0 2, .distance 0 5, .theta 0]
    constant := ![2, 0, -2, -1]
    coefficient := ![1, 0, 0, 0]
    strict := ![false, true, false, false] }
  origin := ![.gapLower 0 6, .triangle 5 1, .gapLower 0 3, .corridorLower 0 5]

-- Original cycle e34d08b4860689528d923792d033f267dbeaeb724b3b8c479c1747a89f7c3262; original global index 17775.
def localCycle00232 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 3, .distance 0 3, .distance 0 5, .distance 0 6, .distance 0 2, .distance 2 4, .distance 3 4, .theta 3]
    constant := ![3, 0, 0, -2, -2, 0, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, true, false, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 2, .triangle 1 2, .gapLower 0 5, .gapLower 0 4, .triangle 8 1, .triangle 6 0, .triangle 25 1, .corridorLower 3 4]

-- Original cycle e3bb372fcaef8247878717490c8f26bc94ed1f985ca2a550f0d269b1906481de; original global index 17808.
def localCycle00233 : Cycle where
  length := 3
  data := {
    node := ![.distance 1 5, .distance 5 6, .distance 1 6, .distance 1 5]
    constant := ![2, -3, 0]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.gapUpper 5 4, .gapLower 6 4, .triangle 24 1]

-- Original cycle e43a03fa52b26bbf611630173faa638924abcb82d16dca50331b17727be8d5e5; original global index 17845.
def localCycle00234 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 0 3, .distance 0 5, .distance 0 2, .distance 2 4, .distance 3 4, .theta 3, .zero]
    constant := ![0, 3, 0, 0, -1, -2, 0, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, true, false, true, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 11 0, .gapLower 0 4, .triangle 7 1, .triangle 6 0, .triangle 25 1, .corridorLower 3 4, .thetaLower 3]

-- Original cycle e4ee758388324c7d9e5cd71cd74c5efb21d93e46389c2a6bd312da3957a9f905; original global index 17898.
def localCycle00235 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 5 6, .distance 1 6, .distance 0 6, .distance 2 6, .theta 2, .zero]
    constant := ![0, 3, -1, -2, 0, -2, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 34 0, .gapLower 6 4, .triangle 4 2, .gapLower 6 2, .corridorLower 2 6, .thetaLower 2]

-- Original cycle e6b544cc4469e2a3ff5d21c6a0965f71d37215220e89767ad0e5f1da27d709ba; original global index 18045.
def localCycle00236 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 2, .distance 1 6, .distance 0 6, .distance 2 6, .distance 3 6, .distance 3 4, .theta 3]
    constant := ![3, -1, 0, -3, 0, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, true, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 0, .triangle 18 2, .gapLower 6 4, .triangle 8 1, .triangle 27 1, .triangle 32 1, .corridorLower 3 4]

-- Original cycle ea4aee8c1ca550451c1fdbd4dbdff3fc56fbdc793a57424c534fb53506930747; original global index 18296.
def localCycle00237 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 3, .distance 0 3, .distance 3 6, .theta 6, .theta 5, .theta 4, .theta 3]
    constant := ![3, 0, 0, -1, -3, 0, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, true, true, true] }
  origin := ![.corridorUpper 2 3, .triangle 15 2, .triangle 1 2, .triangle 11 0, .gapLower 6 0, .thetaNext 5, .thetaNext 4, .thetaNext 3]

-- Original cycle ed026539a7806adc4309a3a6ce3c6b2dcc29619e198754dac5ea43c46b459f32; original global index 18500.
def localCycle00238 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 2 3, .distance 0 2, .distance 0 4, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, 0, -1, -1, -2, -2, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 27 0, .triangle 5 0, .gapLower 0 2, .gapLower 0 1, .corridorLower 0 1, .thetaLower 0]

-- Original cycle edadf13afe562c3a22eb3fad339699938cb92bcd6f9940cdf3ac9eeeb8fe2dbb; original global index 18556.
def localCycle00239 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 2, .distance 1 4, .distance 4 5, .distance 2 5, .distance 5 6, .distance 3 5, .distance 3 4, .theta 3]
    constant := ![3, -1, 0, -1, 0, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 0, .triangle 16 2, .triangle 22 0, .triangle 28 2, .triangle 30 0, .triangle 33 0, .gapLower 3 1, .corridorLower 3 4]

-- Original cycle ef0079eba967bf5208d979de29209b58368f8089a455103bb1171d3fa703d54f; original global index 18650.
def localCycle00240 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 2, .distance 2 6, .distance 5 6, .distance 0 5, .distance 0 2, .distance 2 4, .distance 3 4, .theta 3]
    constant := ![3, -1, -1, 0, -1, 0, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true, false, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 0, .triangle 18 0, .triangle 30 1, .triangle 14 0, .triangle 7 1, .triangle 6 0, .triangle 25 1, .corridorLower 3 4]

-- Original cycle efb10a30d112867ef204f530900deced6b35138582d89933368b956a50ef3515; original global index 18696.
def localCycle00241 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 2 6, .distance 1 6, .distance 0 6, .distance 3 6, .distance 3 5, .distance 3 4, .theta 3]
    constant := ![3, 0, -2, 0, -2, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, true, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 27 2, .gapLower 6 3, .triangle 4 2, .gapLower 6 1, .triangle 33 1, .triangle 31 1, .corridorLower 3 4]

-- Original cycle f00683e50e755ab0cb2441a607b26d7b35b6b6fefa2a696347a54e59e914fc4b; original global index 18729.
def localCycle00242 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 3, .distance 0 3, .distance 0 5, .distance 0 6, .distance 0 2, .distance 2 4, .distance 3 4, .theta 3]
    constant := ![3, 0, 0, -2, 0, -2, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, false, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 2, .triangle 1 2, .gapLower 0 5, .triangle 14 2, .gapLower 0 3, .triangle 6 0, .triangle 25 1, .corridorLower 3 4]

-- Original cycle f1ab80957b475d5d4128082ffc15fcc1497ac7d468873626df908b6e3d035c97; original global index 18844.
def localCycle00243 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 2, .distance 1 4, .distance 4 5, .distance 2 5, .distance 0 2, .distance 2 6, .distance 3 6, .theta 3]
    constant := ![3, -1, 0, -1, 0, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 0, .triangle 16 2, .triangle 22 0, .triangle 28 2, .triangle 7 0, .triangle 8 0, .triangle 27 1, .corridorLower 3 6]

-- Original cycle f5051d1a551e8b5be345ba5202257eaf3587004e4f1ed71e2303bf0f94e3a6d5; original global index 19104.
def localCycle00244 : Cycle where
  length := 3
  data := {
    node := ![.distance 0 2, .distance 0 4, .distance 2 4, .distance 0 2]
    constant := ![-3, 0, 2]
    coefficient := ![0, 0, 0]
    strict := ![false, false, true] }
  origin := ![.gapLower 0 2, .gapLower 4 2, .gapUpper 2 1]

-- Original cycle f7830cb73231077282f3377a7985770a1cde9234d4d28e7ed32c43cbad54bc0b; original global index 19303.
def localCycle00245 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 2, .distance 1 4, .distance 4 5, .distance 3 5, .distance 0 3, .distance 3 6, .distance 3 4, .theta 3]
    constant := ![3, -1, 0, -1, 0, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 0, .triangle 16 2, .triangle 22 0, .triangle 31 2, .triangle 10 0, .triangle 11 0, .triangle 32 1, .corridorLower 3 4]

-- Original cycle f99458bd340cdf790e5fe4d641731b834d6c64642a9591f65624c455bc39f806; original global index 19455.
def localCycle00246 : Cycle where
  length := 7
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 1 6, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, -2, -2, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .gapLower 6 5, .gapLower 6 4, .triangle 4 0, .corridorLower 0 1, .thetaLower 0]

-- Original cycle f9c0d85c6a263f42073f81e7fdbb79c5e2cc23ea342f6dfe792946e7bb9ae846; original global index 19473.
def localCycle00247 : Cycle where
  length := 10
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 2, .distance 1 6, .distance 0 6, .distance 2 6, .distance 3 6, .theta 6, .theta 5, .theta 4, .theta 3]
    constant := ![3, -1, 0, -2, 0, 0, -2, 0, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, true, false, true, true, true] }
  origin := ![.corridorUpper 2 3, .triangle 15 0, .triangle 18 2, .gapLower 6 3, .triangle 8 1, .triangle 27 1, .gapLower 6 0, .thetaNext 5, .thetaNext 4, .thetaNext 3]

-- Original cycle f9eb6f7b0cf9f43cdc6b7829d8fd7d822377e4d503cedfa9544ecda08d9505c5; original global index 19489.
def localCycle00248 : Cycle where
  length := 4
  data := {
    node := ![.distance 1 4, .distance 4 6, .distance 5 6, .distance 1 5, .distance 1 4]
    constant := ![2, -3, -1, 0]
    coefficient := ![0, 0, 0, 0]
    strict := ![true, false, false, false] }
  origin := ![.gapUpper 4 4, .gapLower 6 5, .triangle 24 0, .gapLower 1 2]

-- Original cycle f9f9e359b250ae3e41cb8d3483675199cc53fb468f25aa679535ce4fb9f91c16; original global index 19491.
def localCycle00249 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 2 6, .distance 1 6, .distance 0 6, .distance 0 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, -2, 0, -2, 0, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, true, true, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .gapLower 6 4, .triangle 18 2, .gapLower 6 2, .triangle 8 1, .triangle 0 1, .corridorLower 0 1, .thetaLower 0]

-- Original cycle fb1fd4b84f1e86a2206a5371511d5543b76b78f53a9a99e3fca3e0da37392713; original global index 19602.
def localCycle00250 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 0 2, .distance 0 6, .distance 2 6, .distance 3 6, .theta 6, .theta 5, .theta 4, .theta 3]
    constant := ![3, -1, 0, -2, 0, -2, 0, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, true, true, true] }
  origin := ![.corridorUpper 2 3, .triangle 5 0, .triangle 8 2, .gapLower 6 2, .triangle 27 1, .gapLower 6 0, .thetaNext 5, .thetaNext 4, .thetaNext 3]

-- Original cycle fbe2737cac1c77f6006056e535359a3295697452951d62eb540d4cc403bafdad; original global index 19663.
def localCycle00251 : Cycle where
  length := 3
  data := {
    node := ![.distance 0 2, .distance 0 6, .distance 2 6, .distance 0 2]
    constant := ![0, -3, 2]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.triangle 8 2, .gapLower 6 3, .gapUpper 2 2]

-- Original cycle fbfe2f244af7d302b0b317ca7df5cfa2cedb91a91df010af445400e2610dcd47; original global index 19674.
def localCycle00252 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 5 6, .distance 0 5, .distance 0 4, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, -1, -1, -2, 0, -2, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 34 0, .triangle 14 0, .gapLower 0 2, .triangle 2 1, .gapLower 0 0, .thetaLower 0]

-- Original cycle fc0236a7ce5275f6daab68a3d69d664921d8de17d38e6ec71c92e4cc4766df13; original global index 19676.
def localCycle00253 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 2 3, .distance 0 2, .distance 0 6, .distance 2 6, .distance 3 6, .distance 3 4, .theta 3]
    constant := ![3, -1, 0, -2, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 5 0, .triangle 8 2, .gapLower 6 3, .triangle 27 1, .triangle 32 1, .corridorLower 3 4]

-- Original cycle fc333e0183f7e43a9cbf27971998138b2087345f132b2179f5508cd65b5bb6bb; original global index 19696.
def localCycle00254 : Cycle where
  length := 4
  data := {
    node := ![.distance 0 2, .distance 2 5, .distance 3 5, .distance 0 3, .distance 0 2]
    constant := ![0, 0, 2, -2]
    coefficient := ![0, 0, 0, 0]
    strict := ![false, true, true, false] }
  origin := ![.gapLower 2 2, .triangle 26 1, .gapUpper 3 2, .gapLower 0 4]

-- Original cycle fdf59f28d3f3a2389732b97832f7dcb8d369f57534afb905af644a0372f67b10; original global index 19845.
def localCycle00255 : Cycle where
  length := 13
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 3, .distance 0 3, .distance 3 6, .theta 6, .distance 5 6, .distance 4 6, .distance 2 6, .distance 2 5, .distance 0 2, .distance 2 4, .distance 3 4, .theta 3]
    constant := ![3, 0, 0, -1, -2, 3, -2, 0, 0, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, false, false, true, true, false, false, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 2, .triangle 1 2, .triangle 11 0, .gapLower 6 0, .corridorUpper 5 6, .gapLower 6 5, .triangle 29 2, .triangle 30 1, .triangle 7 0, .triangle 6 0, .triangle 25 1, .corridorLower 3 4]

-- Original cycle fe160dc3c245634c78562e55b37bd6e8895bc939223c1c50bfcd47e21735628a; original global index 19858.
def localCycle00256 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 3, .distance 3 6, .distance 0 3, .distance 0 2, .distance 2 5, .distance 3 5, .distance 3 4, .theta 3]
    constant := ![3, 0, -1, -1, 0, -1, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, false, true, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 2, .triangle 21 0, .triangle 11 0, .triangle 5 1, .triangle 7 0, .triangle 26 1, .triangle 31 1, .corridorLower 3 4]

-- Original cycle ff46feb576139f30fa0c3e8546feb181b0d5ea6ad43e728987c5a46bc2e8bd59; original global index 19956.
def localCycle00257 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 2, .distance 2 6, .distance 0 2, .distance 2 4, .distance 3 4, .theta 3]
    constant := ![3, -1, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 0, .triangle 18 0, .triangle 8 0, .triangle 6 0, .triangle 25 1, .corridorLower 3 4]

def library : Library := fun id => if id < 129 then (if id < 64 then (if id < 32 then (if id < 16 then (if id < 8 then (if id < 4 then (if id < 2 then (if id < 1 then (if id = 0 then some localCycle00000 else none) else (if id = 1 then some localCycle00001 else none)) else (if id < 3 then (if id = 2 then some localCycle00002 else none) else (if id = 3 then some localCycle00003 else none))) else (if id < 6 then (if id < 5 then (if id = 4 then some localCycle00004 else none) else (if id = 5 then some localCycle00005 else none)) else (if id < 7 then (if id = 6 then some localCycle00006 else none) else (if id = 7 then some localCycle00007 else none)))) else (if id < 12 then (if id < 10 then (if id < 9 then (if id = 8 then some localCycle00008 else none) else (if id = 9 then some localCycle00009 else none)) else (if id < 11 then (if id = 10 then some localCycle00010 else none) else (if id = 11 then some localCycle00011 else none))) else (if id < 14 then (if id < 13 then (if id = 12 then some localCycle00012 else none) else (if id = 13 then some localCycle00013 else none)) else (if id < 15 then (if id = 14 then some localCycle00014 else none) else (if id = 15 then some localCycle00015 else none))))) else (if id < 24 then (if id < 20 then (if id < 18 then (if id < 17 then (if id = 16 then some localCycle00016 else none) else (if id = 17 then some localCycle00017 else none)) else (if id < 19 then (if id = 18 then some localCycle00018 else none) else (if id = 19 then some localCycle00019 else none))) else (if id < 22 then (if id < 21 then (if id = 20 then some localCycle00020 else none) else (if id = 21 then some localCycle00021 else none)) else (if id < 23 then (if id = 22 then some localCycle00022 else none) else (if id = 23 then some localCycle00023 else none)))) else (if id < 28 then (if id < 26 then (if id < 25 then (if id = 24 then some localCycle00024 else none) else (if id = 25 then some localCycle00025 else none)) else (if id < 27 then (if id = 26 then some localCycle00026 else none) else (if id = 27 then some localCycle00027 else none))) else (if id < 30 then (if id < 29 then (if id = 28 then some localCycle00028 else none) else (if id = 29 then some localCycle00029 else none)) else (if id < 31 then (if id = 30 then some localCycle00030 else none) else (if id = 31 then some localCycle00031 else none)))))) else (if id < 48 then (if id < 40 then (if id < 36 then (if id < 34 then (if id < 33 then (if id = 32 then some localCycle00032 else none) else (if id = 33 then some localCycle00033 else none)) else (if id < 35 then (if id = 34 then some localCycle00034 else none) else (if id = 35 then some localCycle00035 else none))) else (if id < 38 then (if id < 37 then (if id = 36 then some localCycle00036 else none) else (if id = 37 then some localCycle00037 else none)) else (if id < 39 then (if id = 38 then some localCycle00038 else none) else (if id = 39 then some localCycle00039 else none)))) else (if id < 44 then (if id < 42 then (if id < 41 then (if id = 40 then some localCycle00040 else none) else (if id = 41 then some localCycle00041 else none)) else (if id < 43 then (if id = 42 then some localCycle00042 else none) else (if id = 43 then some localCycle00043 else none))) else (if id < 46 then (if id < 45 then (if id = 44 then some localCycle00044 else none) else (if id = 45 then some localCycle00045 else none)) else (if id < 47 then (if id = 46 then some localCycle00046 else none) else (if id = 47 then some localCycle00047 else none))))) else (if id < 56 then (if id < 52 then (if id < 50 then (if id < 49 then (if id = 48 then some localCycle00048 else none) else (if id = 49 then some localCycle00049 else none)) else (if id < 51 then (if id = 50 then some localCycle00050 else none) else (if id = 51 then some localCycle00051 else none))) else (if id < 54 then (if id < 53 then (if id = 52 then some localCycle00052 else none) else (if id = 53 then some localCycle00053 else none)) else (if id < 55 then (if id = 54 then some localCycle00054 else none) else (if id = 55 then some localCycle00055 else none)))) else (if id < 60 then (if id < 58 then (if id < 57 then (if id = 56 then some localCycle00056 else none) else (if id = 57 then some localCycle00057 else none)) else (if id < 59 then (if id = 58 then some localCycle00058 else none) else (if id = 59 then some localCycle00059 else none))) else (if id < 62 then (if id < 61 then (if id = 60 then some localCycle00060 else none) else (if id = 61 then some localCycle00061 else none)) else (if id < 63 then (if id = 62 then some localCycle00062 else none) else (if id = 63 then some localCycle00063 else none))))))) else (if id < 96 then (if id < 80 then (if id < 72 then (if id < 68 then (if id < 66 then (if id < 65 then (if id = 64 then some localCycle00064 else none) else (if id = 65 then some localCycle00065 else none)) else (if id < 67 then (if id = 66 then some localCycle00066 else none) else (if id = 67 then some localCycle00067 else none))) else (if id < 70 then (if id < 69 then (if id = 68 then some localCycle00068 else none) else (if id = 69 then some localCycle00069 else none)) else (if id < 71 then (if id = 70 then some localCycle00070 else none) else (if id = 71 then some localCycle00071 else none)))) else (if id < 76 then (if id < 74 then (if id < 73 then (if id = 72 then some localCycle00072 else none) else (if id = 73 then some localCycle00073 else none)) else (if id < 75 then (if id = 74 then some localCycle00074 else none) else (if id = 75 then some localCycle00075 else none))) else (if id < 78 then (if id < 77 then (if id = 76 then some localCycle00076 else none) else (if id = 77 then some localCycle00077 else none)) else (if id < 79 then (if id = 78 then some localCycle00078 else none) else (if id = 79 then some localCycle00079 else none))))) else (if id < 88 then (if id < 84 then (if id < 82 then (if id < 81 then (if id = 80 then some localCycle00080 else none) else (if id = 81 then some localCycle00081 else none)) else (if id < 83 then (if id = 82 then some localCycle00082 else none) else (if id = 83 then some localCycle00083 else none))) else (if id < 86 then (if id < 85 then (if id = 84 then some localCycle00084 else none) else (if id = 85 then some localCycle00085 else none)) else (if id < 87 then (if id = 86 then some localCycle00086 else none) else (if id = 87 then some localCycle00087 else none)))) else (if id < 92 then (if id < 90 then (if id < 89 then (if id = 88 then some localCycle00088 else none) else (if id = 89 then some localCycle00089 else none)) else (if id < 91 then (if id = 90 then some localCycle00090 else none) else (if id = 91 then some localCycle00091 else none))) else (if id < 94 then (if id < 93 then (if id = 92 then some localCycle00092 else none) else (if id = 93 then some localCycle00093 else none)) else (if id < 95 then (if id = 94 then some localCycle00094 else none) else (if id = 95 then some localCycle00095 else none)))))) else (if id < 112 then (if id < 104 then (if id < 100 then (if id < 98 then (if id < 97 then (if id = 96 then some localCycle00096 else none) else (if id = 97 then some localCycle00097 else none)) else (if id < 99 then (if id = 98 then some localCycle00098 else none) else (if id = 99 then some localCycle00099 else none))) else (if id < 102 then (if id < 101 then (if id = 100 then some localCycle00100 else none) else (if id = 101 then some localCycle00101 else none)) else (if id < 103 then (if id = 102 then some localCycle00102 else none) else (if id = 103 then some localCycle00103 else none)))) else (if id < 108 then (if id < 106 then (if id < 105 then (if id = 104 then some localCycle00104 else none) else (if id = 105 then some localCycle00105 else none)) else (if id < 107 then (if id = 106 then some localCycle00106 else none) else (if id = 107 then some localCycle00107 else none))) else (if id < 110 then (if id < 109 then (if id = 108 then some localCycle00108 else none) else (if id = 109 then some localCycle00109 else none)) else (if id < 111 then (if id = 110 then some localCycle00110 else none) else (if id = 111 then some localCycle00111 else none))))) else (if id < 120 then (if id < 116 then (if id < 114 then (if id < 113 then (if id = 112 then some localCycle00112 else none) else (if id = 113 then some localCycle00113 else none)) else (if id < 115 then (if id = 114 then some localCycle00114 else none) else (if id = 115 then some localCycle00115 else none))) else (if id < 118 then (if id < 117 then (if id = 116 then some localCycle00116 else none) else (if id = 117 then some localCycle00117 else none)) else (if id < 119 then (if id = 118 then some localCycle00118 else none) else (if id = 119 then some localCycle00119 else none)))) else (if id < 124 then (if id < 122 then (if id < 121 then (if id = 120 then some localCycle00120 else none) else (if id = 121 then some localCycle00121 else none)) else (if id < 123 then (if id = 122 then some localCycle00122 else none) else (if id = 123 then some localCycle00123 else none))) else (if id < 126 then (if id < 125 then (if id = 124 then some localCycle00124 else none) else (if id = 125 then some localCycle00125 else none)) else (if id < 127 then (if id = 126 then some localCycle00126 else none) else (if id < 128 then (if id = 127 then some localCycle00127 else none) else (if id = 128 then some localCycle00128 else none))))))))) else (if id < 193 then (if id < 161 then (if id < 145 then (if id < 137 then (if id < 133 then (if id < 131 then (if id < 130 then (if id = 129 then some localCycle00129 else none) else (if id = 130 then some localCycle00130 else none)) else (if id < 132 then (if id = 131 then some localCycle00131 else none) else (if id = 132 then some localCycle00132 else none))) else (if id < 135 then (if id < 134 then (if id = 133 then some localCycle00133 else none) else (if id = 134 then some localCycle00134 else none)) else (if id < 136 then (if id = 135 then some localCycle00135 else none) else (if id = 136 then some localCycle00136 else none)))) else (if id < 141 then (if id < 139 then (if id < 138 then (if id = 137 then some localCycle00137 else none) else (if id = 138 then some localCycle00138 else none)) else (if id < 140 then (if id = 139 then some localCycle00139 else none) else (if id = 140 then some localCycle00140 else none))) else (if id < 143 then (if id < 142 then (if id = 141 then some localCycle00141 else none) else (if id = 142 then some localCycle00142 else none)) else (if id < 144 then (if id = 143 then some localCycle00143 else none) else (if id = 144 then some localCycle00144 else none))))) else (if id < 153 then (if id < 149 then (if id < 147 then (if id < 146 then (if id = 145 then some localCycle00145 else none) else (if id = 146 then some localCycle00146 else none)) else (if id < 148 then (if id = 147 then some localCycle00147 else none) else (if id = 148 then some localCycle00148 else none))) else (if id < 151 then (if id < 150 then (if id = 149 then some localCycle00149 else none) else (if id = 150 then some localCycle00150 else none)) else (if id < 152 then (if id = 151 then some localCycle00151 else none) else (if id = 152 then some localCycle00152 else none)))) else (if id < 157 then (if id < 155 then (if id < 154 then (if id = 153 then some localCycle00153 else none) else (if id = 154 then some localCycle00154 else none)) else (if id < 156 then (if id = 155 then some localCycle00155 else none) else (if id = 156 then some localCycle00156 else none))) else (if id < 159 then (if id < 158 then (if id = 157 then some localCycle00157 else none) else (if id = 158 then some localCycle00158 else none)) else (if id < 160 then (if id = 159 then some localCycle00159 else none) else (if id = 160 then some localCycle00160 else none)))))) else (if id < 177 then (if id < 169 then (if id < 165 then (if id < 163 then (if id < 162 then (if id = 161 then some localCycle00161 else none) else (if id = 162 then some localCycle00162 else none)) else (if id < 164 then (if id = 163 then some localCycle00163 else none) else (if id = 164 then some localCycle00164 else none))) else (if id < 167 then (if id < 166 then (if id = 165 then some localCycle00165 else none) else (if id = 166 then some localCycle00166 else none)) else (if id < 168 then (if id = 167 then some localCycle00167 else none) else (if id = 168 then some localCycle00168 else none)))) else (if id < 173 then (if id < 171 then (if id < 170 then (if id = 169 then some localCycle00169 else none) else (if id = 170 then some localCycle00170 else none)) else (if id < 172 then (if id = 171 then some localCycle00171 else none) else (if id = 172 then some localCycle00172 else none))) else (if id < 175 then (if id < 174 then (if id = 173 then some localCycle00173 else none) else (if id = 174 then some localCycle00174 else none)) else (if id < 176 then (if id = 175 then some localCycle00175 else none) else (if id = 176 then some localCycle00176 else none))))) else (if id < 185 then (if id < 181 then (if id < 179 then (if id < 178 then (if id = 177 then some localCycle00177 else none) else (if id = 178 then some localCycle00178 else none)) else (if id < 180 then (if id = 179 then some localCycle00179 else none) else (if id = 180 then some localCycle00180 else none))) else (if id < 183 then (if id < 182 then (if id = 181 then some localCycle00181 else none) else (if id = 182 then some localCycle00182 else none)) else (if id < 184 then (if id = 183 then some localCycle00183 else none) else (if id = 184 then some localCycle00184 else none)))) else (if id < 189 then (if id < 187 then (if id < 186 then (if id = 185 then some localCycle00185 else none) else (if id = 186 then some localCycle00186 else none)) else (if id < 188 then (if id = 187 then some localCycle00187 else none) else (if id = 188 then some localCycle00188 else none))) else (if id < 191 then (if id < 190 then (if id = 189 then some localCycle00189 else none) else (if id = 190 then some localCycle00190 else none)) else (if id < 192 then (if id = 191 then some localCycle00191 else none) else (if id = 192 then some localCycle00192 else none))))))) else (if id < 225 then (if id < 209 then (if id < 201 then (if id < 197 then (if id < 195 then (if id < 194 then (if id = 193 then some localCycle00193 else none) else (if id = 194 then some localCycle00194 else none)) else (if id < 196 then (if id = 195 then some localCycle00195 else none) else (if id = 196 then some localCycle00196 else none))) else (if id < 199 then (if id < 198 then (if id = 197 then some localCycle00197 else none) else (if id = 198 then some localCycle00198 else none)) else (if id < 200 then (if id = 199 then some localCycle00199 else none) else (if id = 200 then some localCycle00200 else none)))) else (if id < 205 then (if id < 203 then (if id < 202 then (if id = 201 then some localCycle00201 else none) else (if id = 202 then some localCycle00202 else none)) else (if id < 204 then (if id = 203 then some localCycle00203 else none) else (if id = 204 then some localCycle00204 else none))) else (if id < 207 then (if id < 206 then (if id = 205 then some localCycle00205 else none) else (if id = 206 then some localCycle00206 else none)) else (if id < 208 then (if id = 207 then some localCycle00207 else none) else (if id = 208 then some localCycle00208 else none))))) else (if id < 217 then (if id < 213 then (if id < 211 then (if id < 210 then (if id = 209 then some localCycle00209 else none) else (if id = 210 then some localCycle00210 else none)) else (if id < 212 then (if id = 211 then some localCycle00211 else none) else (if id = 212 then some localCycle00212 else none))) else (if id < 215 then (if id < 214 then (if id = 213 then some localCycle00213 else none) else (if id = 214 then some localCycle00214 else none)) else (if id < 216 then (if id = 215 then some localCycle00215 else none) else (if id = 216 then some localCycle00216 else none)))) else (if id < 221 then (if id < 219 then (if id < 218 then (if id = 217 then some localCycle00217 else none) else (if id = 218 then some localCycle00218 else none)) else (if id < 220 then (if id = 219 then some localCycle00219 else none) else (if id = 220 then some localCycle00220 else none))) else (if id < 223 then (if id < 222 then (if id = 221 then some localCycle00221 else none) else (if id = 222 then some localCycle00222 else none)) else (if id < 224 then (if id = 223 then some localCycle00223 else none) else (if id = 224 then some localCycle00224 else none)))))) else (if id < 241 then (if id < 233 then (if id < 229 then (if id < 227 then (if id < 226 then (if id = 225 then some localCycle00225 else none) else (if id = 226 then some localCycle00226 else none)) else (if id < 228 then (if id = 227 then some localCycle00227 else none) else (if id = 228 then some localCycle00228 else none))) else (if id < 231 then (if id < 230 then (if id = 229 then some localCycle00229 else none) else (if id = 230 then some localCycle00230 else none)) else (if id < 232 then (if id = 231 then some localCycle00231 else none) else (if id = 232 then some localCycle00232 else none)))) else (if id < 237 then (if id < 235 then (if id < 234 then (if id = 233 then some localCycle00233 else none) else (if id = 234 then some localCycle00234 else none)) else (if id < 236 then (if id = 235 then some localCycle00235 else none) else (if id = 236 then some localCycle00236 else none))) else (if id < 239 then (if id < 238 then (if id = 237 then some localCycle00237 else none) else (if id = 238 then some localCycle00238 else none)) else (if id < 240 then (if id = 239 then some localCycle00239 else none) else (if id = 240 then some localCycle00240 else none))))) else (if id < 249 then (if id < 245 then (if id < 243 then (if id < 242 then (if id = 241 then some localCycle00241 else none) else (if id = 242 then some localCycle00242 else none)) else (if id < 244 then (if id = 243 then some localCycle00243 else none) else (if id = 244 then some localCycle00244 else none))) else (if id < 247 then (if id < 246 then (if id = 245 then some localCycle00245 else none) else (if id = 246 then some localCycle00246 else none)) else (if id < 248 then (if id = 247 then some localCycle00247 else none) else (if id = 248 then some localCycle00248 else none)))) else (if id < 253 then (if id < 251 then (if id < 250 then (if id = 249 then some localCycle00249 else none) else (if id = 250 then some localCycle00250 else none)) else (if id < 252 then (if id = 251 then some localCycle00251 else none) else (if id = 252 then some localCycle00252 else none))) else (if id < 255 then (if id < 254 then (if id = 253 then some localCycle00253 else none) else (if id = 254 then some localCycle00254 else none)) else (if id < 256 then (if id = 255 then some localCycle00255 else none) else (if id < 257 then (if id = 256 then some localCycle00256 else none) else (if id = 257 then some localCycle00257 else none)))))))))

def namedLeaf000 : LeafData := { rows := ![![1, 4, 2, 3, 5, 6], ![0, 6, 5, 4, 2, 3], ![4, 0, 6, 5, 1, 3], ![4, 0, 5, 6, 1, 2], ![3, 2, 0, 6, 5, 1], ![0, 3, 6, 2, 4, 1], ![0, 3, 5, 2, 4, 1]], proof := .tail 23 }

theorem namedLeaf000_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3840)) namedLeaf000 = true :=
  by decide +kernel

def namedLeaf001 : LeafData := { rows := ![![1, 4, 2, 3, 5, 6], ![0, 6, 5, 4, 2, 3], ![4, 0, 6, 5, 1, 3], ![4, 0, 6, 5, 1, 2], ![3, 2, 0, 6, 5, 1], ![0, 6, 3, 2, 4, 1], ![0, 5, 3, 2, 4, 1]], proof := .tail 139 }

theorem namedLeaf001_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3841)) namedLeaf001 = true :=
  by decide +kernel

def namedLeaf002 : LeafData := { rows := ![![1, 4, 2, 3, 6, 5], ![0, 6, 5, 4, 2, 3], ![4, 0, 6, 5, 1, 3], ![4, 0, 6, 5, 1, 2], ![3, 2, 0, 6, 5, 1], ![6, 0, 3, 2, 4, 1], ![5, 0, 3, 2, 4, 1]], proof := .tail 163 }

theorem namedLeaf002_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3842)) namedLeaf002 = true :=
  by decide +kernel

def namedLeaf003 : LeafData := { rows := ![![1, 4, 2, 6, 3, 5], ![0, 6, 5, 4, 2, 3], ![4, 0, 6, 5, 1, 3], ![4, 6, 0, 5, 1, 2], ![3, 2, 0, 6, 5, 1], ![6, 0, 3, 2, 4, 1], ![5, 3, 0, 2, 4, 1]], proof := .tail 245 }

theorem namedLeaf003_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3843)) namedLeaf003 = true :=
  by decide +kernel

def namedLeaf004 : LeafData := { rows := ![![1, 4, 6, 2, 3, 5], ![0, 6, 5, 4, 2, 3], ![4, 6, 0, 5, 1, 3], ![4, 6, 0, 5, 1, 2], ![3, 2, 0, 6, 5, 1], ![6, 0, 3, 2, 4, 1], ![5, 3, 2, 0, 4, 1]], proof := .tail 138 }

theorem namedLeaf004_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3844)) namedLeaf004 = true :=
  by decide +kernel

def namedLeaf005 : LeafData := { rows := ![![1, 6, 4, 2, 3, 5], ![0, 6, 5, 4, 2, 3], ![4, 6, 0, 5, 1, 3], ![4, 6, 0, 5, 1, 2], ![3, 2, 6, 0, 5, 1], ![6, 0, 3, 2, 4, 1], ![5, 3, 2, 4, 0, 1]], proof := .tail 36 }

theorem namedLeaf005_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3845)) namedLeaf005 = true :=
  by decide +kernel

def namedLeaf006 : LeafData := { rows := ![![1, 6, 4, 2, 3, 5], ![0, 6, 5, 4, 2, 3], ![6, 4, 0, 5, 1, 3], ![4, 6, 0, 5, 1, 2], ![3, 6, 2, 0, 5, 1], ![6, 0, 3, 2, 4, 1], ![5, 3, 4, 2, 0, 1]], proof := .tail 121 }

theorem namedLeaf006_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3846)) namedLeaf006 = true :=
  by decide +kernel

def namedLeaf007 : LeafData := { rows := ![![1, 6, 4, 2, 3, 5], ![0, 6, 5, 4, 2, 3], ![6, 4, 0, 5, 1, 3], ![6, 4, 0, 5, 1, 2], ![6, 3, 2, 0, 5, 1], ![6, 0, 3, 2, 4, 1], ![5, 4, 3, 2, 0, 1]], proof := .tail 243 }

theorem namedLeaf007_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3847)) namedLeaf007 = true :=
  by decide +kernel

def namedLeaf008 : LeafData := { rows := ![![1, 4, 2, 5, 3, 6], ![0, 4, 2, 5, 3, 6], ![4, 0, 1, 5, 3, 6], ![4, 5, 0, 1, 2, 6], ![3, 2, 0, 1, 5, 6], ![3, 0, 1, 2, 4, 6], ![0, 1, 2, 3, 4, 5]], proof := .low0 (![145, 190, 244, 55, 90, 32, 117, 116, 50, 67, 3, 222, 222, 238, 116, 116, 116, 116, 105, 142, 201, 25, 28, 160, 198, 192, 234, 179]) }

theorem namedLeaf008_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3848)) namedLeaf008 = true :=
  by decide +kernel

def namedLeaf009 : LeafData := { rows := ![![1, 4, 2, 5, 3, 6], ![0, 4, 2, 5, 3, 6], ![4, 0, 1, 5, 3, 6], ![4, 5, 0, 1, 2, 6], ![3, 2, 0, 1, 6, 5], ![3, 0, 1, 2, 6, 4], ![0, 1, 2, 3, 5, 4]], proof := .tail 56 }

theorem namedLeaf009_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3849)) namedLeaf009 = true :=
  by decide +kernel

def namedLeaf010 : LeafData := { rows := ![![1, 4, 2, 5, 3, 6], ![0, 4, 2, 5, 3, 6], ![4, 0, 1, 5, 6, 3], ![4, 5, 0, 1, 6, 2], ![3, 2, 0, 1, 5, 6], ![3, 0, 1, 2, 4, 6], ![0, 1, 3, 2, 4, 5]], proof := .tail 167 }

theorem namedLeaf010_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3850)) namedLeaf010 = true :=
  by decide +kernel

def namedLeaf011 : LeafData := { rows := ![![1, 4, 2, 5, 3, 6], ![0, 4, 2, 5, 3, 6], ![4, 0, 1, 5, 6, 3], ![4, 5, 0, 1, 6, 2], ![3, 2, 0, 1, 6, 5], ![3, 0, 1, 2, 6, 4], ![0, 1, 3, 2, 5, 4]], proof := .tail 157 }

theorem namedLeaf011_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3851)) namedLeaf011 = true :=
  by decide +kernel

def namedLeaf012 : LeafData := { rows := ![![1, 4, 2, 5, 3, 6], ![0, 4, 2, 5, 3, 6], ![4, 0, 1, 6, 5, 3], ![4, 5, 0, 1, 6, 2], ![3, 2, 0, 1, 6, 5], ![3, 0, 1, 6, 2, 4], ![0, 1, 3, 5, 2, 4]], proof := .tail 64 }

theorem namedLeaf012_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3852)) namedLeaf012 = true :=
  by decide +kernel

def namedLeaf013 : LeafData := { rows := ![![1, 4, 2, 5, 3, 6], ![0, 4, 2, 5, 6, 3], ![4, 0, 1, 5, 6, 3], ![4, 5, 0, 6, 1, 2], ![3, 2, 0, 1, 5, 6], ![3, 0, 1, 2, 4, 6], ![0, 3, 1, 2, 4, 5]], proof := .tail 74 }

theorem namedLeaf013_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3853)) namedLeaf013 = true :=
  by decide +kernel

def namedLeaf014 : LeafData := { rows := ![![1, 4, 2, 5, 3, 6], ![0, 4, 2, 5, 6, 3], ![4, 0, 1, 5, 6, 3], ![4, 5, 0, 6, 1, 2], ![3, 2, 0, 1, 6, 5], ![3, 0, 1, 2, 6, 4], ![0, 3, 1, 2, 5, 4]], proof := .tail 157 }

theorem namedLeaf014_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3854)) namedLeaf014 = true :=
  by decide +kernel

def namedLeaf015 : LeafData := { rows := ![![1, 4, 2, 5, 3, 6], ![0, 4, 2, 5, 6, 3], ![4, 0, 1, 6, 5, 3], ![4, 5, 0, 6, 1, 2], ![3, 2, 0, 1, 6, 5], ![3, 0, 1, 6, 2, 4], ![0, 3, 1, 5, 2, 4]], proof := .tail 72 }

theorem namedLeaf015_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3855)) namedLeaf015 = true :=
  by decide +kernel

def namedLeaf016 : LeafData := { rows := ![![1, 4, 2, 5, 3, 6], ![0, 4, 2, 6, 5, 3], ![4, 0, 1, 6, 5, 3], ![4, 5, 0, 6, 1, 2], ![3, 2, 0, 1, 6, 5], ![3, 0, 6, 1, 2, 4], ![0, 3, 5, 1, 2, 4]], proof := .tail 30 }

theorem namedLeaf016_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3856)) namedLeaf016 = true :=
  by decide +kernel

def namedLeaf017 : LeafData := { rows := ![![1, 4, 2, 5, 3, 6], ![0, 4, 6, 2, 5, 3], ![4, 0, 6, 1, 5, 3], ![4, 5, 0, 6, 1, 2], ![3, 2, 0, 1, 6, 5], ![3, 0, 6, 1, 2, 4], ![0, 3, 5, 2, 1, 4]], proof := .tail 257 }

theorem namedLeaf017_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3857)) namedLeaf017 = true :=
  by decide +kernel

def namedLeaf018 : LeafData := { rows := ![![1, 4, 2, 5, 3, 6], ![0, 6, 4, 2, 5, 3], ![4, 0, 6, 1, 5, 3], ![4, 5, 0, 6, 1, 2], ![3, 2, 0, 6, 1, 5], ![3, 0, 6, 1, 2, 4], ![0, 3, 5, 2, 4, 1]], proof := .tail 43 }

theorem namedLeaf018_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3858)) namedLeaf018 = true :=
  by decide +kernel

def namedLeaf019 : LeafData := { rows := ![![1, 4, 2, 5, 6, 3], ![0, 4, 2, 5, 6, 3], ![4, 0, 1, 5, 6, 3], ![4, 5, 6, 0, 1, 2], ![3, 2, 0, 1, 5, 6], ![3, 0, 1, 2, 4, 6], ![3, 0, 1, 2, 4, 5]], proof := .low6 (![141, 208, 150, 53, 122, 66, 128, 182, 37, 57, 176, 255, 113, 8, 241, 225, 168, 127, 158, 162, 228, 9, 209, 7, 170, 96, 140, 102]) }

theorem namedLeaf019_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3859)) namedLeaf019 = true :=
  by decide +kernel

def namedLeaf020 : LeafData := { rows := ![![1, 4, 2, 5, 6, 3], ![0, 4, 2, 5, 6, 3], ![4, 0, 1, 5, 6, 3], ![4, 5, 6, 0, 1, 2], ![3, 2, 0, 1, 6, 5], ![3, 0, 1, 2, 6, 4], ![3, 0, 1, 2, 5, 4]], proof := .tail 211 }

theorem namedLeaf020_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3860)) namedLeaf020 = true :=
  by decide +kernel

def namedLeaf021 : LeafData := { rows := ![![1, 4, 2, 5, 6, 3], ![0, 4, 2, 5, 6, 3], ![4, 0, 1, 6, 5, 3], ![4, 5, 6, 0, 1, 2], ![3, 2, 0, 1, 6, 5], ![3, 0, 1, 6, 2, 4], ![3, 0, 1, 5, 2, 4]], proof := .tail 193 }

theorem namedLeaf021_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3861)) namedLeaf021 = true :=
  by decide +kernel

def namedLeaf022 : LeafData := { rows := ![![1, 4, 2, 5, 6, 3], ![0, 4, 2, 6, 5, 3], ![4, 0, 1, 6, 5, 3], ![4, 5, 6, 0, 1, 2], ![3, 2, 0, 1, 6, 5], ![3, 0, 6, 1, 2, 4], ![3, 0, 5, 1, 2, 4]], proof := .tail 161 }

theorem namedLeaf022_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3862)) namedLeaf022 = true :=
  by decide +kernel

def namedLeaf023 : LeafData := { rows := ![![1, 4, 2, 6, 5, 3], ![0, 4, 2, 6, 5, 3], ![4, 0, 1, 6, 5, 3], ![4, 5, 6, 0, 1, 2], ![3, 2, 0, 1, 6, 5], ![3, 6, 0, 1, 2, 4], ![3, 5, 0, 1, 2, 4]], proof := .low0 (![153, 190, 244, 100, 224, 188, 213, 116, 130, 99, 196, 89, 120, 46, 116, 116, 89, 116, 181, 178, 89, 131, 165, 89, 11, 89, 103, 89]) }

theorem namedLeaf023_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3863)) namedLeaf023 = true :=
  by decide +kernel

def namedLeaf024 : LeafData := { rows := ![![1, 4, 2, 6, 5, 3], ![0, 4, 2, 6, 5, 3], ![4, 0, 1, 6, 5, 3], ![4, 6, 5, 0, 1, 2], ![3, 2, 0, 1, 6, 5], ![6, 3, 0, 1, 2, 4], ![5, 3, 0, 1, 2, 4]], proof := .low0 (![153, 190, 244, 100, 119, 101, 10, 116, 130, 99, 76, 133, 149, 46, 116, 116, 116, 116, 181, 178, 77, 131, 165, 242, 11, 232, 52, 33]) }

theorem namedLeaf024_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3864)) namedLeaf024 = true :=
  by decide +kernel

def namedLeaf025 : LeafData := { rows := ![![1, 4, 2, 5, 6, 3], ![0, 4, 6, 2, 5, 3], ![4, 0, 6, 1, 5, 3], ![4, 5, 6, 0, 1, 2], ![3, 2, 0, 1, 6, 5], ![3, 0, 6, 1, 2, 4], ![3, 0, 5, 2, 1, 4]], proof := .tail 240 }

theorem namedLeaf025_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3865)) namedLeaf025 = true :=
  by decide +kernel

def namedLeaf026 : LeafData := { rows := ![![1, 4, 2, 6, 5, 3], ![0, 4, 6, 2, 5, 3], ![4, 0, 6, 1, 5, 3], ![4, 5, 6, 0, 1, 2], ![3, 2, 0, 1, 6, 5], ![3, 6, 0, 1, 2, 4], ![3, 5, 0, 2, 1, 4]], proof := .tail 257 }

theorem namedLeaf026_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3866)) namedLeaf026 = true :=
  by decide +kernel

def namedLeaf027 : LeafData := { rows := ![![1, 4, 2, 6, 5, 3], ![0, 4, 6, 2, 5, 3], ![4, 0, 6, 1, 5, 3], ![4, 6, 5, 0, 1, 2], ![3, 2, 0, 1, 6, 5], ![6, 3, 0, 1, 2, 4], ![5, 3, 0, 2, 1, 4]], proof := .tail 257 }

theorem namedLeaf027_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3867)) namedLeaf027 = true :=
  by decide +kernel

def namedLeaf028 : LeafData := { rows := ![![1, 4, 2, 5, 6, 3], ![0, 6, 4, 2, 5, 3], ![4, 0, 6, 1, 5, 3], ![4, 5, 6, 0, 1, 2], ![3, 2, 0, 6, 1, 5], ![3, 0, 6, 1, 2, 4], ![3, 0, 5, 2, 4, 1]], proof := .tail 60 }

theorem namedLeaf028_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3868)) namedLeaf028 = true :=
  by decide +kernel

def namedLeaf029 : LeafData := { rows := ![![1, 4, 2, 6, 5, 3], ![0, 6, 4, 2, 5, 3], ![4, 0, 6, 1, 5, 3], ![4, 5, 6, 0, 1, 2], ![3, 2, 0, 6, 1, 5], ![3, 6, 0, 1, 2, 4], ![3, 5, 0, 2, 4, 1]], proof := .tail 43 }

theorem namedLeaf029_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3869)) namedLeaf029 = true :=
  by decide +kernel

def namedLeaf030 : LeafData := { rows := ![![1, 4, 2, 6, 5, 3], ![0, 6, 4, 2, 5, 3], ![4, 0, 6, 1, 5, 3], ![4, 6, 5, 0, 1, 2], ![3, 2, 0, 6, 1, 5], ![6, 3, 0, 1, 2, 4], ![5, 3, 0, 2, 4, 1]], proof := .tail 221 }

theorem namedLeaf030_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3870)) namedLeaf030 = true :=
  by decide +kernel

def namedLeaf031 : LeafData := { rows := ![![1, 4, 6, 2, 5, 3], ![0, 4, 6, 2, 5, 3], ![4, 6, 0, 1, 5, 3], ![4, 5, 6, 0, 1, 2], ![3, 2, 0, 1, 6, 5], ![3, 6, 0, 1, 2, 4], ![3, 5, 2, 0, 1, 4]], proof := .tail 171 }

theorem namedLeaf031_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3871)) namedLeaf031 = true :=
  by decide +kernel

def namedLeaf032 : LeafData := { rows := ![![1, 4, 6, 2, 5, 3], ![0, 6, 4, 2, 5, 3], ![4, 6, 0, 1, 5, 3], ![4, 5, 6, 0, 1, 2], ![3, 2, 0, 6, 1, 5], ![3, 6, 0, 1, 2, 4], ![3, 5, 2, 0, 4, 1]], proof := .tail 16 }

theorem namedLeaf032_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3872)) namedLeaf032 = true :=
  by decide +kernel

def namedLeaf033 : LeafData := { rows := ![![1, 6, 4, 2, 5, 3], ![0, 6, 4, 2, 5, 3], ![4, 6, 0, 1, 5, 3], ![4, 5, 6, 0, 1, 2], ![3, 2, 6, 0, 1, 5], ![3, 6, 0, 1, 2, 4], ![3, 5, 2, 4, 0, 1]], proof := .tail 39 }

theorem namedLeaf033_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3873)) namedLeaf033 = true :=
  by decide +kernel

def namedLeaf034 : LeafData := { rows := ![![1, 6, 4, 2, 5, 3], ![0, 6, 4, 2, 5, 3], ![6, 4, 0, 1, 5, 3], ![4, 5, 6, 0, 1, 2], ![3, 6, 2, 0, 1, 5], ![3, 6, 0, 1, 2, 4], ![3, 5, 4, 2, 0, 1]], proof := .tail 125 }

theorem namedLeaf034_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3874)) namedLeaf034 = true :=
  by decide +kernel

def namedLeaf035 : LeafData := { rows := ![![1, 4, 6, 2, 5, 3], ![0, 4, 6, 2, 5, 3], ![4, 6, 0, 1, 5, 3], ![4, 6, 5, 0, 1, 2], ![3, 2, 0, 1, 6, 5], ![6, 3, 0, 1, 2, 4], ![5, 3, 2, 0, 1, 4]], proof := .low6 (![219, 155, 18, 251, 236, 202, 65, 226, 24, 114, 14, 14, 14, 1, 4, 62, 191, 191, 31, 29, 21, 110, 98, 123, 253, 87, 118, 144]) }

theorem namedLeaf035_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3875)) namedLeaf035 = true :=
  by decide +kernel

def namedLeaf036 : LeafData := { rows := ![![1, 4, 6, 2, 5, 3], ![0, 6, 4, 2, 5, 3], ![4, 6, 0, 1, 5, 3], ![4, 6, 5, 0, 1, 2], ![3, 2, 0, 6, 1, 5], ![6, 3, 0, 1, 2, 4], ![5, 3, 2, 0, 4, 1]], proof := .tail 42 }

theorem namedLeaf036_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3876)) namedLeaf036 = true :=
  by decide +kernel

def namedLeaf037 : LeafData := { rows := ![![1, 6, 4, 2, 5, 3], ![0, 6, 4, 2, 5, 3], ![4, 6, 0, 1, 5, 3], ![4, 6, 5, 0, 1, 2], ![3, 2, 6, 0, 1, 5], ![6, 3, 0, 1, 2, 4], ![5, 3, 2, 4, 0, 1]], proof := .tail 174 }

theorem namedLeaf037_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3877)) namedLeaf037 = true :=
  by decide +kernel

def namedLeaf038 : LeafData := { rows := ![![1, 6, 4, 2, 5, 3], ![0, 6, 4, 2, 5, 3], ![6, 4, 0, 1, 5, 3], ![4, 6, 5, 0, 1, 2], ![3, 6, 2, 0, 1, 5], ![6, 3, 0, 1, 2, 4], ![5, 3, 4, 2, 0, 1]], proof := .tail 125 }

theorem namedLeaf038_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3878)) namedLeaf038 = true :=
  by decide +kernel

def namedLeaf039 : LeafData := { rows := ![![1, 6, 4, 2, 5, 3], ![0, 6, 4, 2, 5, 3], ![6, 4, 0, 1, 5, 3], ![6, 4, 5, 0, 1, 2], ![6, 3, 2, 0, 1, 5], ![6, 3, 0, 1, 2, 4], ![5, 4, 3, 2, 0, 1]], proof := .tail 92 }

theorem namedLeaf039_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3879)) namedLeaf039 = true :=
  by decide +kernel

def namedLeaf040 : LeafData := { rows := ![![1, 4, 2, 5, 3, 6], ![0, 4, 5, 2, 3, 6], ![4, 0, 5, 1, 3, 6], ![4, 5, 0, 1, 2, 6], ![3, 2, 0, 1, 5, 6], ![3, 0, 2, 1, 4, 6], ![0, 1, 2, 3, 4, 5]], proof := .tail 22 }

theorem namedLeaf040_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3880)) namedLeaf040 = true :=
  by decide +kernel

def namedLeaf041 : LeafData := { rows := ![![1, 4, 2, 5, 3, 6], ![0, 4, 5, 2, 3, 6], ![4, 0, 5, 1, 3, 6], ![4, 5, 0, 1, 2, 6], ![3, 2, 0, 1, 6, 5], ![3, 0, 2, 1, 6, 4], ![0, 1, 2, 3, 5, 4]], proof := .tail 229 }

theorem namedLeaf041_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3881)) namedLeaf041 = true :=
  by decide +kernel

def namedLeaf042 : LeafData := { rows := ![![1, 4, 2, 5, 3, 6], ![0, 4, 5, 2, 3, 6], ![4, 0, 5, 1, 6, 3], ![4, 5, 0, 1, 6, 2], ![3, 2, 0, 1, 5, 6], ![3, 0, 2, 1, 4, 6], ![0, 1, 3, 2, 4, 5]], proof := .tail 151 }

theorem namedLeaf042_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3882)) namedLeaf042 = true :=
  by decide +kernel

def namedLeaf043 : LeafData := { rows := ![![1, 4, 2, 5, 3, 6], ![0, 4, 5, 2, 3, 6], ![4, 0, 5, 1, 6, 3], ![4, 5, 0, 1, 6, 2], ![3, 2, 0, 1, 6, 5], ![3, 0, 2, 1, 6, 4], ![0, 1, 3, 2, 5, 4]], proof := .tail 151 }

theorem namedLeaf043_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3883)) namedLeaf043 = true :=
  by decide +kernel

def namedLeaf044 : LeafData := { rows := ![![1, 4, 2, 5, 3, 6], ![0, 4, 5, 2, 6, 3], ![4, 0, 5, 1, 6, 3], ![4, 5, 0, 6, 1, 2], ![3, 2, 0, 1, 5, 6], ![3, 0, 2, 1, 4, 6], ![0, 3, 1, 2, 4, 5]], proof := .tail 215 }

theorem namedLeaf044_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3884)) namedLeaf044 = true :=
  by decide +kernel

def namedLeaf045 : LeafData := { rows := ![![1, 4, 2, 5, 3, 6], ![0, 4, 5, 2, 6, 3], ![4, 0, 5, 1, 6, 3], ![4, 5, 0, 6, 1, 2], ![3, 2, 0, 1, 6, 5], ![3, 0, 2, 1, 6, 4], ![0, 3, 1, 2, 5, 4]], proof := .tail 215 }

theorem namedLeaf045_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3885)) namedLeaf045 = true :=
  by decide +kernel

def namedLeaf046 : LeafData := { rows := ![![1, 4, 2, 5, 3, 6], ![0, 4, 5, 6, 2, 3], ![4, 0, 5, 6, 1, 3], ![4, 5, 0, 6, 1, 2], ![3, 2, 0, 1, 5, 6], ![3, 0, 2, 1, 4, 6], ![0, 3, 2, 1, 4, 5]], proof := .tail 80 }

theorem namedLeaf046_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3886)) namedLeaf046 = true :=
  by decide +kernel

def namedLeaf047 : LeafData := { rows := ![![1, 4, 2, 5, 3, 6], ![0, 4, 5, 6, 2, 3], ![4, 0, 5, 6, 1, 3], ![4, 5, 0, 6, 1, 2], ![3, 2, 0, 1, 6, 5], ![3, 0, 2, 1, 6, 4], ![0, 3, 2, 1, 5, 4]], proof := .tail 80 }

theorem namedLeaf047_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3887)) namedLeaf047 = true :=
  by decide +kernel

def namedLeaf048 : LeafData := { rows := ![![1, 4, 2, 5, 3, 6], ![0, 4, 6, 5, 2, 3], ![4, 0, 5, 6, 1, 3], ![4, 5, 0, 6, 1, 2], ![3, 2, 0, 1, 6, 5], ![3, 0, 2, 6, 1, 4], ![0, 3, 2, 5, 1, 4]], proof := .tail 200 }

theorem namedLeaf048_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3888)) namedLeaf048 = true :=
  by decide +kernel

def namedLeaf049 : LeafData := { rows := ![![1, 4, 2, 5, 3, 6], ![0, 4, 6, 5, 2, 3], ![4, 0, 6, 5, 1, 3], ![4, 5, 0, 6, 1, 2], ![3, 2, 0, 1, 6, 5], ![3, 0, 6, 2, 1, 4], ![0, 3, 5, 2, 1, 4]], proof := .tail 212 }

theorem namedLeaf049_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3889)) namedLeaf049 = true :=
  by decide +kernel

def namedLeaf050 : LeafData := { rows := ![![1, 4, 2, 5, 3, 6], ![0, 6, 4, 5, 2, 3], ![4, 0, 5, 6, 1, 3], ![4, 5, 0, 6, 1, 2], ![3, 2, 0, 6, 1, 5], ![3, 0, 2, 6, 1, 4], ![0, 3, 2, 5, 4, 1]], proof := .tail 203 }

theorem namedLeaf050_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3890)) namedLeaf050 = true :=
  by decide +kernel

def namedLeaf051 : LeafData := { rows := ![![1, 4, 2, 5, 3, 6], ![0, 6, 4, 5, 2, 3], ![4, 0, 6, 5, 1, 3], ![4, 5, 0, 6, 1, 2], ![3, 2, 0, 6, 1, 5], ![3, 0, 6, 2, 1, 4], ![0, 3, 5, 2, 4, 1]], proof := .tail 212 }

theorem namedLeaf051_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3891)) namedLeaf051 = true :=
  by decide +kernel

def namedLeaf052 : LeafData := { rows := ![![1, 4, 2, 5, 6, 3], ![0, 4, 5, 2, 6, 3], ![4, 0, 5, 1, 6, 3], ![4, 5, 6, 0, 1, 2], ![3, 2, 0, 1, 5, 6], ![3, 0, 2, 1, 4, 6], ![3, 0, 1, 2, 4, 5]], proof := .tail 215 }

theorem namedLeaf052_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3892)) namedLeaf052 = true :=
  by decide +kernel

def namedLeaf053 : LeafData := { rows := ![![1, 4, 2, 5, 6, 3], ![0, 4, 5, 2, 6, 3], ![4, 0, 5, 1, 6, 3], ![4, 5, 6, 0, 1, 2], ![3, 2, 0, 1, 6, 5], ![3, 0, 2, 1, 6, 4], ![3, 0, 1, 2, 5, 4]], proof := .tail 215 }

theorem namedLeaf053_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3893)) namedLeaf053 = true :=
  by decide +kernel

def namedLeaf054 : LeafData := { rows := ![![1, 4, 2, 5, 6, 3], ![0, 4, 5, 6, 2, 3], ![4, 0, 5, 6, 1, 3], ![4, 5, 6, 0, 1, 2], ![3, 2, 0, 1, 5, 6], ![3, 0, 2, 1, 4, 6], ![3, 0, 2, 1, 4, 5]], proof := .tail 80 }

theorem namedLeaf054_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3894)) namedLeaf054 = true :=
  by decide +kernel

def namedLeaf055 : LeafData := { rows := ![![1, 4, 2, 5, 6, 3], ![0, 4, 5, 6, 2, 3], ![4, 0, 5, 6, 1, 3], ![4, 5, 6, 0, 1, 2], ![3, 2, 0, 1, 6, 5], ![3, 0, 2, 1, 6, 4], ![3, 0, 2, 1, 5, 4]], proof := .tail 80 }

theorem namedLeaf055_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3895)) namedLeaf055 = true :=
  by decide +kernel

def namedLeaf056 : LeafData := { rows := ![![1, 4, 2, 5, 6, 3], ![0, 4, 6, 5, 2, 3], ![4, 0, 5, 6, 1, 3], ![4, 5, 6, 0, 1, 2], ![3, 2, 0, 1, 6, 5], ![3, 0, 2, 6, 1, 4], ![3, 0, 2, 5, 1, 4]], proof := .tail 200 }

theorem namedLeaf056_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3896)) namedLeaf056 = true :=
  by decide +kernel

def namedLeaf057 : LeafData := { rows := ![![1, 4, 2, 5, 6, 3], ![0, 4, 6, 5, 2, 3], ![4, 0, 6, 5, 1, 3], ![4, 5, 6, 0, 1, 2], ![3, 2, 0, 1, 6, 5], ![3, 0, 6, 2, 1, 4], ![3, 0, 5, 2, 1, 4]], proof := .tail 212 }

theorem namedLeaf057_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3897)) namedLeaf057 = true :=
  by decide +kernel

def namedLeaf058 : LeafData := { rows := ![![1, 4, 2, 6, 5, 3], ![0, 4, 6, 5, 2, 3], ![4, 0, 6, 5, 1, 3], ![4, 5, 6, 0, 1, 2], ![3, 2, 0, 1, 6, 5], ![3, 6, 0, 2, 1, 4], ![3, 5, 0, 2, 1, 4]], proof := .tail 212 }

theorem namedLeaf058_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3898)) namedLeaf058 = true :=
  by decide +kernel

def namedLeaf059 : LeafData := { rows := ![![1, 4, 2, 6, 5, 3], ![0, 4, 6, 5, 2, 3], ![4, 0, 6, 5, 1, 3], ![4, 6, 5, 0, 1, 2], ![3, 2, 0, 1, 6, 5], ![6, 3, 0, 2, 1, 4], ![5, 3, 0, 2, 1, 4]], proof := .tail 159 }

theorem namedLeaf059_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3899)) namedLeaf059 = true :=
  by decide +kernel

def namedLeaf060 : LeafData := { rows := ![![1, 4, 2, 5, 6, 3], ![0, 6, 4, 5, 2, 3], ![4, 0, 5, 6, 1, 3], ![4, 5, 6, 0, 1, 2], ![3, 2, 0, 6, 1, 5], ![3, 0, 2, 6, 1, 4], ![3, 0, 2, 5, 4, 1]], proof := .tail 203 }

theorem namedLeaf060_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3900)) namedLeaf060 = true :=
  by decide +kernel

def namedLeaf061 : LeafData := { rows := ![![1, 4, 2, 5, 6, 3], ![0, 6, 4, 5, 2, 3], ![4, 0, 6, 5, 1, 3], ![4, 5, 6, 0, 1, 2], ![3, 2, 0, 6, 1, 5], ![3, 0, 6, 2, 1, 4], ![3, 0, 5, 2, 4, 1]], proof := .tail 212 }

theorem namedLeaf061_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3901)) namedLeaf061 = true :=
  by decide +kernel

def namedLeaf062 : LeafData := { rows := ![![1, 4, 2, 6, 5, 3], ![0, 6, 4, 5, 2, 3], ![4, 0, 6, 5, 1, 3], ![4, 5, 6, 0, 1, 2], ![3, 2, 0, 6, 1, 5], ![3, 6, 0, 2, 1, 4], ![3, 5, 0, 2, 4, 1]], proof := .tail 212 }

theorem namedLeaf062_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3902)) namedLeaf062 = true :=
  by decide +kernel

def namedLeaf063 : LeafData := { rows := ![![1, 4, 2, 6, 5, 3], ![0, 6, 4, 5, 2, 3], ![4, 0, 6, 5, 1, 3], ![4, 6, 5, 0, 1, 2], ![3, 2, 0, 6, 1, 5], ![6, 3, 0, 2, 1, 4], ![5, 3, 0, 2, 4, 1]], proof := .tail 107 }

theorem namedLeaf063_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3903)) namedLeaf063 = true :=
  by decide +kernel

def namedLeaf064 : LeafData := { rows := ![![1, 4, 6, 2, 5, 3], ![0, 4, 6, 5, 2, 3], ![4, 6, 0, 5, 1, 3], ![4, 5, 6, 0, 1, 2], ![3, 2, 0, 1, 6, 5], ![3, 6, 0, 2, 1, 4], ![3, 5, 2, 0, 1, 4]], proof := .tail 59 }

theorem namedLeaf064_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3904)) namedLeaf064 = true :=
  by decide +kernel

def namedLeaf065 : LeafData := { rows := ![![1, 4, 6, 2, 5, 3], ![0, 6, 4, 5, 2, 3], ![4, 6, 0, 5, 1, 3], ![4, 5, 6, 0, 1, 2], ![3, 2, 0, 6, 1, 5], ![3, 6, 0, 2, 1, 4], ![3, 5, 2, 0, 4, 1]], proof := .tail 59 }

theorem namedLeaf065_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3905)) namedLeaf065 = true :=
  by decide +kernel

def namedLeaf066 : LeafData := { rows := ![![1, 6, 4, 2, 5, 3], ![0, 6, 4, 5, 2, 3], ![4, 6, 0, 5, 1, 3], ![4, 5, 6, 0, 1, 2], ![3, 2, 6, 0, 1, 5], ![3, 6, 0, 2, 1, 4], ![3, 5, 2, 4, 0, 1]], proof := .tail 59 }

theorem namedLeaf066_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3906)) namedLeaf066 = true :=
  by decide +kernel

def namedLeaf067 : LeafData := { rows := ![![1, 6, 4, 2, 5, 3], ![0, 6, 4, 5, 2, 3], ![6, 4, 0, 5, 1, 3], ![4, 5, 6, 0, 1, 2], ![3, 6, 2, 0, 1, 5], ![3, 6, 0, 2, 1, 4], ![3, 5, 4, 2, 0, 1]], proof := .tail 187 }

theorem namedLeaf067_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3907)) namedLeaf067 = true :=
  by decide +kernel

def namedLeaf068 : LeafData := { rows := ![![1, 4, 6, 2, 5, 3], ![0, 4, 6, 5, 2, 3], ![4, 6, 0, 5, 1, 3], ![4, 6, 5, 0, 1, 2], ![3, 2, 0, 1, 6, 5], ![6, 3, 0, 2, 1, 4], ![5, 3, 2, 0, 1, 4]], proof := .tail 214 }

theorem namedLeaf068_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3908)) namedLeaf068 = true :=
  by decide +kernel

def namedLeaf069 : LeafData := { rows := ![![1, 4, 6, 2, 5, 3], ![0, 6, 4, 5, 2, 3], ![4, 6, 0, 5, 1, 3], ![4, 6, 5, 0, 1, 2], ![3, 2, 0, 6, 1, 5], ![6, 3, 0, 2, 1, 4], ![5, 3, 2, 0, 4, 1]], proof := .tail 214 }

theorem namedLeaf069_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3909)) namedLeaf069 = true :=
  by decide +kernel

def namedLeaf070 : LeafData := { rows := ![![1, 6, 4, 2, 5, 3], ![0, 6, 4, 5, 2, 3], ![4, 6, 0, 5, 1, 3], ![4, 6, 5, 0, 1, 2], ![3, 2, 6, 0, 1, 5], ![6, 3, 0, 2, 1, 4], ![5, 3, 2, 4, 0, 1]], proof := .tail 58 }

theorem namedLeaf070_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3910)) namedLeaf070 = true :=
  by decide +kernel

def namedLeaf071 : LeafData := { rows := ![![1, 6, 4, 2, 5, 3], ![0, 6, 4, 5, 2, 3], ![6, 4, 0, 5, 1, 3], ![4, 6, 5, 0, 1, 2], ![3, 6, 2, 0, 1, 5], ![6, 3, 0, 2, 1, 4], ![5, 3, 4, 2, 0, 1]], proof := .tail 187 }

theorem namedLeaf071_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3911)) namedLeaf071 = true :=
  by decide +kernel

def namedLeaf072 : LeafData := { rows := ![![1, 6, 4, 2, 5, 3], ![0, 6, 4, 5, 2, 3], ![6, 4, 0, 5, 1, 3], ![6, 4, 5, 0, 1, 2], ![6, 3, 2, 0, 1, 5], ![6, 3, 0, 2, 1, 4], ![5, 4, 3, 2, 0, 1]], proof := .tail 73 }

theorem namedLeaf072_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3912)) namedLeaf072 = true :=
  by decide +kernel

def namedLeaf073 : LeafData := { rows := ![![1, 4, 2, 5, 3, 6], ![0, 5, 4, 2, 3, 6], ![4, 0, 5, 1, 3, 6], ![4, 5, 0, 1, 2, 6], ![3, 2, 0, 5, 1, 6], ![3, 0, 2, 4, 1, 6], ![0, 1, 2, 3, 4, 5]], proof := .tail 12 }

theorem namedLeaf073_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3913)) namedLeaf073 = true :=
  by decide +kernel

def namedLeaf074 : LeafData := { rows := ![![1, 4, 2, 5, 3, 6], ![0, 5, 4, 2, 3, 6], ![4, 0, 5, 1, 6, 3], ![4, 5, 0, 1, 6, 2], ![3, 2, 0, 5, 1, 6], ![3, 0, 2, 4, 1, 6], ![0, 1, 3, 2, 4, 5]], proof := .tail 104 }

theorem namedLeaf074_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3914)) namedLeaf074 = true :=
  by decide +kernel

def namedLeaf075 : LeafData := { rows := ![![1, 4, 2, 5, 3, 6], ![0, 5, 4, 2, 6, 3], ![4, 0, 5, 1, 6, 3], ![4, 5, 0, 6, 1, 2], ![3, 2, 0, 5, 1, 6], ![3, 0, 2, 4, 1, 6], ![0, 3, 1, 2, 4, 5]], proof := .tail 163 }

theorem namedLeaf075_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3915)) namedLeaf075 = true :=
  by decide +kernel

def namedLeaf076 : LeafData := { rows := ![![1, 4, 2, 5, 3, 6], ![0, 5, 4, 6, 2, 3], ![4, 0, 5, 6, 1, 3], ![4, 5, 0, 6, 1, 2], ![3, 2, 0, 5, 1, 6], ![3, 0, 2, 4, 1, 6], ![0, 3, 2, 1, 4, 5]], proof := .tail 143 }

theorem namedLeaf076_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3916)) namedLeaf076 = true :=
  by decide +kernel

def namedLeaf077 : LeafData := { rows := ![![1, 4, 2, 5, 3, 6], ![0, 5, 6, 4, 2, 3], ![4, 0, 5, 6, 1, 3], ![4, 5, 0, 6, 1, 2], ![3, 2, 0, 5, 6, 1], ![3, 0, 2, 4, 1, 6], ![0, 3, 2, 4, 1, 5]], proof := .tail 217 }

theorem namedLeaf077_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3917)) namedLeaf077 = true :=
  by decide +kernel

def namedLeaf078 : LeafData := { rows := ![![1, 4, 2, 5, 3, 6], ![0, 6, 5, 4, 2, 3], ![4, 0, 5, 6, 1, 3], ![4, 5, 0, 6, 1, 2], ![3, 2, 0, 5, 6, 1], ![3, 0, 2, 4, 6, 1], ![0, 3, 2, 4, 5, 1]], proof := .tail 0 }

theorem namedLeaf078_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3918)) namedLeaf078 = true :=
  by decide +kernel

def namedLeaf079 : LeafData := { rows := ![![1, 4, 2, 5, 3, 6], ![0, 6, 5, 4, 2, 3], ![4, 0, 5, 6, 1, 3], ![4, 5, 0, 6, 1, 2], ![3, 2, 0, 6, 5, 1], ![3, 0, 2, 6, 4, 1], ![0, 3, 2, 5, 4, 1]], proof := .tail 164 }

theorem namedLeaf079_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3919)) namedLeaf079 = true :=
  by decide +kernel

def namedLeaf080 : LeafData := { rows := ![![1, 4, 2, 5, 3, 6], ![0, 6, 5, 4, 2, 3], ![4, 0, 6, 5, 1, 3], ![4, 5, 0, 6, 1, 2], ![3, 2, 0, 6, 5, 1], ![3, 0, 6, 2, 4, 1], ![0, 3, 5, 2, 4, 1]], proof := .tail 239 }

theorem namedLeaf080_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3920)) namedLeaf080 = true :=
  by decide +kernel

def namedLeaf081 : LeafData := { rows := ![![1, 4, 2, 5, 6, 3], ![0, 5, 4, 2, 6, 3], ![4, 0, 5, 1, 6, 3], ![4, 5, 6, 0, 1, 2], ![3, 2, 0, 5, 1, 6], ![3, 0, 2, 4, 1, 6], ![3, 0, 1, 2, 4, 5]], proof := .tail 163 }

theorem namedLeaf081_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3921)) namedLeaf081 = true :=
  by decide +kernel

def namedLeaf082 : LeafData := { rows := ![![1, 4, 2, 5, 6, 3], ![0, 5, 4, 6, 2, 3], ![4, 0, 5, 6, 1, 3], ![4, 5, 6, 0, 1, 2], ![3, 2, 0, 5, 1, 6], ![3, 0, 2, 4, 1, 6], ![3, 0, 2, 1, 4, 5]], proof := .tail 143 }

theorem namedLeaf082_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3922)) namedLeaf082 = true :=
  by decide +kernel

def namedLeaf083 : LeafData := { rows := ![![1, 4, 2, 5, 6, 3], ![0, 5, 6, 4, 2, 3], ![4, 0, 5, 6, 1, 3], ![4, 5, 6, 0, 1, 2], ![3, 2, 0, 5, 6, 1], ![3, 0, 2, 4, 1, 6], ![3, 0, 2, 4, 1, 5]], proof := .tail 217 }

theorem namedLeaf083_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3923)) namedLeaf083 = true :=
  by decide +kernel

def namedLeaf084 : LeafData := { rows := ![![1, 4, 2, 5, 6, 3], ![0, 6, 5, 4, 2, 3], ![4, 0, 5, 6, 1, 3], ![4, 5, 6, 0, 1, 2], ![3, 2, 0, 5, 6, 1], ![3, 0, 2, 4, 6, 1], ![3, 0, 2, 4, 5, 1]], proof := .tail 0 }

theorem namedLeaf084_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3924)) namedLeaf084 = true :=
  by decide +kernel

def namedLeaf085 : LeafData := { rows := ![![1, 4, 2, 5, 6, 3], ![0, 6, 5, 4, 2, 3], ![4, 0, 5, 6, 1, 3], ![4, 5, 6, 0, 1, 2], ![3, 2, 0, 6, 5, 1], ![3, 0, 2, 6, 4, 1], ![3, 0, 2, 5, 4, 1]], proof := .tail 164 }

theorem namedLeaf085_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3925)) namedLeaf085 = true :=
  by decide +kernel

def namedLeaf086 : LeafData := { rows := ![![1, 4, 2, 5, 6, 3], ![0, 6, 5, 4, 2, 3], ![4, 0, 6, 5, 1, 3], ![4, 5, 6, 0, 1, 2], ![3, 2, 0, 6, 5, 1], ![3, 0, 6, 2, 4, 1], ![3, 0, 5, 2, 4, 1]], proof := .tail 239 }

theorem namedLeaf086_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3926)) namedLeaf086 = true :=
  by decide +kernel

def namedLeaf087 : LeafData := { rows := ![![1, 4, 2, 6, 5, 3], ![0, 6, 5, 4, 2, 3], ![4, 0, 6, 5, 1, 3], ![4, 5, 6, 0, 1, 2], ![3, 2, 0, 6, 5, 1], ![3, 6, 0, 2, 4, 1], ![3, 5, 0, 2, 4, 1]], proof := .tail 239 }

theorem namedLeaf087_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3927)) namedLeaf087 = true :=
  by decide +kernel

def namedLeaf088 : LeafData := { rows := ![![1, 4, 2, 6, 5, 3], ![0, 6, 5, 4, 2, 3], ![4, 0, 6, 5, 1, 3], ![4, 6, 5, 0, 1, 2], ![3, 2, 0, 6, 5, 1], ![6, 3, 0, 2, 4, 1], ![5, 3, 0, 2, 4, 1]], proof := .tail 163 }

theorem namedLeaf088_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3928)) namedLeaf088 = true :=
  by decide +kernel

def namedLeaf089 : LeafData := { rows := ![![1, 4, 6, 2, 5, 3], ![0, 6, 5, 4, 2, 3], ![4, 6, 0, 5, 1, 3], ![4, 5, 6, 0, 1, 2], ![3, 2, 0, 6, 5, 1], ![3, 6, 0, 2, 4, 1], ![3, 5, 2, 0, 4, 1]], proof := .tail 69 }

theorem namedLeaf089_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3929)) namedLeaf089 = true :=
  by decide +kernel

def namedLeaf090 : LeafData := { rows := ![![1, 6, 4, 2, 5, 3], ![0, 6, 5, 4, 2, 3], ![4, 6, 0, 5, 1, 3], ![4, 5, 6, 0, 1, 2], ![3, 2, 6, 0, 5, 1], ![3, 6, 0, 2, 4, 1], ![3, 5, 2, 4, 0, 1]], proof := .tail 69 }

theorem namedLeaf090_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3930)) namedLeaf090 = true :=
  by decide +kernel

def namedLeaf091 : LeafData := { rows := ![![1, 6, 4, 2, 5, 3], ![0, 6, 5, 4, 2, 3], ![6, 4, 0, 5, 1, 3], ![4, 5, 6, 0, 1, 2], ![3, 6, 2, 0, 5, 1], ![3, 6, 0, 2, 4, 1], ![3, 5, 4, 2, 0, 1]], proof := .tail 121 }

theorem namedLeaf091_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3931)) namedLeaf091 = true :=
  by decide +kernel

def namedLeaf092 : LeafData := { rows := ![![1, 4, 6, 2, 5, 3], ![0, 6, 5, 4, 2, 3], ![4, 6, 0, 5, 1, 3], ![4, 6, 5, 0, 1, 2], ![3, 2, 0, 6, 5, 1], ![6, 3, 0, 2, 4, 1], ![5, 3, 2, 0, 4, 1]], proof := .tail 138 }

theorem namedLeaf092_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3932)) namedLeaf092 = true :=
  by decide +kernel

def namedLeaf093 : LeafData := { rows := ![![1, 6, 4, 2, 5, 3], ![0, 6, 5, 4, 2, 3], ![4, 6, 0, 5, 1, 3], ![4, 6, 5, 0, 1, 2], ![3, 2, 6, 0, 5, 1], ![6, 3, 0, 2, 4, 1], ![5, 3, 2, 4, 0, 1]], proof := .tail 36 }

theorem namedLeaf093_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3933)) namedLeaf093 = true :=
  by decide +kernel

def namedLeaf094 : LeafData := { rows := ![![1, 6, 4, 2, 5, 3], ![0, 6, 5, 4, 2, 3], ![6, 4, 0, 5, 1, 3], ![4, 6, 5, 0, 1, 2], ![3, 6, 2, 0, 5, 1], ![6, 3, 0, 2, 4, 1], ![5, 3, 4, 2, 0, 1]], proof := .tail 121 }

theorem namedLeaf094_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3934)) namedLeaf094 = true :=
  by decide +kernel

def namedLeaf095 : LeafData := { rows := ![![1, 6, 4, 2, 5, 3], ![0, 6, 5, 4, 2, 3], ![6, 4, 0, 5, 1, 3], ![6, 4, 5, 0, 1, 2], ![6, 3, 2, 0, 5, 1], ![6, 3, 0, 2, 4, 1], ![5, 4, 3, 2, 0, 1]], proof := .tail 243 }

theorem namedLeaf095_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3935)) namedLeaf095 = true :=
  by decide +kernel

def namedLeaf096 : LeafData := { rows := ![![1, 4, 5, 2, 3, 6], ![0, 4, 5, 2, 3, 6], ![4, 5, 0, 1, 3, 6], ![4, 5, 0, 1, 2, 6], ![3, 2, 0, 1, 5, 6], ![3, 2, 0, 1, 4, 6], ![0, 1, 2, 3, 4, 5]], proof := .low0 (![93, 190, 227, 134, 34, 230, 180, 116, 51, 48, 254, 172, 172, 223, 116, 116, 116, 116, 20, 63, 71, 194, 17, 109, 54, 63, 254, 40]) }

theorem namedLeaf096_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3936)) namedLeaf096 = true :=
  by decide +kernel

def namedLeaf097 : LeafData := { rows := ![![1, 4, 5, 2, 3, 6], ![0, 4, 5, 2, 3, 6], ![4, 5, 0, 1, 3, 6], ![4, 5, 0, 1, 2, 6], ![3, 2, 0, 1, 6, 5], ![3, 2, 0, 1, 6, 4], ![0, 1, 2, 3, 5, 4]], proof := .tail 136 }

theorem namedLeaf097_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3937)) namedLeaf097 = true :=
  by decide +kernel

def namedLeaf098 : LeafData := { rows := ![![1, 4, 5, 2, 3, 6], ![0, 4, 5, 2, 3, 6], ![4, 5, 0, 1, 6, 3], ![4, 5, 0, 1, 6, 2], ![3, 2, 0, 1, 5, 6], ![3, 2, 0, 1, 4, 6], ![0, 1, 3, 2, 4, 5]], proof := .tail 152 }

theorem namedLeaf098_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3938)) namedLeaf098 = true :=
  by decide +kernel

def namedLeaf099 : LeafData := { rows := ![![1, 4, 5, 2, 3, 6], ![0, 4, 5, 2, 6, 3], ![4, 5, 0, 1, 6, 3], ![4, 5, 0, 6, 1, 2], ![3, 2, 0, 1, 5, 6], ![3, 2, 0, 1, 4, 6], ![0, 3, 1, 2, 4, 5]], proof := .tail 256 }

theorem namedLeaf099_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3939)) namedLeaf099 = true :=
  by decide +kernel

def namedLeaf100 : LeafData := { rows := ![![1, 4, 5, 2, 3, 6], ![0, 4, 5, 6, 2, 3], ![4, 5, 0, 6, 1, 3], ![4, 5, 0, 6, 1, 2], ![3, 2, 0, 1, 5, 6], ![3, 2, 0, 1, 4, 6], ![0, 3, 2, 1, 4, 5]], proof := .tail 84 }

theorem namedLeaf100_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3940)) namedLeaf100 = true :=
  by decide +kernel

def namedLeaf101 : LeafData := { rows := ![![1, 4, 5, 2, 3, 6], ![0, 4, 5, 2, 3, 6], ![4, 5, 0, 1, 6, 3], ![4, 5, 0, 1, 6, 2], ![3, 2, 0, 1, 6, 5], ![3, 2, 0, 1, 6, 4], ![0, 1, 3, 2, 5, 4]], proof := .tail 152 }

theorem namedLeaf101_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3941)) namedLeaf101 = true :=
  by decide +kernel

def namedLeaf102 : LeafData := { rows := ![![1, 4, 5, 2, 3, 6], ![0, 4, 5, 2, 6, 3], ![4, 5, 0, 1, 6, 3], ![4, 5, 0, 6, 1, 2], ![3, 2, 0, 1, 6, 5], ![3, 2, 0, 1, 6, 4], ![0, 3, 1, 2, 5, 4]], proof := .tail 256 }

theorem namedLeaf102_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3942)) namedLeaf102 = true :=
  by decide +kernel

def namedLeaf103 : LeafData := { rows := ![![1, 4, 5, 2, 3, 6], ![0, 4, 5, 6, 2, 3], ![4, 5, 0, 6, 1, 3], ![4, 5, 0, 6, 1, 2], ![3, 2, 0, 1, 6, 5], ![3, 2, 0, 1, 6, 4], ![0, 3, 2, 1, 5, 4]], proof := .tail 84 }

theorem namedLeaf103_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3943)) namedLeaf103 = true :=
  by decide +kernel

def namedLeaf104 : LeafData := { rows := ![![1, 4, 5, 2, 3, 6], ![0, 4, 6, 5, 2, 3], ![4, 5, 0, 6, 1, 3], ![4, 5, 0, 6, 1, 2], ![3, 2, 0, 1, 6, 5], ![3, 2, 0, 6, 1, 4], ![0, 3, 2, 5, 1, 4]], proof := .tail 108 }

theorem namedLeaf104_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3944)) namedLeaf104 = true :=
  by decide +kernel

def namedLeaf105 : LeafData := { rows := ![![1, 4, 5, 2, 3, 6], ![0, 6, 4, 5, 2, 3], ![4, 5, 0, 6, 1, 3], ![4, 5, 0, 6, 1, 2], ![3, 2, 0, 6, 1, 5], ![3, 2, 0, 6, 1, 4], ![0, 3, 2, 5, 4, 1]], proof := .tail 95 }

theorem namedLeaf105_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3945)) namedLeaf105 = true :=
  by decide +kernel

def namedLeaf106 : LeafData := { rows := ![![1, 4, 5, 2, 6, 3], ![0, 4, 5, 2, 6, 3], ![4, 5, 0, 1, 6, 3], ![4, 5, 6, 0, 1, 2], ![3, 2, 0, 1, 5, 6], ![3, 2, 0, 1, 4, 6], ![3, 0, 1, 2, 4, 5]], proof := .low6 (![237, 208, 35, 197, 147, 66, 6, 182, 37, 57, 176, 61, 169, 8, 183, 82, 168, 169, 154, 249, 228, 78, 209, 7, 170, 156, 26, 102]) }

theorem namedLeaf106_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3946)) namedLeaf106 = true :=
  by decide +kernel

def namedLeaf107 : LeafData := { rows := ![![1, 4, 5, 2, 6, 3], ![0, 4, 5, 2, 6, 3], ![4, 5, 0, 1, 6, 3], ![4, 5, 6, 0, 1, 2], ![3, 2, 0, 1, 6, 5], ![3, 2, 0, 1, 6, 4], ![3, 0, 1, 2, 5, 4]], proof := .low0 (![115, 190, 148, 134, 38, 70, 205, 116, 252, 189, 106, 49, 94, 173, 116, 116, 116, 116, 210, 204, 86, 88, 75, 185, 231, 41, 5, 137]) }

theorem namedLeaf107_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3947)) namedLeaf107 = true :=
  by decide +kernel

def namedLeaf108 : LeafData := { rows := ![![1, 4, 5, 2, 6, 3], ![0, 4, 5, 6, 2, 3], ![4, 5, 0, 6, 1, 3], ![4, 5, 6, 0, 1, 2], ![3, 2, 0, 1, 5, 6], ![3, 2, 0, 1, 4, 6], ![3, 0, 2, 1, 4, 5]], proof := .tail 84 }

theorem namedLeaf108_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3948)) namedLeaf108 = true :=
  by decide +kernel

def namedLeaf109 : LeafData := { rows := ![![1, 4, 5, 2, 6, 3], ![0, 4, 5, 6, 2, 3], ![4, 5, 0, 6, 1, 3], ![4, 5, 6, 0, 1, 2], ![3, 2, 0, 1, 6, 5], ![3, 2, 0, 1, 6, 4], ![3, 0, 2, 1, 5, 4]], proof := .tail 84 }

theorem namedLeaf109_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3949)) namedLeaf109 = true :=
  by decide +kernel

def namedLeaf110 : LeafData := { rows := ![![1, 4, 5, 2, 6, 3], ![0, 4, 6, 5, 2, 3], ![4, 5, 0, 6, 1, 3], ![4, 5, 6, 0, 1, 2], ![3, 2, 0, 1, 6, 5], ![3, 2, 0, 6, 1, 4], ![3, 0, 2, 5, 1, 4]], proof := .tail 108 }

theorem namedLeaf110_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3950)) namedLeaf110 = true :=
  by decide +kernel

def namedLeaf111 : LeafData := { rows := ![![1, 4, 5, 2, 6, 3], ![0, 6, 4, 5, 2, 3], ![4, 5, 0, 6, 1, 3], ![4, 5, 6, 0, 1, 2], ![3, 2, 0, 6, 1, 5], ![3, 2, 0, 6, 1, 4], ![3, 0, 2, 5, 4, 1]], proof := .tail 95 }

theorem namedLeaf111_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3951)) namedLeaf111 = true :=
  by decide +kernel

def namedLeaf112 : LeafData := { rows := ![![1, 4, 5, 6, 2, 3], ![0, 4, 5, 6, 2, 3], ![4, 5, 6, 0, 1, 3], ![4, 5, 6, 0, 1, 2], ![3, 2, 0, 1, 5, 6], ![3, 2, 0, 1, 4, 6], ![3, 2, 0, 1, 4, 5]], proof := .low6 (![27, 132, 91, 218, 124, 66, 6, 45, 250, 247, 166, 44, 129, 186, 15, 45, 220, 220, 175, 126, 79, 169, 97, 112, 169, 246, 68, 102]) }

theorem namedLeaf112_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3952)) namedLeaf112 = true :=
  by decide +kernel

def namedLeaf113 : LeafData := { rows := ![![1, 4, 5, 6, 2, 3], ![0, 4, 5, 6, 2, 3], ![4, 5, 6, 0, 1, 3], ![4, 5, 6, 0, 1, 2], ![3, 2, 0, 1, 6, 5], ![3, 2, 0, 1, 6, 4], ![3, 2, 0, 1, 5, 4]], proof := .low6 (![27, 132, 91, 218, 233, 248, 195, 45, 250, 247, 85, 184, 2, 186, 15, 45, 184, 220, 175, 235, 184, 146, 83, 184, 207, 19, 216, 184]) }

theorem namedLeaf113_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3953)) namedLeaf113 = true :=
  by decide +kernel

def namedLeaf114 : LeafData := { rows := ![![1, 4, 5, 6, 2, 3], ![0, 4, 6, 5, 2, 3], ![4, 5, 6, 0, 1, 3], ![4, 5, 6, 0, 1, 2], ![3, 2, 0, 1, 6, 5], ![3, 2, 0, 6, 1, 4], ![3, 2, 0, 5, 1, 4]], proof := .tail 111 }

theorem namedLeaf114_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3954)) namedLeaf114 = true :=
  by decide +kernel

def namedLeaf115 : LeafData := { rows := ![![1, 4, 6, 5, 2, 3], ![0, 4, 6, 5, 2, 3], ![4, 5, 6, 0, 1, 3], ![4, 5, 6, 0, 1, 2], ![3, 2, 0, 1, 6, 5], ![3, 2, 6, 0, 1, 4], ![3, 2, 5, 0, 1, 4]], proof := .tail 47 }

theorem namedLeaf115_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3955)) namedLeaf115 = true :=
  by decide +kernel

def namedLeaf116 : LeafData := { rows := ![![1, 4, 6, 5, 2, 3], ![0, 4, 6, 5, 2, 3], ![4, 6, 5, 0, 1, 3], ![4, 5, 6, 0, 1, 2], ![3, 2, 0, 1, 6, 5], ![3, 6, 2, 0, 1, 4], ![3, 5, 2, 0, 1, 4]], proof := .tail 177 }

theorem namedLeaf116_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3956)) namedLeaf116 = true :=
  by decide +kernel

def namedLeaf117 : LeafData := { rows := ![![1, 4, 6, 5, 2, 3], ![0, 4, 6, 5, 2, 3], ![4, 6, 5, 0, 1, 3], ![4, 6, 5, 0, 1, 2], ![3, 2, 0, 1, 6, 5], ![6, 3, 2, 0, 1, 4], ![5, 3, 2, 0, 1, 4]], proof := .tail 135 }

theorem namedLeaf117_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3957)) namedLeaf117 = true :=
  by decide +kernel

def namedLeaf118 : LeafData := { rows := ![![1, 4, 5, 6, 2, 3], ![0, 6, 4, 5, 2, 3], ![4, 5, 6, 0, 1, 3], ![4, 5, 6, 0, 1, 2], ![3, 2, 0, 6, 1, 5], ![3, 2, 0, 6, 1, 4], ![3, 2, 0, 5, 4, 1]], proof := .tail 199 }

theorem namedLeaf118_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3958)) namedLeaf118 = true :=
  by decide +kernel

def namedLeaf119 : LeafData := { rows := ![![1, 4, 6, 5, 2, 3], ![0, 6, 4, 5, 2, 3], ![4, 5, 6, 0, 1, 3], ![4, 5, 6, 0, 1, 2], ![3, 2, 0, 6, 1, 5], ![3, 2, 6, 0, 1, 4], ![3, 2, 5, 0, 4, 1]], proof := .tail 199 }

theorem namedLeaf119_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3959)) namedLeaf119 = true :=
  by decide +kernel

def namedLeaf120 : LeafData := { rows := ![![1, 4, 6, 5, 2, 3], ![0, 6, 4, 5, 2, 3], ![4, 6, 5, 0, 1, 3], ![4, 5, 6, 0, 1, 2], ![3, 2, 0, 6, 1, 5], ![3, 6, 2, 0, 1, 4], ![3, 5, 2, 0, 4, 1]], proof := .tail 177 }

theorem namedLeaf120_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3960)) namedLeaf120 = true :=
  by decide +kernel

def namedLeaf121 : LeafData := { rows := ![![1, 4, 6, 5, 2, 3], ![0, 6, 4, 5, 2, 3], ![4, 6, 5, 0, 1, 3], ![4, 6, 5, 0, 1, 2], ![3, 2, 0, 6, 1, 5], ![6, 3, 2, 0, 1, 4], ![5, 3, 2, 0, 4, 1]], proof := .tail 199 }

theorem namedLeaf121_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3961)) namedLeaf121 = true :=
  by decide +kernel

def namedLeaf122 : LeafData := { rows := ![![1, 6, 4, 5, 2, 3], ![0, 6, 4, 5, 2, 3], ![4, 5, 6, 0, 1, 3], ![4, 5, 6, 0, 1, 2], ![3, 2, 6, 0, 1, 5], ![3, 2, 6, 0, 1, 4], ![3, 2, 5, 4, 0, 1]], proof := .tail 13 }

theorem namedLeaf122_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3962)) namedLeaf122 = true :=
  by decide +kernel

def namedLeaf123 : LeafData := { rows := ![![1, 6, 4, 5, 2, 3], ![0, 6, 4, 5, 2, 3], ![4, 6, 5, 0, 1, 3], ![4, 5, 6, 0, 1, 2], ![3, 2, 6, 0, 1, 5], ![3, 6, 2, 0, 1, 4], ![3, 5, 2, 4, 0, 1]], proof := .tail 177 }

theorem namedLeaf123_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3963)) namedLeaf123 = true :=
  by decide +kernel

def namedLeaf124 : LeafData := { rows := ![![1, 6, 4, 5, 2, 3], ![0, 6, 4, 5, 2, 3], ![4, 6, 5, 0, 1, 3], ![4, 6, 5, 0, 1, 2], ![3, 2, 6, 0, 1, 5], ![6, 3, 2, 0, 1, 4], ![5, 3, 2, 4, 0, 1]], proof := .tail 13 }

theorem namedLeaf124_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3964)) namedLeaf124 = true :=
  by decide +kernel

def namedLeaf125 : LeafData := { rows := ![![1, 6, 4, 5, 2, 3], ![0, 6, 4, 5, 2, 3], ![6, 4, 5, 0, 1, 3], ![4, 5, 6, 0, 1, 2], ![3, 6, 2, 0, 1, 5], ![3, 6, 2, 0, 1, 4], ![3, 5, 4, 2, 0, 1]], proof := .tail 206 }

theorem namedLeaf125_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3965)) namedLeaf125 = true :=
  by decide +kernel

def namedLeaf126 : LeafData := { rows := ![![1, 6, 4, 5, 2, 3], ![0, 6, 4, 5, 2, 3], ![6, 4, 5, 0, 1, 3], ![4, 6, 5, 0, 1, 2], ![3, 6, 2, 0, 1, 5], ![6, 3, 2, 0, 1, 4], ![5, 3, 4, 2, 0, 1]], proof := .tail 206 }

theorem namedLeaf126_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3966)) namedLeaf126 = true :=
  by decide +kernel

def namedLeaf127 : LeafData := { rows := ![![1, 6, 4, 5, 2, 3], ![0, 6, 4, 5, 2, 3], ![6, 4, 5, 0, 1, 3], ![6, 4, 5, 0, 1, 2], ![6, 3, 2, 0, 1, 5], ![6, 3, 2, 0, 1, 4], ![5, 4, 3, 2, 0, 1]], proof := .tail 81 }

theorem namedLeaf127_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3967)) namedLeaf127 = true :=
  by decide +kernel

def fallback : LeafData := { rows := fun _ _ => 0, proof := .tail 0 }
def lookup (offset : ℕ) : LeafData :=
  if offset < 128 then (if offset < 64 then
  (if offset < 32 then
  (if offset < 16 then
  (if offset < 8 then
  (if offset < 4 then
  (if offset < 2 then
  (if offset < 1 then
  (namedLeaf000) else
  (namedLeaf001)) else
  (if offset < 3 then
  (namedLeaf002) else
  (namedLeaf003))) else
  (if offset < 6 then
  (if offset < 5 then
  (namedLeaf004) else
  (namedLeaf005)) else
  (if offset < 7 then
  (namedLeaf006) else
  (namedLeaf007)))) else
  (if offset < 12 then
  (if offset < 10 then
  (if offset < 9 then
  (namedLeaf008) else
  (namedLeaf009)) else
  (if offset < 11 then
  (namedLeaf010) else
  (namedLeaf011))) else
  (if offset < 14 then
  (if offset < 13 then
  (namedLeaf012) else
  (namedLeaf013)) else
  (if offset < 15 then
  (namedLeaf014) else
  (namedLeaf015))))) else
  (if offset < 24 then
  (if offset < 20 then
  (if offset < 18 then
  (if offset < 17 then
  (namedLeaf016) else
  (namedLeaf017)) else
  (if offset < 19 then
  (namedLeaf018) else
  (namedLeaf019))) else
  (if offset < 22 then
  (if offset < 21 then
  (namedLeaf020) else
  (namedLeaf021)) else
  (if offset < 23 then
  (namedLeaf022) else
  (namedLeaf023)))) else
  (if offset < 28 then
  (if offset < 26 then
  (if offset < 25 then
  (namedLeaf024) else
  (namedLeaf025)) else
  (if offset < 27 then
  (namedLeaf026) else
  (namedLeaf027))) else
  (if offset < 30 then
  (if offset < 29 then
  (namedLeaf028) else
  (namedLeaf029)) else
  (if offset < 31 then
  (namedLeaf030) else
  (namedLeaf031)))))) else
  (if offset < 48 then
  (if offset < 40 then
  (if offset < 36 then
  (if offset < 34 then
  (if offset < 33 then
  (namedLeaf032) else
  (namedLeaf033)) else
  (if offset < 35 then
  (namedLeaf034) else
  (namedLeaf035))) else
  (if offset < 38 then
  (if offset < 37 then
  (namedLeaf036) else
  (namedLeaf037)) else
  (if offset < 39 then
  (namedLeaf038) else
  (namedLeaf039)))) else
  (if offset < 44 then
  (if offset < 42 then
  (if offset < 41 then
  (namedLeaf040) else
  (namedLeaf041)) else
  (if offset < 43 then
  (namedLeaf042) else
  (namedLeaf043))) else
  (if offset < 46 then
  (if offset < 45 then
  (namedLeaf044) else
  (namedLeaf045)) else
  (if offset < 47 then
  (namedLeaf046) else
  (namedLeaf047))))) else
  (if offset < 56 then
  (if offset < 52 then
  (if offset < 50 then
  (if offset < 49 then
  (namedLeaf048) else
  (namedLeaf049)) else
  (if offset < 51 then
  (namedLeaf050) else
  (namedLeaf051))) else
  (if offset < 54 then
  (if offset < 53 then
  (namedLeaf052) else
  (namedLeaf053)) else
  (if offset < 55 then
  (namedLeaf054) else
  (namedLeaf055)))) else
  (if offset < 60 then
  (if offset < 58 then
  (if offset < 57 then
  (namedLeaf056) else
  (namedLeaf057)) else
  (if offset < 59 then
  (namedLeaf058) else
  (namedLeaf059))) else
  (if offset < 62 then
  (if offset < 61 then
  (namedLeaf060) else
  (namedLeaf061)) else
  (if offset < 63 then
  (namedLeaf062) else
  (namedLeaf063))))))) else
  (if offset < 96 then
  (if offset < 80 then
  (if offset < 72 then
  (if offset < 68 then
  (if offset < 66 then
  (if offset < 65 then
  (namedLeaf064) else
  (namedLeaf065)) else
  (if offset < 67 then
  (namedLeaf066) else
  (namedLeaf067))) else
  (if offset < 70 then
  (if offset < 69 then
  (namedLeaf068) else
  (namedLeaf069)) else
  (if offset < 71 then
  (namedLeaf070) else
  (namedLeaf071)))) else
  (if offset < 76 then
  (if offset < 74 then
  (if offset < 73 then
  (namedLeaf072) else
  (namedLeaf073)) else
  (if offset < 75 then
  (namedLeaf074) else
  (namedLeaf075))) else
  (if offset < 78 then
  (if offset < 77 then
  (namedLeaf076) else
  (namedLeaf077)) else
  (if offset < 79 then
  (namedLeaf078) else
  (namedLeaf079))))) else
  (if offset < 88 then
  (if offset < 84 then
  (if offset < 82 then
  (if offset < 81 then
  (namedLeaf080) else
  (namedLeaf081)) else
  (if offset < 83 then
  (namedLeaf082) else
  (namedLeaf083))) else
  (if offset < 86 then
  (if offset < 85 then
  (namedLeaf084) else
  (namedLeaf085)) else
  (if offset < 87 then
  (namedLeaf086) else
  (namedLeaf087)))) else
  (if offset < 92 then
  (if offset < 90 then
  (if offset < 89 then
  (namedLeaf088) else
  (namedLeaf089)) else
  (if offset < 91 then
  (namedLeaf090) else
  (namedLeaf091))) else
  (if offset < 94 then
  (if offset < 93 then
  (namedLeaf092) else
  (namedLeaf093)) else
  (if offset < 95 then
  (namedLeaf094) else
  (namedLeaf095)))))) else
  (if offset < 112 then
  (if offset < 104 then
  (if offset < 100 then
  (if offset < 98 then
  (if offset < 97 then
  (namedLeaf096) else
  (namedLeaf097)) else
  (if offset < 99 then
  (namedLeaf098) else
  (namedLeaf099))) else
  (if offset < 102 then
  (if offset < 101 then
  (namedLeaf100) else
  (namedLeaf101)) else
  (if offset < 103 then
  (namedLeaf102) else
  (namedLeaf103)))) else
  (if offset < 108 then
  (if offset < 106 then
  (if offset < 105 then
  (namedLeaf104) else
  (namedLeaf105)) else
  (if offset < 107 then
  (namedLeaf106) else
  (namedLeaf107))) else
  (if offset < 110 then
  (if offset < 109 then
  (namedLeaf108) else
  (namedLeaf109)) else
  (if offset < 111 then
  (namedLeaf110) else
  (namedLeaf111))))) else
  (if offset < 120 then
  (if offset < 116 then
  (if offset < 114 then
  (if offset < 113 then
  (namedLeaf112) else
  (namedLeaf113)) else
  (if offset < 115 then
  (namedLeaf114) else
  (namedLeaf115))) else
  (if offset < 118 then
  (if offset < 117 then
  (namedLeaf116) else
  (namedLeaf117)) else
  (if offset < 119 then
  (namedLeaf118) else
  (namedLeaf119)))) else
  (if offset < 124 then
  (if offset < 122 then
  (if offset < 121 then
  (namedLeaf120) else
  (namedLeaf121)) else
  (if offset < 123 then
  (namedLeaf122) else
  (namedLeaf123))) else
  (if offset < 126 then
  (if offset < 125 then
  (namedLeaf124) else
  (namedLeaf125)) else
  (if offset < 127 then
  (namedLeaf126) else
  (namedLeaf127)))))))) else fallback

theorem point_checked (j : Fin 128) :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 (3840 + j.val))) (lookup j.val) = true := by
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

theorem correct (id : Fin 24698) (hlow : 3840 ≤ id.val) (hhigh : id.val < 3968) :
    leafCheck library (N4R2WordTree.catalog id) (lookup (id.val - 3840)) = true := by
  let j : Fin 128 := ⟨id.val - 3840, by omega⟩
  have hsum : 3840 + j.val = id.val := by dsimp [j]; omega
  have hindex : Fin.ofNat 24698 (3840 + j.val) = id := by
    apply Fin.ext
    simp only [Fin.ofNat, hsum, Nat.mod_eq_of_lt id.isLt]
  have hh := point_checked j
  rw [hindex] at hh
  exact hh

#print axioms point_checked
#print axioms correct

end Jsp404.N4R2ReplayData.LeafShard030
