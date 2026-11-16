import PlattAssemblyKernel
import PlattCertificates.Count131072.C047040
import PlattCertificates.Count131072.C047041
import PlattCertificates.Count131072.C047042
import PlattCertificates.Count131072.C047043
import PlattCertificates.Count131072.C047044
import PlattCertificates.Count131072.C047045
import PlattCertificates.Count131072.C047046
import PlattCertificates.Count131072.C047047
import PlattCertificates.Count131072.C047048
import PlattCertificates.Count131072.C047049
import PlattCertificates.Count131072.C047050
import PlattCertificates.Count131072.C047051
import PlattCertificates.Count131072.C047052
import PlattCertificates.Count131072.C047053
import PlattCertificates.Count131072.C047054
import PlattCertificates.Count131072.C047055
import PlattCertificates.Count131072.C047056
import PlattCertificates.Count131072.C047057
import PlattCertificates.Count131072.C047058
import PlattCertificates.Count131072.C047059
import PlattCertificates.Count131072.C047060
import PlattCertificates.Count131072.C047061
import PlattCertificates.Count131072.C047062
import PlattCertificates.Count131072.C047063
import PlattCertificates.Count131072.C047064
import PlattCertificates.Count131072.C047065
import PlattCertificates.Count131072.C047066
import PlattCertificates.Count131072.C047067
import PlattCertificates.Count131072.C047068
import PlattCertificates.Count131072.C047069
import PlattCertificates.Count131072.C047070
import PlattCertificates.Count131072.C047071
namespace ChenEffective.PlattWindow.Assembly.Prefix.S5.B000220
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts47040 : List PrefixCut := [⟨64,265067857,265068009⟩]
theorem checked47040 : checkPrefixCuts (2^48) 6169559041 10 Manual.Count131072.C047040.packed 64 cuts47040 = true := by
 decide +kernel
def cuts47041 : List PrefixCut := [⟨17,72037268,72037310⟩,
⟨64,266659006,266659161⟩]
theorem checked47041 : checkPrefixCuts (2^48) 6169690113 10 Manual.Count131072.C047041.packed 64 cuts47041 = true := by
 decide +kernel
def pointBounds47041 : List (Nat × Nat × Nat) := [(6169724928,110896744547950,110897131235738)]
theorem point_links_checked47041 : (cuts47041.take 1).map (fun c => (6169690113-1+2*2^10*c.k,110896672510682+c.lower,110897059198428+c.upper)) = pointBounds47041 := by
 decide +kernel
def cuts47042 : List PrefixCut := [⟨48,200777463,200777582⟩,
⟨64,266425209,266425363⟩]
theorem checked47042 : checkPrefixCuts (2^48) 6169821185 10 Manual.Count131072.C047042.packed 64 cuts47042 = true := by
 decide +kernel
def pointBounds47042 : List (Nat × Nat × Nat) := [(6169919488,110897139947151,110897526635171)]
theorem point_links_checked47042 : (cuts47042.take 1).map (fun c => (6169821185-1+2*2^10*c.k,110896939169688+c.lower,110897325857589+c.upper)) = pointBounds47042 := by
 decide +kernel
def cuts47043 : List PrefixCut := [⟨64,264275426,264275574⟩]
theorem checked47043 : checkPrefixCuts (2^48) 6169952257 10 Manual.Count131072.C047043.packed 64 cuts47043 = true := by
 decide +kernel
def cuts47044 : List PrefixCut := [⟨15,63593146,63593183⟩,
⟨64,267417515,267417664⟩]
theorem checked47044 : checkPrefixCuts (2^48) 6170083329 10 Manual.Count131072.C047044.packed 64 cuts47044 = true := by
 decide +kernel
def pointBounds47044 : List (Nat × Nat × Nat) := [(6170114048,110897533463469,110897920151709)]
theorem point_links_checked47044 : (cuts47044.take 1).map (fun c => (6170083329-1+2*2^10*c.k,110897469870323+c.lower,110897856558526+c.upper)) = pointBounds47044 := by
 decide +kernel
def cuts47045 : List PrefixCut := [⟨46,189132161,189132268⟩,
⟨64,262986895,262987047⟩]
theorem checked47045 : checkPrefixCuts (2^48) 6170214401 10 Manual.Count131072.C047045.packed 64 cuts47045 = true := by
 decide +kernel
def pointBounds47045 : List (Nat × Nat × Nat) := [(6170308608,110897926419999,110898313108458)]
theorem point_links_checked47045 : (cuts47045.take 1).map (fun c => (6170214401-1+2*2^10*c.k,110897737287838+c.lower,110898123976190+c.upper)) = pointBounds47045 := by
 decide +kernel
def cuts47046 : List PrefixCut := [⟨64,266174485,266174636⟩]
theorem checked47046 : checkPrefixCuts (2^48) 6170345473 10 Manual.Count131072.C047046.packed 64 cuts47046 = true := by
 decide +kernel
def cuts47047 : List PrefixCut := [⟨13,53735995,53736028⟩,
⟨64,263203800,263203951⟩]
theorem checked47047 : checkPrefixCuts (2^48) 6170476545 10 Manual.Count131072.C047047.packed 64 cuts47047 = true := by
 decide +kernel
def pointBounds47047 : List (Nat × Nat × Nat) := [(6170503168,110898320185213,110898706873901)]
theorem point_links_checked47047 : (cuts47047.take 1).map (fun c => (6170476545-1+2*2^10*c.k,110898266449218+c.lower,110898653137873+c.upper)) = pointBounds47047 := by
 decide +kernel
def cuts47048 : List PrefixCut := [⟨44,186748194,186748305⟩,
⟨64,268991334,268991494⟩]
theorem checked47048 : checkPrefixCuts (2^48) 6170607617 10 Manual.Count131072.C047048.packed 64 cuts47048 = true := by
 decide +kernel
def pointBounds47048 : List (Nat × Nat × Nat) := [(6170697728,110898716401212,110899103090129)]
theorem point_links_checked47048 : (cuts47048.take 1).map (fun c => (6170607617-1+2*2^10*c.k,110898529653018+c.lower,110898916341824+c.upper)) = pointBounds47048 := by
 decide +kernel
def cuts47049 : List PrefixCut := [⟨64,263329467,263329620⟩]
theorem checked47049 : checkPrefixCuts (2^48) 6170738689 10 Manual.Count131072.C047049.packed 64 cuts47049 = true := by
 decide +kernel
def cuts47050 : List PrefixCut := [⟨11,47027420,47027446⟩,
⟨64,263095813,263095965⟩]
theorem checked47050 : checkPrefixCuts (2^48) 6170869761 10 Manual.Count131072.C047050.packed 64 cuts47050 = true := by
 decide +kernel
def pointBounds47050 : List (Nat × Nat × Nat) := [(6170892288,110899109001239,110899495690384)]
theorem point_links_checked47050 : (cuts47050.take 1).map (fun c => (6170869761-1+2*2^10*c.k,110899061973819+c.lower,110899448662938+c.upper)) = pointBounds47050 := by
 decide +kernel
def cuts47051 : List PrefixCut := [⟨42,176884117,176884213⟩,
⟨64,267605813,267605967⟩]
theorem checked47051 : checkPrefixCuts (2^48) 6171000833 10 Manual.Count131072.C047051.packed 64 cuts47051 = true := by
 decide +kernel
def pointBounds47051 : List (Nat × Nat × Nat) := [(6171086848,110899501953749,110899888643116)]
theorem point_links_checked47051 : (cuts47051.take 1).map (fun c => (6171000833-1+2*2^10*c.k,110899325069632+c.lower,110899711758903+c.upper)) = pointBounds47051 := by
 decide +kernel
def cuts47052 : List PrefixCut := [⟨64,262491669,262491817⟩]
theorem checked47052 : checkPrefixCuts (2^48) 6171131905 10 Manual.Count131072.C047052.packed 64 cuts47052 = true := by
 decide +kernel
def cuts47053 : List PrefixCut := [⟨9,37902338,37902357⟩,
⟨64,264356133,264356281⟩]
theorem checked47053 : checkPrefixCuts (2^48) 6171262977 10 Manual.Count131072.C047053.packed 64 cuts47053 = true := by
 decide +kernel
def pointBounds47053 : List (Nat × Nat × Nat) := [(6171281408,110899893069452,110900279759044)]
theorem point_links_checked47053 : (cuts47053.take 1).map (fun c => (6171262977-1+2*2^10*c.k,110899855167114+c.lower,110900241856687+c.upper)) = pointBounds47053 := by
 decide +kernel
def cuts47054 : List PrefixCut := [⟨40,169438590,169438685⟩,
⟨64,267862437,267862592⟩]
theorem checked47054 : checkPrefixCuts (2^48) 6171394049 10 Manual.Count131072.C047054.packed 64 cuts47054 = true := by
 decide +kernel
def pointBounds47054 : List (Nat × Nat × Nat) := [(6171475968,110900288961837,110900675651653)]
theorem point_links_checked47054 : (cuts47054.take 1).map (fun c => (6171394049-1+2*2^10*c.k,110900119523247+c.lower,110900506212968+c.upper)) = pointBounds47054 := by
 decide +kernel
def cuts47055 : List PrefixCut := [⟨64,263934427,263934572⟩]
theorem checked47055 : checkPrefixCuts (2^48) 6171525121 10 Manual.Count131072.C047055.packed 64 cuts47055 = true := by
 decide +kernel
def cuts47056 : List PrefixCut := [⟨7,27136535,27136553⟩,
⟨64,264886549,264886706⟩]
theorem checked47056 : checkPrefixCuts (2^48) 6171656193 10 Manual.Count131072.C047056.packed 64 cuts47056 = true := by
 decide +kernel
def pointBounds47056 : List (Nat × Nat × Nat) := [(6171670528,110900678456646,110901065146685)]
theorem point_links_checked47056 : (cuts47056.take 1).map (fun c => (6171656193-1+2*2^10*c.k,110900651320111+c.lower,110901038010132+c.upper)) = pointBounds47056 := by
 decide +kernel
def cuts47057 : List PrefixCut := [⟨38,157159728,157159818⟩,
⟨64,265747459,265747612⟩]
theorem checked47057 : checkPrefixCuts (2^48) 6171787265 10 Manual.Count131072.C047057.packed 64 cuts47057 = true := by
 decide +kernel
def pointBounds47057 : List (Nat × Nat × Nat) := [(6171865088,110901073366388,110901460056656)]
theorem point_links_checked47057 : (cuts47057.take 1).map (fun c => (6171787265-1+2*2^10*c.k,110900916206660+c.lower,110901302896838+c.upper)) = pointBounds47057 := by
 decide +kernel
def cuts47058 : List PrefixCut := [⟨64,262366988,262367139⟩]
theorem checked47058 : checkPrefixCuts (2^48) 6171918337 10 Manual.Count131072.C047058.packed 64 cuts47058 = true := by
 decide +kernel
def cuts47059 : List PrefixCut := [⟨5,21479828,21479841⟩,
⟨64,267149929,267150081⟩]
theorem checked47059 : checkPrefixCuts (2^48) 6172049409 10 Manual.Count131072.C047059.packed 64 cuts47059 = true := by
 decide +kernel
def pointBounds47059 : List (Nat × Nat × Nat) := [(6172059648,110901465800935,110901852491430)]
theorem point_links_checked47059 : (cuts47059.take 1).map (fun c => (6172049409-1+2*2^10*c.k,110901444321107+c.lower,110901831011589+c.upper)) = pointBounds47059 := by
 decide +kernel
def cuts47060 : List PrefixCut := [⟨36,150902080,150902167⟩,
⟨64,265000906,265001055⟩]
theorem checked47060 : checkPrefixCuts (2^48) 6172180481 10 Manual.Count131072.C047060.packed 64 cuts47060 = true := by
 decide +kernel
def pointBounds47060 : List (Nat × Nat × Nat) := [(6172254208,110901862373116,110902249063837)]
theorem point_links_checked47060 : (cuts47060.take 1).map (fun c => (6172180481-1+2*2^10*c.k,110901711471036+c.lower,110902098161670+c.upper)) = pointBounds47060 := by
 decide +kernel
def cuts47061 : List PrefixCut := [⟨64,268461061,268461214⟩]
theorem checked47061 : checkPrefixCuts (2^48) 6172311553 10 Manual.Count131072.C047061.packed 64 cuts47061 = true := by
 decide +kernel
def cuts47062 : List PrefixCut := [⟨3,13042127,13042135⟩,
⟨64,267178503,267178654⟩]
theorem checked47062 : checkPrefixCuts (2^48) 6172442625 10 Manual.Count131072.C047062.packed 64 cuts47062 = true := by
 decide +kernel
def pointBounds47062 : List (Nat × Nat × Nat) := [(6172448768,110902257975130,110902644666074)]
theorem point_links_checked47062 : (cuts47062.take 1).map (fun c => (6172442625-1+2*2^10*c.k,110902244933003+c.lower,110902631623939+c.upper)) = pointBounds47062 := by
 decide +kernel
def cuts47063 : List PrefixCut := [⟨34,140085170,140085251⟩,
⟨64,267765614,267765765⟩]
theorem checked47063 : checkPrefixCuts (2^48) 6172573697 10 Manual.Count131072.C047063.packed 64 cuts47063 = true := by
 decide +kernel
def pointBounds47063 : List (Nat × Nat × Nat) := [(6172643328,110902652196676,110903038887844)]
theorem point_links_checked47063 : (cuts47063.take 1).map (fun c => (6172573697-1+2*2^10*c.k,110902512111506+c.lower,110902898802593+c.upper)) = pointBounds47063 := by
 decide +kernel
def cuts47064 : List PrefixCut := [⟨64,267851164,267851319⟩]
theorem checked47064 : checkPrefixCuts (2^48) 6172704769 10 Manual.Count131072.C047064.packed 64 cuts47064 = true := by
 decide +kernel
def cuts47065 : List PrefixCut := [⟨1,4103906,4103908⟩,
⟨64,264744730,264744879⟩]
theorem checked47065 : checkPrefixCuts (2^48) 6172835841 10 Manual.Count131072.C047065.packed 64 cuts47065 = true := by
 decide +kernel
def pointBounds47065 : List (Nat × Nat × Nat) := [(6172837888,110903051832190,110903438523585)]
theorem point_links_checked47065 : (cuts47065.take 1).map (fun c => (6172835841-1+2*2^10*c.k,110903047728284+c.lower,110903434419677+c.upper)) = pointBounds47065 := by
 decide +kernel
def cuts47066 : List PrefixCut := [⟨32,132826245,132826320⟩,
⟨64,262231289,262231440⟩]
theorem checked47066 : checkPrefixCuts (2^48) 6172966913 10 Manual.Count131072.C047066.packed 64 cuts47066 = true := by
 decide +kernel
def pointBounds47066 : List (Nat × Nat × Nat) := [(6173032448,110903445299259,110903831990876)]
theorem point_links_checked47066 : (cuts47066.take 1).map (fun c => (6172966913-1+2*2^10*c.k,110903312473014+c.lower,110903699164556+c.upper)) = pointBounds47066 := by
 decide +kernel
def cuts47067 : List PrefixCut := [⟨63,261587370,261587521⟩,
⟨64,266010188,266010342⟩]
theorem checked47067 : checkPrefixCuts (2^48) 6173097985 10 Manual.Count131072.C047067.packed 64 cuts47067 = true := by
 decide +kernel
def pointBounds47067 : List (Nat × Nat × Nat) := [(6173227008,110903836291673,110904222983517)]
theorem point_links_checked47067 : (cuts47067.take 1).map (fun c => (6173097985-1+2*2^10*c.k,110903574704303+c.lower,110903961395996+c.upper)) = pointBounds47067 := by
 decide +kernel
def cuts47068 : List PrefixCut := [⟨64,264727868,264728021⟩]
theorem checked47068 : checkPrefixCuts (2^48) 6173229057 10 Manual.Count131072.C047068.packed 64 cuts47068 = true := by
 decide +kernel
def cuts47069 : List PrefixCut := [⟨30,123470877,123470951⟩,
⟨64,261302677,261302830⟩]
theorem checked47069 : checkPrefixCuts (2^48) 6173360129 10 Manual.Count131072.C047069.packed 64 cuts47069 = true := by
 decide +kernel
def pointBounds47069 : List (Nat × Nat × Nat) := [(6173421568,110904228913236,110904615605310)]
theorem point_links_checked47069 : (cuts47069.take 1).map (fun c => (6173360129-1+2*2^10*c.k,110904105442359+c.lower,110904492134359+c.upper)) = pointBounds47069 := by
 decide +kernel
def cuts47070 : List PrefixCut := [⟨61,250993112,250993258⟩,
⟨64,265172589,265172744⟩]
theorem checked47070 : checkPrefixCuts (2^48) 6173491201 10 Manual.Count131072.C047070.packed 64 cuts47070 = true := by
 decide +kernel
def pointBounds47070 : List (Nat × Nat × Nat) := [(6173616128,110904617738148,110905004430447)]
theorem point_links_checked47070 : (cuts47070.take 1).map (fun c => (6173491201-1+2*2^10*c.k,110904366745036+c.lower,110904753437189+c.upper)) = pointBounds47070 := by
 decide +kernel
def cuts47071 : List PrefixCut := [⟨64,267036256,267036411⟩]
theorem checked47071 : checkPrefixCuts (2^48) 6173622273 10 Manual.Count131072.C047071.packed 64 cuts47071 = true := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S5.B000220
