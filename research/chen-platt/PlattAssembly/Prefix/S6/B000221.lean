import PlattAssemblyKernel
import PlattCertificates.Count131072.C057072
import PlattCertificates.Count131072.C057073
import PlattCertificates.Count131072.C057074
import PlattCertificates.Count131072.C057075
import PlattCertificates.Count131072.C057076
import PlattCertificates.Count131072.C057077
import PlattCertificates.Count131072.C057078
import PlattCertificates.Count131072.C057079
import PlattCertificates.Count131072.C057080
import PlattCertificates.Count131072.C057081
import PlattCertificates.Count131072.C057082
import PlattCertificates.Count131072.C057083
import PlattCertificates.Count131072.C057084
import PlattCertificates.Count131072.C057085
import PlattCertificates.Count131072.C057086
import PlattCertificates.Count131072.C057087
import PlattCertificates.Count131072.C057088
import PlattCertificates.Count131072.C057089
import PlattCertificates.Count131072.C057090
import PlattCertificates.Count131072.C057091
import PlattCertificates.Count131072.C057092
import PlattCertificates.Count131072.C057093
import PlattCertificates.Count131072.C057094
import PlattCertificates.Count131072.C057095
import PlattCertificates.Count131072.C057096
import PlattCertificates.Count131072.C057097
import PlattCertificates.Count131072.C057098
import PlattCertificates.Count131072.C057099
import PlattCertificates.Count131072.C057100
import PlattCertificates.Count131072.C057101
import PlattCertificates.Count131072.C057102
import PlattCertificates.Count131072.C057103
namespace ChenEffective.PlattWindow.Assembly.Prefix.S6.B000221
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts57072 : List PrefixCut := [⟨64,215114974,215115096⟩]
theorem checked57072 : checkPrefixCuts (2^48) 7484473345 10 Manual.Count131072.C057072.packed 64 cuts57072 = true := by
 decide +kernel
def cuts57073 : List PrefixCut := [⟨49,167501279,167501375⟩,
⟨64,218947113,218947237⟩]
theorem checked57073 : checkPrefixCuts (2^48) 7484604417 10 Manual.Count131072.C057073.packed 64 cuts57073 = true := by
 decide +kernel
def pointBounds57073 : List (Nat × Nat × Nat) := [(7484704768,113298838936119,113299226991030)]
theorem point_links_checked57073 : (cuts57073.take 1).map (fun c => (7484604417-1+2*2^10*c.k,113298671434840+c.lower,113299059489655+c.upper)) = pointBounds57073 := by
 decide +kernel
def cuts57074 : List PrefixCut := [⟨64,216009992,216010117⟩]
theorem checked57074 : checkPrefixCuts (2^48) 7484735489 10 Manual.Count131072.C057074.packed 64 cuts57074 = true := by
 decide +kernel
def cuts57075 : List PrefixCut := [⟨36,121353520,121353589⟩,
⟨64,214990851,214990975⟩]
theorem checked57075 : checkPrefixCuts (2^48) 7484866561 10 Manual.Count131072.C057075.packed 64 cuts57075 = true := by
 decide +kernel
def pointBounds57075 : List (Nat × Nat × Nat) := [(7484940288,113299227745465,113299615800598)]
theorem point_links_checked57075 : (cuts57075.take 1).map (fun c => (7484866561-1+2*2^10*c.k,113299106391945+c.lower,113299494447009+c.upper)) = pointBounds57075 := by
 decide +kernel
def cuts57076 : List PrefixCut := [⟨64,220477402,220477527⟩]
theorem checked57076 : checkPrefixCuts (2^48) 7484997633 10 Manual.Count131072.C057076.packed 64 cuts57076 = true := by
 decide +kernel
def cuts57077 : List PrefixCut := [⟨23,76073766,76073809⟩,
⟨64,214268844,214268965⟩]
theorem checked57077 : checkPrefixCuts (2^48) 7485128705 10 Manual.Count131072.C057077.packed 64 cuts57077 = true := by
 decide +kernel
def pointBounds57077 : List (Nat × Nat × Nat) := [(7485175808,113299617933964,113300005989320)]
theorem point_links_checked57077 : (cuts57077.take 1).map (fun c => (7485128705-1+2*2^10*c.k,113299541860198+c.lower,113299929915511+c.upper)) = pointBounds57077 := by
 decide +kernel
def cuts57078 : List PrefixCut := [⟨64,216032480,216032602⟩]
theorem checked57078 : checkPrefixCuts (2^48) 7485259777 10 Manual.Count131072.C057078.packed 64 cuts57078 = true := by
 decide +kernel
def cuts57079 : List PrefixCut := [⟨10,32639561,32639581⟩,
⟨64,214637366,214637491⟩]
theorem checked57079 : checkPrefixCuts (2^48) 7485390849 10 Manual.Count131072.C057079.packed 64 cuts57079 = true := by
 decide +kernel
def pointBounds57079 : List (Nat × Nat × Nat) := [(7485411328,113300004801083,113300392856659)]
theorem point_links_checked57079 : (cuts57079.take 1).map (fun c => (7485390849-1+2*2^10*c.k,113299972161522+c.lower,113300360217078+c.upper)) = pointBounds57079 := by
 decide +kernel
def cuts57080 : List PrefixCut := [⟨61,204932316,204932438⟩,
⟨64,215160041,215160169⟩]
theorem checked57080 : checkPrefixCuts (2^48) 7485521921 10 Manual.Count131072.C057080.packed 64 cuts57080 = true := by
 decide +kernel
def pointBounds57080 : List (Nat × Nat × Nat) := [(7485646848,113300391731204,113300779787007)]
theorem point_links_checked57080 : (cuts57080.take 1).map (fun c => (7485521921-1+2*2^10*c.k,113300186798888+c.lower,113300574854569+c.upper)) = pointBounds57080 := by
 decide +kernel
def cuts57081 : List PrefixCut := [⟨64,216622744,216622867⟩]
theorem checked57081 : checkPrefixCuts (2^48) 7485652993 10 Manual.Count131072.C057081.packed 64 cuts57081 = true := by
 decide +kernel
def cuts57082 : List PrefixCut := [⟨48,163000378,163000469⟩,
⟨64,216769355,216769476⟩]
theorem checked57082 : checkPrefixCuts (2^48) 7485784065 10 Manual.Count131072.C057082.packed 64 cuts57082 = true := by
 decide +kernel
def pointBounds57082 : List (Nat × Nat × Nat) := [(7485882368,113300781582051,113301169638074)]
theorem point_links_checked57082 : (cuts57082.take 1).map (fun c => (7485784065-1+2*2^10*c.k,113300618581673+c.lower,113301006637605+c.upper)) = pointBounds57082 := by
 decide +kernel
def cuts57083 : List PrefixCut := [⟨64,218006371,218006497⟩]
theorem checked57083 : checkPrefixCuts (2^48) 7485915137 10 Manual.Count131072.C057083.packed 64 cuts57083 = true := by
 decide +kernel
def cuts57084 : List PrefixCut := [⟨35,118928041,118928108⟩,
⟨64,217664153,217664275⟩]
theorem checked57084 : checkPrefixCuts (2^48) 7486046209 10 Manual.Count131072.C057084.packed 64 cuts57084 = true := by
 decide +kernel
def pointBounds57084 : List (Nat × Nat × Nat) := [(7486117888,113301172285440,113301560341686)]
theorem point_links_checked57084 : (cuts57084.take 1).map (fun c => (7486046209-1+2*2^10*c.k,113301053357399+c.lower,113301441413578+c.upper)) = pointBounds57084 := by
 decide +kernel
def cuts57085 : List PrefixCut := [⟨64,213486874,213487000⟩]
theorem checked57085 : checkPrefixCuts (2^48) 7486177281 10 Manual.Count131072.C057085.packed 64 cuts57085 = true := by
 decide +kernel
def cuts57086 : List PrefixCut := [⟨22,74971433,74971476⟩,
⟨64,219085277,219085400⟩]
theorem checked57086 : checkPrefixCuts (2^48) 7486308353 10 Manual.Count131072.C057086.packed 64 cuts57086 = true := by
 decide +kernel
def pointBounds57086 : List (Nat × Nat × Nat) := [(7486353408,113301559479859,113301947536329)]
theorem point_links_checked57086 : (cuts57086.take 1).map (fun c => (7486308353-1+2*2^10*c.k,113301484508426+c.lower,113301872564853+c.upper)) = pointBounds57086 := by
 decide +kernel
def cuts57087 : List PrefixCut := [⟨64,216787972,216788094⟩]
theorem checked57087 : checkPrefixCuts (2^48) 7486439425 10 Manual.Count131072.C057087.packed 64 cuts57087 = true := by
 decide +kernel
def cuts57088 : List PrefixCut := [⟨9,30040212,30040229⟩,
⟨64,215468288,215468407⟩]
theorem checked57088 : checkPrefixCuts (2^48) 7486570497 10 Manual.Count131072.C057088.packed 64 cuts57088 = true := by
 decide +kernel
def pointBounds57088 : List (Nat × Nat × Nat) := [(7486588928,113301950421887,113302338478576)]
theorem point_links_checked57088 : (cuts57088.take 1).map (fun c => (7486570497-1+2*2^10*c.k,113301920381675+c.lower,113302308438347+c.upper)) = pointBounds57088 := by
 decide +kernel
def cuts57089 : List PrefixCut := [⟨60,206403913,206404027⟩,
⟨64,219938477,219938599⟩]
theorem checked57089 : checkPrefixCuts (2^48) 7486701569 10 Manual.Count131072.C057089.packed 64 cuts57089 = true := by
 decide +kernel
def pointBounds57089 : List (Nat × Nat × Nat) := [(7486824448,113302342253876,113302730310781)]
theorem point_links_checked57089 : (cuts57089.take 1).map (fun c => (7486701569-1+2*2^10*c.k,113302135849963+c.lower,113302523906754+c.upper)) = pointBounds57089 := by
 decide +kernel
def cuts57090 : List PrefixCut := [⟨64,221739200,221739325⟩]
theorem checked57090 : checkPrefixCuts (2^48) 7486832641 10 Manual.Count131072.C057090.packed 64 cuts57090 = true := by
 decide +kernel
def cuts57091 : List PrefixCut := [⟨47,157373057,157373149⟩,
⟨64,216096077,216096202⟩]
theorem checked57091 : checkPrefixCuts (2^48) 7486963713 10 Manual.Count131072.C057091.packed 64 cuts57091 = true := by
 decide +kernel
def pointBounds57091 : List (Nat × Nat × Nat) := [(7487059968,113302734900697,113303122957827)]
theorem point_links_checked57091 : (cuts57091.take 1).map (fun c => (7486963713-1+2*2^10*c.k,113302577527640+c.lower,113302965584678+c.upper)) = pointBounds57091 := by
 decide +kernel
def cuts57092 : List PrefixCut := [⟨64,218272753,218272880⟩]
theorem checked57092 : checkPrefixCuts (2^48) 7487094785 10 Manual.Count131072.C057092.packed 64 cuts57092 = true := by
 decide +kernel
def cuts57093 : List PrefixCut := [⟨34,114773998,114774062⟩,
⟨64,214058470,214058593⟩]
theorem checked57093 : checkPrefixCuts (2^48) 7487225857 10 Manual.Count131072.C057093.packed 64 cuts57093 = true := by
 decide +kernel
def pointBounds57093 : List (Nat × Nat × Nat) := [(7487295488,113303126670468,113303514727822)]
theorem point_links_checked57093 : (cuts57093.take 1).map (fun c => (7487225857-1+2*2^10*c.k,113303011896470+c.lower,113303399953760+c.upper)) = pointBounds57093 := by
 decide +kernel
def cuts57094 : List PrefixCut := [⟨64,214731397,214731514⟩]
theorem checked57094 : checkPrefixCuts (2^48) 7487356929 10 Manual.Count131072.C057094.packed 64 cuts57094 = true := by
 decide +kernel
def cuts57095 : List PrefixCut := [⟨21,71050002,71050044⟩,
⟨64,217547057,217547183⟩]
theorem checked57095 : checkPrefixCuts (2^48) 7487488001 10 Manual.Count131072.C057095.packed 64 cuts57095 = true := by
 decide +kernel
def pointBounds57095 : List (Nat × Nat × Nat) := [(7487531008,113303511736339,113303899793911)]
theorem point_links_checked57095 : (cuts57095.take 1).map (fun c => (7487488001-1+2*2^10*c.k,113303440686337+c.lower,113303828743867+c.upper)) = pointBounds57095 := by
 decide +kernel
def cuts57096 : List PrefixCut := [⟨64,214723872,214723997⟩]
theorem checked57096 : checkPrefixCuts (2^48) 7487619073 10 Manual.Count131072.C057096.packed 64 cuts57096 = true := by
 decide +kernel
def cuts57097 : List PrefixCut := [⟨8,25787661,25787675⟩,
⟨64,216110959,216111083⟩]
theorem checked57097 : checkPrefixCuts (2^48) 7487750145 10 Manual.Count131072.C057097.packed 64 cuts57097 = true := by
 decide +kernel
def pointBounds57097 : List (Nat × Nat × Nat) := [(7487766528,113303898744927,113304286802722)]
theorem point_links_checked57097 : (cuts57097.take 1).map (fun c => (7487750145-1+2*2^10*c.k,113303872957266+c.lower,113304261015047+c.upper)) = pointBounds57097 := by
 decide +kernel
def cuts57098 : List PrefixCut := [⟨59,199266828,199266942⟩,
⟨64,216520682,216520805⟩]
theorem checked57098 : checkPrefixCuts (2^48) 7487881217 10 Manual.Count131072.C057098.packed 64 cuts57098 = true := by
 decide +kernel
def pointBounds57098 : List (Nat × Nat × Nat) := [(7488002048,113304288335053,113304676393072)]
theorem point_links_checked57098 : (cuts57098.take 1).map (fun c => (7487881217-1+2*2^10*c.k,113304089068225+c.lower,113304477126130+c.upper)) = pointBounds57098 := by
 decide +kernel
def cuts57099 : List PrefixCut := [⟨64,216930398,216930521⟩]
theorem checked57099 : checkPrefixCuts (2^48) 7488012289 10 Manual.Count131072.C057099.packed 64 cuts57099 = true := by
 decide +kernel
def cuts57100 : List PrefixCut := [⟨46,157085158,157085249⟩,
⟨64,218881223,218881349⟩]
theorem checked57100 : checkPrefixCuts (2^48) 7488143361 10 Manual.Count131072.C057100.packed 64 cuts57100 = true := by
 decide +kernel
def pointBounds57100 : List (Nat × Nat × Nat) := [(7488237568,113304679604463,113305067662705)]
theorem point_links_checked57100 : (cuts57100.take 1).map (fun c => (7488143361-1+2*2^10*c.k,113304522519305+c.lower,113304910577456+c.upper)) = pointBounds57100 := by
 decide +kernel
def cuts57101 : List PrefixCut := [⟨64,219441217,219441337⟩]
theorem checked57101 : checkPrefixCuts (2^48) 7488274433 10 Manual.Count131072.C057101.packed 64 cuts57101 = true := by
 decide +kernel
def cuts57102 : List PrefixCut := [⟨33,109493628,109493689⟩,
⟨64,216242404,216242524⟩]
theorem checked57102 : checkPrefixCuts (2^48) 7488405505 10 Manual.Count131072.C057102.packed 64 cuts57102 = true := by
 decide +kernel
def pointBounds57102 : List (Nat × Nat × Nat) := [(7488473088,113305070335373,113305458393831)]
theorem point_links_checked57102 : (cuts57102.take 1).map (fun c => (7488405505-1+2*2^10*c.k,113304960841745+c.lower,113305348900142+c.upper)) = pointBounds57102 := by
 decide +kernel
def cuts57103 : List PrefixCut := [⟨64,215637241,215637363⟩]
theorem checked57103 : checkPrefixCuts (2^48) 7488536577 10 Manual.Count131072.C057103.packed 64 cuts57103 = true := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S6.B000221
