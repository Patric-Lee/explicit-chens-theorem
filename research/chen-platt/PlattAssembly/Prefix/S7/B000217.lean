import PlattAssemblyKernel
import PlattCertificates.Count131072.C066944
import PlattCertificates.Count131072.C066945
import PlattCertificates.Count131072.C066946
import PlattCertificates.Count131072.C066947
import PlattCertificates.Count131072.C066948
import PlattCertificates.Count131072.C066949
import PlattCertificates.Count131072.C066950
import PlattCertificates.Count131072.C066951
import PlattCertificates.Count131072.C066952
import PlattCertificates.Count131072.C066953
import PlattCertificates.Count131072.C066954
import PlattCertificates.Count131072.C066955
import PlattCertificates.Count131072.C066956
import PlattCertificates.Count131072.C066957
import PlattCertificates.Count131072.C066958
import PlattCertificates.Count131072.C066959
import PlattCertificates.Count131072.C066960
import PlattCertificates.Count131072.C066961
import PlattCertificates.Count131072.C066962
import PlattCertificates.Count131072.C066963
import PlattCertificates.Count131072.C066964
import PlattCertificates.Count131072.C066965
import PlattCertificates.Count131072.C066966
import PlattCertificates.Count131072.C066967
import PlattCertificates.Count131072.C066968
import PlattCertificates.Count131072.C066969
import PlattCertificates.Count131072.C066970
import PlattCertificates.Count131072.C066971
import PlattCertificates.Count131072.C066972
import PlattCertificates.Count131072.C066973
import PlattCertificates.Count131072.C066974
import PlattCertificates.Count131072.C066975
namespace ChenEffective.PlattWindow.Assembly.Prefix.S7.B000217
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts66944 : List PrefixCut := [⟨60,172890178,172890285⟩,
⟨64,184850037,184850151⟩]
theorem checked66944 : checkPrefixCuts (2^48) 8778416129 10 Manual.Count131072.C066944.packed 64 cuts66944 = true := by
 decide +kernel
def pointBounds66944 : List (Nat × Nat × Nat) := [(8778539008,115265902312924,115266291497363)]
theorem point_links_checked66944 : (cuts66944.take 1).map (fun c => (8778416129-1+2*2^10*c.k,115265729422746+c.lower,115266118607078+c.upper)) = pointBounds66944 := by
 decide +kernel
def cuts66945 : List PrefixCut := [⟨64,181929494,181929602⟩]
theorem checked66945 : checkPrefixCuts (2^48) 8778547201 10 Manual.Count131072.C066945.packed 64 cuts66945 = true := by
 decide +kernel
def cuts66946 : List PrefixCut := [⟨64,185870551,185870653⟩]
theorem checked66946 : checkPrefixCuts (2^48) 8778678273 10 Manual.Count131072.C066946.packed 64 cuts66946 = true := by
 decide +kernel
def cuts66947 : List PrefixCut := [⟨2,4969762,4969766⟩,
⟨64,182693556,182693669⟩]
theorem checked66947 : checkPrefixCuts (2^48) 8778809345 10 Manual.Count131072.C066947.packed 64 cuts66947 = true := by
 decide +kernel
def pointBounds66947 : List (Nat × Nat × Nat) := [(8778813440,115266287042590,115266676227250)]
theorem point_links_checked66947 : (cuts66947.take 1).map (fun c => (8778809345-1+2*2^10*c.k,115266282072828+c.lower,115266671257484+c.upper)) = pointBounds66947 := by
 decide +kernel
def cuts66948 : List PrefixCut := [⟨64,181183899,181184008⟩]
theorem checked66948 : checkPrefixCuts (2^48) 8778940417 10 Manual.Count131072.C066948.packed 64 cuts66948 = true := by
 decide +kernel
def cuts66949 : List PrefixCut := [⟨8,22475464,22475478⟩,
⟨64,183008723,183008835⟩]
theorem checked66949 : checkPrefixCuts (2^48) 8779071489 10 Manual.Count131072.C066949.packed 64 cuts66949 = true := by
 decide +kernel
def pointBounds66949 : List (Nat × Nat × Nat) := [(8779087872,115266668425747,115267057610639)]
theorem point_links_checked66949 : (cuts66949.take 1).map (fun c => (8779071489-1+2*2^10*c.k,115266645950283+c.lower,115267035135161+c.upper)) = pointBounds66949 := by
 decide +kernel
def cuts66950 : List PrefixCut := [⟨64,184288441,184288550⟩]
theorem checked66950 : checkPrefixCuts (2^48) 8779202561 10 Manual.Count131072.C066950.packed 64 cuts66950 = true := by
 decide +kernel
def cuts66951 : List PrefixCut := [⟨14,40621320,40621341⟩,
⟨64,184381889,184381990⟩]
theorem checked66951 : checkPrefixCuts (2^48) 8779333633 10 Manual.Count131072.C066951.packed 64 cuts66951 = true := by
 decide +kernel
def pointBounds66951 : List (Nat × Nat × Nat) := [(8779362304,115267053868767,115267443053887)]
theorem point_links_checked66951 : (cuts66951.take 1).map (fun c => (8779333633-1+2*2^10*c.k,115267013247447+c.lower,115267402432546+c.upper)) = pointBounds66951 := by
 decide +kernel
def cuts66952 : List PrefixCut := [⟨64,183353201,183353306⟩]
theorem checked66952 : checkPrefixCuts (2^48) 8779464705 10 Manual.Count131072.C066952.packed 64 cuts66952 = true := by
 decide +kernel
def cuts66953 : List PrefixCut := [⟨20,57002762,57002795⟩,
⟨64,184921385,184921495⟩]
theorem checked66953 : checkPrefixCuts (2^48) 8779595777 10 Manual.Count131072.C066953.packed 64 cuts66953 = true := by
 decide +kernel
def pointBounds66953 : List (Nat × Nat × Nat) := [(8779636736,115267437985299,115267827170637)]
theorem point_links_checked66953 : (cuts66953.take 1).map (fun c => (8779595777-1+2*2^10*c.k,115267380982537+c.lower,115267770167842+c.upper)) = pointBounds66953 := by
 decide +kernel
def cuts66954 : List PrefixCut := [⟨64,184405674,184405779⟩]
theorem checked66954 : checkPrefixCuts (2^48) 8779726849 10 Manual.Count131072.C066954.packed 64 cuts66954 = true := by
 decide +kernel
def cuts66955 : List PrefixCut := [⟨26,74056449,74056491⟩,
⟨64,186550872,186550979⟩]
theorem checked66955 : checkPrefixCuts (2^48) 8779857921 10 Manual.Count131072.C066955.packed 64 cuts66955 = true := by
 decide +kernel
def pointBounds66955 : List (Nat × Nat × Nat) := [(8779911168,115267824366045,115268213551607)]
theorem point_links_checked66955 : (cuts66955.take 1).map (fun c => (8779857921-1+2*2^10*c.k,115267750309596+c.lower,115268139495116+c.upper)) = pointBounds66955 := by
 decide +kernel
def cuts66956 : List PrefixCut := [⟨64,183919292,183919406⟩]
theorem checked66956 : checkPrefixCuts (2^48) 8779988993 10 Manual.Count131072.C066956.packed 64 cuts66956 = true := by
 decide +kernel
def cuts66957 : List PrefixCut := [⟨32,91012907,91012958⟩,
⟨64,182954818,182954922⟩]
theorem checked66957 : checkPrefixCuts (2^48) 8780120065 10 Manual.Count131072.C066957.packed 64 cuts66957 = true := by
 decide +kernel
def pointBounds66957 : List (Nat × Nat × Nat) := [(8780185600,115268211792667,115268600978459)]
theorem point_links_checked66957 : (cuts66957.take 1).map (fun c => (8780120065-1+2*2^10*c.k,115268120779760+c.lower,115268509965501+c.upper)) = pointBounds66957 := by
 decide +kernel
def cuts66958 : List PrefixCut := [⟨64,184715232,184715339⟩]
theorem checked66958 : checkPrefixCuts (2^48) 8780251137 10 Manual.Count131072.C066958.packed 64 cuts66958 = true := by
 decide +kernel
def cuts66959 : List PrefixCut := [⟨38,107551590,107551655⟩,
⟨64,182789059,182789167⟩]
theorem checked66959 : checkPrefixCuts (2^48) 8780382209 10 Manual.Count131072.C066959.packed 64 cuts66959 = true := by
 decide +kernel
def pointBounds66959 : List (Nat × Nat × Nat) := [(8780460032,115268596001400,115268985187417)]
theorem point_links_checked66959 : (cuts66959.take 1).map (fun c => (8780382209-1+2*2^10*c.k,115268488449810+c.lower,115268877635762+c.upper)) = pointBounds66959 := by
 decide +kernel
def cuts66960 : List PrefixCut := [⟨64,182561960,182562065⟩]
theorem checked66960 : checkPrefixCuts (2^48) 8780513281 10 Manual.Count131072.C066960.packed 64 cuts66960 = true := by
 decide +kernel
def cuts66961 : List PrefixCut := [⟨44,128993858,128993934⟩,
⟨64,186021279,186021390⟩]
theorem checked66961 : checkPrefixCuts (2^48) 8780644353 10 Manual.Count131072.C066961.packed 64 cuts66961 = true := by
 decide +kernel
def pointBounds66961 : List (Nat × Nat × Nat) := [(8780734464,115268982794687,115269371980928)]
theorem point_links_checked66961 : (cuts66961.take 1).map (fun c => (8780644353-1+2*2^10*c.k,115268853800829+c.lower,115269242986994+c.upper)) = pointBounds66961 := by
 decide +kernel
def cuts66962 : List PrefixCut := [⟨64,184127222,184127325⟩]
theorem checked66962 : checkPrefixCuts (2^48) 8780775425 10 Manual.Count131072.C066962.packed 64 cuts66962 = true := by
 decide +kernel
def cuts66963 : List PrefixCut := [⟨50,144664876,144664960⟩,
⟨64,183996250,183996358⟩]
theorem checked66963 : checkPrefixCuts (2^48) 8780906497 10 Manual.Count131072.C066963.packed 64 cuts66963 = true := by
 decide +kernel
def pointBounds66963 : List (Nat × Nat × Nat) := [(8781008896,115269368614206,115269757800669)]
theorem point_links_checked66963 : (cuts66963.take 1).map (fun c => (8780906497-1+2*2^10*c.k,115269223949330+c.lower,115269613135709+c.upper)) = pointBounds66963 := by
 decide +kernel
def cuts66964 : List PrefixCut := [⟨64,185275689,185275800⟩]
theorem checked66964 : checkPrefixCuts (2^48) 8781037569 10 Manual.Count131072.C066964.packed 64 cuts66964 = true := by
 decide +kernel
def cuts66965 : List PrefixCut := [⟨56,160078511,160078606⟩,
⟨64,183349662,183349772⟩]
theorem checked66965 : checkPrefixCuts (2^48) 8781168641 10 Manual.Count131072.C066965.packed 64 cuts66965 = true := by
 decide +kernel
def pointBounds66965 : List (Nat × Nat × Nat) := [(8781283328,115269753299780,115270142486473)]
theorem point_links_checked66965 : (cuts66965.take 1).map (fun c => (8781168641-1+2*2^10*c.k,115269593221269+c.lower,115269982407867+c.upper)) = pointBounds66965 := by
 decide +kernel
def cuts66966 : List PrefixCut := [⟨64,183218706,183218813⟩]
theorem checked66966 : checkPrefixCuts (2^48) 8781299713 10 Manual.Count131072.C066966.packed 64 cuts66966 = true := by
 decide +kernel
def cuts66967 : List PrefixCut := [⟨62,172798727,172798823⟩,
⟨64,177991305,177991404⟩]
theorem checked66967 : checkPrefixCuts (2^48) 8781430785 10 Manual.Count131072.C066967.packed 64 cuts66967 = true := by
 decide +kernel
def pointBounds66967 : List (Nat × Nat × Nat) := [(8781557760,115270132588364,115270521775275)]
theorem point_links_checked66967 : (cuts66967.take 1).map (fun c => (8781430785-1+2*2^10*c.k,115269959789637+c.lower,115270348976452+c.upper)) = pointBounds66967 := by
 decide +kernel
def cuts66968 : List PrefixCut := [⟨64,184303053,184303158⟩]
theorem checked66968 : checkPrefixCuts (2^48) 8781561857 10 Manual.Count131072.C066968.packed 64 cuts66968 = true := by
 decide +kernel
def cuts66969 : List PrefixCut := [⟨64,184332339,184332448⟩]
theorem checked66969 : checkPrefixCuts (2^48) 8781692929 10 Manual.Count131072.C066969.packed 64 cuts66969 = true := by
 decide +kernel
def cuts66970 : List PrefixCut := [⟨4,12147697,12147704⟩,
⟨64,183848822,183848927⟩]
theorem checked66970 : checkPrefixCuts (2^48) 8781824001 10 Manual.Count131072.C066970.packed 64 cuts66970 = true := by
 decide +kernel
def pointBounds66970 : List (Nat × Nat × Nat) := [(8781832192,115270518564031,115270907751166)]
theorem point_links_checked66970 : (cuts66970.take 1).map (fun c => (8781824001-1+2*2^10*c.k,115270506416334+c.lower,115270895603462+c.upper)) = pointBounds66970 := by
 decide +kernel
def cuts66971 : List PrefixCut := [⟨64,183076840,183076950⟩]
theorem checked66971 : checkPrefixCuts (2^48) 8781955073 10 Manual.Count131072.C066971.packed 64 cuts66971 = true := by
 decide +kernel
def cuts66972 : List PrefixCut := [⟨10,29294607,29294624⟩,
⟨64,183330530,183330637⟩]
theorem checked66972 : checkPrefixCuts (2^48) 8782086145 10 Manual.Count131072.C066972.packed 64 cuts66972 = true := by
 decide +kernel
def pointBounds66972 : List (Nat × Nat × Nat) := [(8782106624,115270902636603,115271291823963)]
theorem point_links_checked66972 : (cuts66972.take 1).map (fun c => (8782086145-1+2*2^10*c.k,115270873341996+c.lower,115271262529339+c.upper)) = pointBounds66972 := by
 decide +kernel
def cuts66973 : List PrefixCut := [⟨64,182494472,182494581⟩]
theorem checked66973 : checkPrefixCuts (2^48) 8782217217 10 Manual.Count131072.C066973.packed 64 cuts66973 = true := by
 decide +kernel
def cuts66974 : List PrefixCut := [⟨17,48555762,48555790⟩,
⟨64,181337941,181338050⟩]
theorem checked66974 : checkPrefixCuts (2^48) 8782348289 10 Manual.Count131072.C066974.packed 64 cuts66974 = true := by
 decide +kernel
def pointBounds66974 : List (Nat × Nat × Nat) := [(8782383104,115271287722760,115271676910347)]
theorem point_links_checked66974 : (cuts66974.take 1).map (fun c => (8782348289-1+2*2^10*c.k,115271239166998+c.lower,115271628354557+c.upper)) = pointBounds66974 := by
 decide +kernel
def cuts66975 : List PrefixCut := [⟨64,185501661,185501772⟩]
theorem checked66975 : checkPrefixCuts (2^48) 8782479361 10 Manual.Count131072.C066975.packed 64 cuts66975 = true := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S7.B000217
