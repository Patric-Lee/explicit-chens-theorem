import PlattAssemblyKernel
import PlattCertificates.Count131072.C070000
import PlattCertificates.Count131072.C070001
import PlattCertificates.Count131072.C070002
import PlattCertificates.Count131072.C070003
import PlattCertificates.Count131072.C070004
import PlattCertificates.Count131072.C070005
import PlattCertificates.Count131072.C070006
import PlattCertificates.Count131072.C070007
import PlattCertificates.Count131072.C070008
import PlattCertificates.Count131072.C070009
import PlattCertificates.Count131072.C070010
import PlattCertificates.Count131072.C070011
import PlattCertificates.Count131072.C070012
import PlattCertificates.Count131072.C070013
import PlattCertificates.Count131072.C070014
import PlattCertificates.Count131072.C070015
import PlattCertificates.Count131072.C070016
import PlattCertificates.Count131072.C070017
import PlattCertificates.Count131072.C070018
import PlattCertificates.Count131072.C070019
import PlattCertificates.Count131072.C070020
import PlattCertificates.Count131072.C070021
import PlattCertificates.Count131072.C070022
import PlattCertificates.Count131072.C070023
import PlattCertificates.Count131072.C070024
import PlattCertificates.Count131072.C070025
import PlattCertificates.Count131072.C070026
import PlattCertificates.Count131072.C070027
import PlattCertificates.Count131072.C070028
import PlattCertificates.Count131072.C070029
import PlattCertificates.Count131072.C070030
import PlattCertificates.Count131072.C070031
namespace ChenEffective.PlattWindow.Assembly.Prefix.S8.B000000
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts70000 : List PrefixCut := [⟨64,175127620,175127725⟩]
theorem checked70000 : checkPrefixCuts (2^48) 9178972161 10 Manual.Count131072.C070000.packed 64 cuts70000 = true := by
 decide +kernel
def cuts70001 : List PrefixCut := [⟨48,130293817,130293894⟩,
⟨64,175370434,175370536⟩]
theorem checked70001 : checkPrefixCuts (2^48) 9179103233 10 Manual.Count131072.C070001.packed 64 cuts70001 = true := by
 decide +kernel
def pointBounds70001 : List (Nat × Nat × Nat) := [(9179201536,115814035500148,115814425005521)]
theorem point_links_checked70001 : (cuts70001.take 1).map (fun c => (9179103233-1+2*2^10*c.k,115813905206331+c.lower,115814294711627+c.upper)) = pointBounds70001 := by
 decide +kernel
def cuts70002 : List PrefixCut := [⟨64,174846658,174846757⟩]
theorem checked70002 : checkPrefixCuts (2^48) 9179234305 10 Manual.Count131072.C070002.packed 64 cuts70002 = true := by
 decide +kernel
def cuts70003 : List PrefixCut := [⟨61,168435504,168435603⟩,
⟨64,176959942,176960046⟩]
theorem checked70003 : checkPrefixCuts (2^48) 9179365377 10 Manual.Count131072.C070003.packed 64 cuts70003 = true := by
 decide +kernel
def pointBounds70003 : List (Nat × Nat × Nat) := [(9179490304,115814423858927,115814813364523)]
theorem point_links_checked70003 : (cuts70003.take 1).map (fun c => (9179365377-1+2*2^10*c.k,115814255423423+c.lower,115814644928920+c.upper)) = pointBounds70003 := by
 decide +kernel
def cuts70004 : List PrefixCut := [⟨64,175577575,175577681⟩]
theorem checked70004 : checkPrefixCuts (2^48) 9179496449 10 Manual.Count131072.C070004.packed 64 cuts70004 = true := by
 decide +kernel
def cuts70005 : List PrefixCut := [⟨64,174103255,174103356⟩]
theorem checked70005 : checkPrefixCuts (2^48) 9179627521 10 Manual.Count131072.C070005.packed 64 cuts70005 = true := by
 decide +kernel
def cuts70006 : List PrefixCut := [⟨10,27657598,27657614⟩,
⟨64,177994876,177994984⟩]
theorem checked70006 : checkPrefixCuts (2^48) 9179758593 10 Manual.Count131072.C070006.packed 64 cuts70006 = true := by
 decide +kernel
def pointBounds70006 : List (Nat × Nat × Nat) := [(9179779072,115814809721793,115815199227617)]
theorem point_links_checked70006 : (cuts70006.take 1).map (fun c => (9179758593-1+2*2^10*c.k,115814782064195+c.lower,115815171570003+c.upper)) = pointBounds70006 := by
 decide +kernel
def cuts70007 : List PrefixCut := [⟨64,175079457,175079559⟩]
theorem checked70007 : checkPrefixCuts (2^48) 9179889665 10 Manual.Count131072.C070007.packed 64 cuts70007 = true := by
 decide +kernel
def cuts70008 : List PrefixCut := [⟨23,62825629,62825669⟩,
⟨64,174923660,174923765⟩]
theorem checked70008 : checkPrefixCuts (2^48) 9180020737 10 Manual.Count131072.C070008.packed 64 cuts70008 = true := by
 decide +kernel
def pointBounds70008 : List (Nat × Nat × Nat) := [(9180067840,115815197964157,115815587470215)]
theorem point_links_checked70008 : (cuts70008.take 1).map (fun c => (9180020737-1+2*2^10*c.k,115815135138528+c.lower,115815524644546+c.upper)) = pointBounds70008 := by
 decide +kernel
def cuts70009 : List PrefixCut := [⟨64,176300911,176301012⟩]
theorem checked70009 : checkPrefixCuts (2^48) 9180151809 10 Manual.Count131072.C070009.packed 64 cuts70009 = true := by
 decide +kernel
def cuts70010 : List PrefixCut := [⟨36,97286354,97286413⟩,
⟨64,173324310,173324411⟩]
theorem checked70010 : checkPrefixCuts (2^48) 9180282881 10 Manual.Count131072.C070010.packed 64 cuts70010 = true := by
 decide +kernel
def pointBounds70010 : List (Nat × Nat × Nat) := [(9180356608,115815583649453,115815973155736)]
theorem point_links_checked70010 : (cuts70010.take 1).map (fun c => (9180282881-1+2*2^10*c.k,115815486363099+c.lower,115815875869323+c.upper)) = pointBounds70010 := by
 decide +kernel
def cuts70011 : List PrefixCut := [⟨64,176510488,176510594⟩]
theorem checked70011 : checkPrefixCuts (2^48) 9180413953 10 Manual.Count131072.C070011.packed 64 cuts70011 = true := by
 decide +kernel
def cuts70012 : List PrefixCut := [⟨49,134381750,134381828⟩,
⟨64,175036309,175036409⟩]
theorem checked70012 : checkPrefixCuts (2^48) 9180545025 10 Manual.Count131072.C070012.packed 64 cuts70012 = true := by
 decide +kernel
def pointBounds70012 : List (Nat × Nat × Nat) := [(9180645376,115815970579647,115816360086156)]
theorem point_links_checked70012 : (cuts70012.take 1).map (fun c => (9180545025-1+2*2^10*c.k,115815836197897+c.lower,115816225704328+c.upper)) = pointBounds70012 := by
 decide +kernel
def cuts70013 : List PrefixCut := [⟨64,175217771,175217874⟩]
theorem checked70013 : checkPrefixCuts (2^48) 9180676097 10 Manual.Count131072.C070013.packed 64 cuts70013 = true := by
 decide +kernel
def cuts70014 : List PrefixCut := [⟨62,168071790,168071892⟩,
⟨64,173743636,173743741⟩]
theorem checked70014 : checkPrefixCuts (2^48) 9180807169 10 Manual.Count131072.C070014.packed 64 cuts70014 = true := by
 decide +kernel
def pointBounds70014 : List (Nat × Nat × Nat) := [(9180934144,115816354523767,115816744030503)]
theorem point_links_checked70014 : (cuts70014.take 1).map (fun c => (9180807169-1+2*2^10*c.k,115816186451977+c.lower,115816575958611+c.upper)) = pointBounds70014 := by
 decide +kernel
def cuts70015 : List PrefixCut := [⟨64,173925111,173925212⟩]
theorem checked70015 : checkPrefixCuts (2^48) 9180938241 10 Manual.Count131072.C070015.packed 64 cuts70015 = true := by
 decide +kernel
def cuts70016 : List PrefixCut := [⟨64,174842374,174842478⟩]
theorem checked70016 : checkPrefixCuts (2^48) 9181069313 10 Manual.Count131072.C070016.packed 64 cuts70016 = true := by
 decide +kernel
def cuts70017 : List PrefixCut := [⟨11,29247452,29247469⟩,
⟨64,174625253,174625359⟩]
theorem checked70017 : checkPrefixCuts (2^48) 9181200385 10 Manual.Count131072.C070017.packed 64 cuts70017 = true := by
 decide +kernel
def pointBounds70017 : List (Nat × Nat × Nat) := [(9181222912,115816738210550,115817127717511)]
theorem point_links_checked70017 : (cuts70017.take 1).map (fun c => (9181200385-1+2*2^10*c.k,115816708963098+c.lower,115817098470042+c.upper)) = pointBounds70017 := by
 decide +kernel
def cuts70018 : List PrefixCut := [⟨64,177780460,177780564⟩]
theorem checked70018 : checkPrefixCuts (2^48) 9181331457 10 Manual.Count131072.C070018.packed 64 cuts70018 = true := by
 decide +kernel
def cuts70019 : List PrefixCut := [⟨24,65605525,65605569⟩,
⟨64,174160431,174160539⟩]
theorem checked70019 : checkPrefixCuts (2^48) 9181462529 10 Manual.Count131072.C070019.packed 64 cuts70019 = true := by
 decide +kernel
def pointBounds70019 : List (Nat × Nat × Nat) := [(9181511680,115817126974336,115817516481534)]
theorem point_links_checked70019 : (cuts70019.take 1).map (fun c => (9181462529-1+2*2^10*c.k,115817061368811+c.lower,115817450875965+c.upper)) = pointBounds70019 := by
 decide +kernel
def cuts70020 : List PrefixCut := [⟨64,173146299,173146396⟩]
theorem checked70020 : checkPrefixCuts (2^48) 9181593601 10 Manual.Count131072.C070020.packed 64 cuts70020 = true := by
 decide +kernel
def cuts70021 : List PrefixCut := [⟨37,100551243,100551302⟩,
⟨64,171396445,171396546⟩]
theorem checked70021 : checkPrefixCuts (2^48) 9181724673 10 Manual.Count131072.C070021.packed 64 cuts70021 = true := by
 decide +kernel
def pointBounds70021 : List (Nat × Nat × Nat) := [(9181800448,115817509226784,115817898734202)]
theorem point_links_checked70021 : (cuts70021.take 1).map (fun c => (9181724673-1+2*2^10*c.k,115817408675541+c.lower,115817798182900+c.upper)) = pointBounds70021 := by
 decide +kernel
def cuts70022 : List PrefixCut := [⟨64,177279831,177279936⟩]
theorem checked70022 : checkPrefixCuts (2^48) 9181855745 10 Manual.Count131072.C070022.packed 64 cuts70022 = true := by
 decide +kernel
def cuts70023 : List PrefixCut := [⟨50,138468402,138468484⟩,
⟨64,176725501,176725609⟩]
theorem checked70023 : checkPrefixCuts (2^48) 9181986817 10 Manual.Count131072.C070023.packed 64 cuts70023 = true := by
 decide +kernel
def pointBounds70023 : List (Nat × Nat × Nat) := [(9182089216,115817895820219,115818285327866)]
theorem point_links_checked70023 : (cuts70023.take 1).map (fun c => (9181986817-1+2*2^10*c.k,115817757351817+c.lower,115818146859382+c.upper)) = pointBounds70023 := by
 decide +kernel
def cuts70024 : List PrefixCut := [⟨64,176814932,176815035⟩]
theorem checked70024 : checkPrefixCuts (2^48) 9182117889 10 Manual.Count131072.C070024.packed 64 cuts70024 = true := by
 decide +kernel
def cuts70025 : List PrefixCut := [⟨63,173440499,173440593⟩,
⟨64,176076727,176076822⟩]
theorem checked70025 : checkPrefixCuts (2^48) 9182248961 10 Manual.Count131072.C070025.packed 64 cuts70025 = true := by
 decide +kernel
def pointBounds70025 : List (Nat × Nat × Nat) := [(9182377984,115818284332749,115818673840619)]
theorem point_links_checked70025 : (cuts70025.take 1).map (fun c => (9182248961-1+2*2^10*c.k,115818110892250+c.lower,115818500400026+c.upper)) = pointBounds70025 := by
 decide +kernel
def cuts70026 : List PrefixCut := [⟨64,175614397,175614503⟩]
theorem checked70026 : checkPrefixCuts (2^48) 9182380033 10 Manual.Count131072.C070026.packed 64 cuts70026 = true := by
 decide +kernel
def cuts70027 : List PrefixCut := [⟨64,174845565,174845672⟩]
theorem checked70027 : checkPrefixCuts (2^48) 9182511105 10 Manual.Count131072.C070027.packed 64 cuts70027 = true := by
 decide +kernel
def cuts70028 : List PrefixCut := [⟨12,34637765,34637784⟩,
⟨64,173187825,173187934⟩]
theorem checked70028 : checkPrefixCuts (2^48) 9182642177 10 Manual.Count131072.C070028.packed 64 cuts70028 = true := by
 decide +kernel
def pointBounds70028 : List (Nat × Nat × Nat) := [(9182666752,115818672066704,115819061574807)]
theorem point_links_checked70028 : (cuts70028.take 1).map (fun c => (9182642177-1+2*2^10*c.k,115818637428939+c.lower,115819026937023+c.upper)) = pointBounds70028 := by
 decide +kernel
def cuts70029 : List PrefixCut := [⟨64,174993845,174993953⟩]
theorem checked70029 : checkPrefixCuts (2^48) 9182773249 10 Manual.Count131072.C070029.packed 64 cuts70029 = true := by
 decide +kernel
def cuts70030 : List PrefixCut := [⟨25,68047381,68047414⟩,
⟨64,172631156,172631255⟩]
theorem checked70030 : checkPrefixCuts (2^48) 9182904321 10 Manual.Count131072.C070030.packed 64 cuts70030 = true := by
 decide +kernel
def pointBounds70030 : List (Nat × Nat × Nat) := [(9182955520,115819053657990,115819443166324)]
theorem point_links_checked70030 : (cuts70030.take 1).map (fun c => (9182904321-1+2*2^10*c.k,115818985610609+c.lower,115819375118910+c.upper)) = pointBounds70030 := by
 decide +kernel
def cuts70031 : List PrefixCut := [⟨64,176000324,176000433⟩]
theorem checked70031 : checkPrefixCuts (2^48) 9183035393 10 Manual.Count131072.C070031.packed 64 cuts70031 = true := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S8.B000000
