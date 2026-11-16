import PlattAssemblyKernel
import PlattCertificates.Count131072.C067968
import PlattCertificates.Count131072.C067969
import PlattCertificates.Count131072.C067970
import PlattCertificates.Count131072.C067971
import PlattCertificates.Count131072.C067972
import PlattCertificates.Count131072.C067973
import PlattCertificates.Count131072.C067974
import PlattCertificates.Count131072.C067975
import PlattCertificates.Count131072.C067976
import PlattCertificates.Count131072.C067977
import PlattCertificates.Count131072.C067978
import PlattCertificates.Count131072.C067979
import PlattCertificates.Count131072.C067980
import PlattCertificates.Count131072.C067981
import PlattCertificates.Count131072.C067982
import PlattCertificates.Count131072.C067983
import PlattCertificates.Count131072.C067984
import PlattCertificates.Count131072.C067985
import PlattCertificates.Count131072.C067986
import PlattCertificates.Count131072.C067987
import PlattCertificates.Count131072.C067988
import PlattCertificates.Count131072.C067989
import PlattCertificates.Count131072.C067990
import PlattCertificates.Count131072.C067991
import PlattCertificates.Count131072.C067992
import PlattCertificates.Count131072.C067993
import PlattCertificates.Count131072.C067994
import PlattCertificates.Count131072.C067995
import PlattCertificates.Count131072.C067996
import PlattCertificates.Count131072.C067997
import PlattCertificates.Count131072.C067998
import PlattCertificates.Count131072.C067999
namespace ChenEffective.PlattWindow.Assembly.Prefix.S7.B000249
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts67968 : List PrefixCut := [⟨64,180897862,180897970⟩]
theorem checked67968 : checkPrefixCuts (2^48) 8912633857 10 Manual.Count131072.C067968.packed 64 cuts67968 = true := by
 decide +kernel
def cuts67969 : List PrefixCut := [⟨21,58993349,58993385⟩,
⟨64,181874197,181874305⟩]
theorem checked67969 : checkPrefixCuts (2^48) 8912764929 10 Manual.Count131072.C067969.packed 64 cuts67969 = true := by
 decide +kernel
def pointBounds67969 : List (Nat × Nat × Nat) := [(8912807936,115452447901354,115452837194708)]
theorem point_links_checked67969 : (cuts67969.take 1).map (fun c => (8912764929-1+2*2^10*c.k,115452388908005+c.lower,115452778201323+c.upper)) = pointBounds67969 := by
 decide +kernel
def cuts67970 : List PrefixCut := [⟨64,181366230,181366338⟩]
theorem checked67970 : checkPrefixCuts (2^48) 8912896001 10 Manual.Count131072.C067970.packed 64 cuts67970 = true := by
 decide +kernel
def cuts67971 : List PrefixCut := [⟨29,81697628,81697675⟩,
⟨64,183732061,183732165⟩]
theorem checked67971 : checkPrefixCuts (2^48) 8913027073 10 Manual.Count131072.C067971.packed 64 cuts67971 = true := by
 decide +kernel
def pointBounds67971 : List (Nat × Nat × Nat) := [(8913086464,115452833846060,115453223139641)]
theorem point_links_checked67971 : (cuts67971.take 1).map (fun c => (8913027073-1+2*2^10*c.k,115452752148432+c.lower,115453141441966+c.upper)) = pointBounds67971 := by
 decide +kernel
def cuts67972 : List PrefixCut := [⟨64,179087176,179087282⟩]
theorem checked67972 : checkPrefixCuts (2^48) 8913158145 10 Manual.Count131072.C067972.packed 64 cuts67972 = true := by
 decide +kernel
def cuts67973 : List PrefixCut := [⟨38,106137357,106137419⟩,
⟨64,179589807,179589913⟩]
theorem checked67973 : checkPrefixCuts (2^48) 8913289217 10 Manual.Count131072.C067973.packed 64 cuts67973 = true := by
 decide +kernel
def pointBounds67973 : List (Nat × Nat × Nat) := [(8913367040,115453221105026,115453610398832)]
theorem point_links_checked67973 : (cuts67973.take 1).map (fun c => (8913289217-1+2*2^10*c.k,115453114967669+c.lower,115453504261413+c.upper)) = pointBounds67973 := by
 decide +kernel
def cuts67974 : List PrefixCut := [⟨64,180692412,180692518⟩]
theorem checked67974 : checkPrefixCuts (2^48) 8913420289 10 Manual.Count131072.C067974.packed 64 cuts67974 = true := by
 decide +kernel
def cuts67975 : List PrefixCut := [⟨47,133165030,133165107⟩,
⟨64,181352917,181353021⟩]
theorem checked67975 : checkPrefixCuts (2^48) 8913551361 10 Manual.Count131072.C067975.packed 64 cuts67975 = true := by
 decide +kernel
def pointBounds67975 : List (Nat × Nat × Nat) := [(8913647616,115453608414918,115453997708951)]
theorem point_links_checked67975 : (cuts67975.take 1).map (fun c => (8913551361-1+2*2^10*c.k,115453475249888+c.lower,115453864543844+c.upper)) = pointBounds67975 := by
 decide +kernel
def cuts67976 : List PrefixCut := [⟨64,181792322,181792429⟩]
theorem checked67976 : checkPrefixCuts (2^48) 8913682433 10 Manual.Count131072.C067976.packed 64 cuts67976 = true := by
 decide +kernel
def cuts67977 : List PrefixCut := [⟨56,157791162,157791250⟩,
⟨64,180905488,180905587⟩]
theorem checked67977 : checkPrefixCuts (2^48) 8913813505 10 Manual.Count131072.C067977.packed 64 cuts67977 = true := by
 decide +kernel
def pointBounds67977 : List (Nat × Nat × Nat) := [(8913928192,115453996186289,115454385480544)]
theorem point_links_checked67977 : (cuts67977.take 1).map (fun c => (8913813505-1+2*2^10*c.k,115453838395127+c.lower,115454227689294+c.upper)) = pointBounds67977 := by
 decide +kernel
def cuts67978 : List PrefixCut := [⟨64,179955539,179955647⟩]
theorem checked67978 : checkPrefixCuts (2^48) 8913944577 10 Manual.Count131072.C067978.packed 64 cuts67978 = true := by
 decide +kernel
def cuts67979 : List PrefixCut := [⟨64,179163488,179163592⟩]
theorem checked67979 : checkPrefixCuts (2^48) 8914075649 10 Manual.Count131072.C067979.packed 64 cuts67979 = true := by
 decide +kernel
def cuts67980 : List PrefixCut := [⟨1,2873415,2873416⟩,
⟨64,179255579,179255686⟩]
theorem checked67980 : checkPrefixCuts (2^48) 8914206721 10 Manual.Count131072.C067980.packed 64 cuts67980 = true := by
 decide +kernel
def pointBounds67980 : List (Nat × Nat × Nat) := [(8914208768,115454381293057,115454770587536)]
theorem point_links_checked67980 : (cuts67980.take 1).map (fun c => (8914206721-1+2*2^10*c.k,115454378419642+c.lower,115454767714120+c.upper)) = pointBounds67980 := by
 decide +kernel
def cuts67981 : List PrefixCut := [⟨64,180831696,180831805⟩]
theorem checked67981 : checkPrefixCuts (2^48) 8914337793 10 Manual.Count131072.C067981.packed 64 cuts67981 = true := by
 decide +kernel
def cuts67982 : List PrefixCut := [⟨10,26996646,26996660⟩,
⟨64,181334227,181334332⟩]
theorem checked67982 : checkPrefixCuts (2^48) 8914468865 10 Manual.Count131072.C067982.packed 64 cuts67982 = true := by
 decide +kernel
def pointBounds67982 : List (Nat × Nat × Nat) := [(8914489344,115454765503563,115455154798271)]
theorem point_links_checked67982 : (cuts67982.take 1).map (fun c => (8914468865-1+2*2^10*c.k,115454738506917+c.lower,115455127801611+c.upper)) = pointBounds67982 := by
 decide +kernel
def cuts67983 : List PrefixCut := [⟨64,181268421,181268523⟩]
theorem checked67983 : checkPrefixCuts (2^48) 8914599937 10 Manual.Count131072.C067983.packed 64 cuts67983 = true := by
 decide +kernel
def cuts67984 : List PrefixCut := [⟨19,54181094,54181124⟩,
⟨64,182339264,182339373⟩]
theorem checked67984 : checkPrefixCuts (2^48) 8914731009 10 Manual.Count131072.C067984.packed 64 cuts67984 = true := by
 decide +kernel
def pointBounds67984 : List (Nat × Nat × Nat) := [(8914769920,115455155290659,115455544585590)]
theorem point_links_checked67984 : (cuts67984.take 1).map (fun c => (8914731009-1+2*2^10*c.k,115455101109565+c.lower,115455490404466+c.upper)) = pointBounds67984 := by
 decide +kernel
def cuts67985 : List PrefixCut := [⟨64,181294674,181294777⟩]
theorem checked67985 : checkPrefixCuts (2^48) 8914862081 10 Manual.Count131072.C067985.packed 64 cuts67985 = true := by
 decide +kernel
def cuts67986 : List PrefixCut := [⟨28,79911525,79911568⟩,
⟨64,182144480,182144586⟩]
theorem checked67986 : checkPrefixCuts (2^48) 8914993153 10 Manual.Count131072.C067986.packed 64 cuts67986 = true := by
 decide +kernel
def pointBounds67986 : List (Nat × Nat × Nat) := [(8915050496,115455544655028,115455933950184)]
theorem point_links_checked67986 : (cuts67986.take 1).map (fun c => (8914993153-1+2*2^10*c.k,115455464743503+c.lower,115455854038616+c.upper)) = pointBounds67986 := by
 decide +kernel
def cuts67987 : List PrefixCut := [⟨64,180878894,180878997⟩]
theorem checked67987 : checkPrefixCuts (2^48) 8915124225 10 Manual.Count131072.C067987.packed 64 cuts67987 = true := by
 decide +kernel
def cuts67988 : List PrefixCut := [⟨37,105514096,105514160⟩,
⟨64,183117848,183117956⟩]
theorem checked67988 : checkPrefixCuts (2^48) 8915255297 10 Manual.Count131072.C067988.packed 64 cuts67988 = true := by
 decide +kernel
def pointBounds67988 : List (Nat × Nat × Nat) := [(8915331072,115455933280973,115456322576359)]
theorem point_links_checked67988 : (cuts67988.take 1).map (fun c => (8915255297-1+2*2^10*c.k,115455827766877+c.lower,115456217062199+c.upper)) = pointBounds67988 := by
 decide +kernel
def cuts67989 : List PrefixCut := [⟨64,178568845,178568952⟩]
theorem checked67989 : checkPrefixCuts (2^48) 8915386369 10 Manual.Count131072.C067989.packed 64 cuts67989 = true := by
 decide +kernel
def cuts67990 : List PrefixCut := [⟨46,127326573,127326650⟩,
⟨64,177019246,177019351⟩]
theorem checked67990 : checkPrefixCuts (2^48) 8915517441 10 Manual.Count131072.C067990.packed 64 cuts67990 = true := by
 decide +kernel
def pointBounds67990 : List (Nat × Nat × Nat) := [(8915611648,115456316780143,115456706075757)]
theorem point_links_checked67990 : (cuts67990.take 1).map (fun c => (8915517441-1+2*2^10*c.k,115456189453570+c.lower,115456578749107+c.upper)) = pointBounds67990 := by
 decide +kernel
def cuts67991 : List PrefixCut := [⟨64,180805109,180805216⟩]
theorem checked67991 : checkPrefixCuts (2^48) 8915648513 10 Manual.Count131072.C067991.packed 64 cuts67991 = true := by
 decide +kernel
def cuts67992 : List PrefixCut := [⟨55,156588291,156588378⟩,
⟨64,180802471,180802573⟩]
theorem checked67992 : checkPrefixCuts (2^48) 8915779585 10 Manual.Count131072.C067992.packed 64 cuts67992 = true := by
 decide +kernel
def pointBounds67992 : List (Nat × Nat × Nat) := [(8915892224,115456703866216,115457093162052)]
theorem point_links_checked67992 : (cuts67992.take 1).map (fun c => (8915779585-1+2*2^10*c.k,115456547277925+c.lower,115456936573674+c.upper)) = pointBounds67992 := by
 decide +kernel
def cuts67993 : List PrefixCut := [⟨64,183167525,183167637⟩]
theorem checked67993 : checkPrefixCuts (2^48) 8915910657 10 Manual.Count131072.C067993.packed 64 cuts67993 = true := by
 decide +kernel
def cuts67994 : List PrefixCut := [⟨64,181902065,181902165⟩]
theorem checked67994 : checkPrefixCuts (2^48) 8916041729 10 Manual.Count131072.C067994.packed 64 cuts67994 = true := by
 decide +kernel
def pointBounds67994 : List (Nat × Nat × Nat) := [(8916172800,115457093149986,115457482446049)]
theorem point_links_checked67994 : (cuts67994.take 1).map (fun c => (8916041729-1+2*2^10*c.k,115456911247921+c.lower,115457300543884+c.upper)) = pointBounds67994 := by
 decide +kernel
def cuts67995 : List PrefixCut := [⟨64,181867819,181867922⟩]
theorem checked67995 : checkPrefixCuts (2^48) 8916172801 10 Manual.Count131072.C067995.packed 64 cuts67995 = true := by
 decide +kernel
def cuts67996 : List PrefixCut := [⟨64,178834590,178834700⟩]
theorem checked67996 : checkPrefixCuts (2^48) 8916303873 10 Manual.Count131072.C067996.packed 64 cuts67996 = true := by
 decide +kernel
def cuts67997 : List PrefixCut := [⟨9,26233065,26233078⟩,
⟨64,179084520,179084620⟩]
theorem checked67997 : checkPrefixCuts (2^48) 8916434945 10 Manual.Count131072.C067997.packed 64 cuts67997 = true := by
 decide +kernel
def pointBounds67997 : List (Nat × Nat × Nat) := [(8916453376,115457480085460,115457869381749)]
theorem point_links_checked67997 : (cuts67997.take 1).map (fun c => (8916434945-1+2*2^10*c.k,115457453852395+c.lower,115457843148671+c.upper)) = pointBounds67997 := by
 decide +kernel
def cuts67998 : List PrefixCut := [⟨64,181828238,181828341⟩]
theorem checked67998 : checkPrefixCuts (2^48) 8916566017 10 Manual.Count131072.C067998.packed 64 cuts67998 = true := by
 decide +kernel
def cuts67999 : List PrefixCut := [⟨18,50759908,50759937⟩,
⟨64,182109668,182109775⟩]
theorem checked67999 : checkPrefixCuts (2^48) 8916697089 10 Manual.Count131072.C067999.packed 64 cuts67999 = true := by
 decide +kernel
def pointBounds67999 : List (Nat × Nat × Nat) := [(8916733952,115457865525061,115458254821569)]
theorem point_links_checked67999 : (cuts67999.take 1).map (fun c => (8916697089-1+2*2^10*c.k,115457814765153+c.lower,115458204061632+c.upper)) = pointBounds67999 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S7.B000249
