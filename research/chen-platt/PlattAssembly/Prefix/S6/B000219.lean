import PlattAssemblyKernel
import PlattCertificates.Count131072.C057008
import PlattCertificates.Count131072.C057009
import PlattCertificates.Count131072.C057010
import PlattCertificates.Count131072.C057011
import PlattCertificates.Count131072.C057012
import PlattCertificates.Count131072.C057013
import PlattCertificates.Count131072.C057014
import PlattCertificates.Count131072.C057015
import PlattCertificates.Count131072.C057016
import PlattCertificates.Count131072.C057017
import PlattCertificates.Count131072.C057018
import PlattCertificates.Count131072.C057019
import PlattCertificates.Count131072.C057020
import PlattCertificates.Count131072.C057021
import PlattCertificates.Count131072.C057022
import PlattCertificates.Count131072.C057023
import PlattCertificates.Count131072.C057024
import PlattCertificates.Count131072.C057025
import PlattCertificates.Count131072.C057026
import PlattCertificates.Count131072.C057027
import PlattCertificates.Count131072.C057028
import PlattCertificates.Count131072.C057029
import PlattCertificates.Count131072.C057030
import PlattCertificates.Count131072.C057031
import PlattCertificates.Count131072.C057032
import PlattCertificates.Count131072.C057033
import PlattCertificates.Count131072.C057034
import PlattCertificates.Count131072.C057035
import PlattCertificates.Count131072.C057036
import PlattCertificates.Count131072.C057037
import PlattCertificates.Count131072.C057038
import PlattCertificates.Count131072.C057039
namespace ChenEffective.PlattWindow.Assembly.Prefix.S6.B000219
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts57008 : List PrefixCut := [⟨64,216034050,216034173⟩]
theorem checked57008 : checkPrefixCuts (2^48) 7476084737 10 Manual.Count131072.C057008.packed 64 cuts57008 = true := by
 decide +kernel
def cuts57009 : List PrefixCut := [⟨5,16189222,16189231⟩,
⟨64,218289161,218289288⟩]
theorem checked57009 : checkPrefixCuts (2^48) 7476215809 10 Manual.Count131072.C057009.packed 64 cuts57009 = true := by
 decide +kernel
def pointBounds57009 : List (Nat × Nat × Nat) := [(7476226048,113284795148403,113285183195332)]
theorem point_links_checked57009 : (cuts57009.take 1).map (fun c => (7476215809-1+2*2^10*c.k,113284778959181+c.lower,113285167006101+c.upper)) = pointBounds57009 := by
 decide +kernel
def cuts57010 : List PrefixCut := [⟨56,190237520,190237628⟩,
⟨64,216139414,216139537⟩]
theorem checked57010 : checkPrefixCuts (2^48) 7476346881 10 Manual.Count131072.C057010.packed 64 cuts57010 = true := by
 decide +kernel
def pointBounds57010 : List (Nat × Nat × Nat) := [(7476461568,113285187485862,113285575533017)]
theorem point_links_checked57010 : (cuts57010.take 1).map (fun c => (7476346881-1+2*2^10*c.k,113284997248342+c.lower,113285385295389+c.upper)) = pointBounds57010 := by
 decide +kernel
def cuts57011 : List PrefixCut := [⟨64,217942727,217942848⟩]
theorem checked57011 : checkPrefixCuts (2^48) 7476477953 10 Manual.Count131072.C057011.packed 64 cuts57011 = true := by
 decide +kernel
def cuts57012 : List PrefixCut := [⟨43,145995772,145995855⟩,
⟨64,216018910,216019035⟩]
theorem checked57012 : checkPrefixCuts (2^48) 7476609025 10 Manual.Count131072.C057012.packed 64 cuts57012 = true := by
 decide +kernel
def pointBounds57012 : List (Nat × Nat × Nat) := [(7476697088,113285577326255,113285965373629)]
theorem point_links_checked57012 : (cuts57012.take 1).map (fun c => (7476609025-1+2*2^10*c.k,113285431330483+c.lower,113285819377774+c.upper)) = pointBounds57012 := by
 decide +kernel
def cuts57013 : List PrefixCut := [⟨64,221059708,221059833⟩]
theorem checked57013 : checkPrefixCuts (2^48) 7476740097 10 Manual.Count131072.C057013.packed 64 cuts57013 = true := by
 decide +kernel
def cuts57014 : List PrefixCut := [⟨30,102396915,102396975⟩,
⟨64,220039400,220039525⟩]
theorem checked57014 : checkPrefixCuts (2^48) 7476871169 10 Manual.Count131072.C057014.packed 64 cuts57014 = true := by
 decide +kernel
def pointBounds57014 : List (Nat × Nat × Nat) := [(7476932608,113285970806016,113286358853617)]
theorem point_links_checked57014 : (cuts57014.take 1).map (fun c => (7476871169-1+2*2^10*c.k,113285868409101+c.lower,113286256456642+c.upper)) = pointBounds57014 := by
 decide +kernel
def cuts57015 : List PrefixCut := [⟨64,216911019,216911143⟩]
theorem checked57015 : checkPrefixCuts (2^48) 7477002241 10 Manual.Count131072.C057015.packed 64 cuts57015 = true := by
 decide +kernel
def cuts57016 : List PrefixCut := [⟨17,57069324,57069355⟩,
⟨64,217622455,217622575⟩]
theorem checked57016 : checkPrefixCuts (2^48) 7477133313 10 Manual.Count131072.C057016.packed 64 cuts57016 = true := by
 decide +kernel
def pointBounds57016 : List (Nat × Nat × Nat) := [(7477168128,113286362428844,113286750476665)]
theorem point_links_checked57016 : (cuts57016.take 1).map (fun c => (7477133313-1+2*2^10*c.k,113286305359520+c.lower,113286693407310+c.upper)) = pointBounds57016 := by
 decide +kernel
def cuts57017 : List PrefixCut := [⟨64,216526979,216527103⟩]
theorem checked57017 : checkPrefixCuts (2^48) 7477264385 10 Manual.Count131072.C057017.packed 64 cuts57017 = true := by
 decide +kernel
def cuts57018 : List PrefixCut := [⟨4,14906796,14906804⟩,
⟨64,220513363,220513487⟩]
theorem checked57018 : checkPrefixCuts (2^48) 7477395457 10 Manual.Count131072.C057018.packed 64 cuts57018 = true := by
 decide +kernel
def pointBounds57018 : List (Nat × Nat × Nat) := [(7477403648,113286754415750,113287142463792)]
theorem point_links_checked57018 : (cuts57018.take 1).map (fun c => (7477395457-1+2*2^10*c.k,113286739508954+c.lower,113287127556988+c.upper)) = pointBounds57018 := by
 decide +kernel
def cuts57019 : List PrefixCut := [⟨55,186970291,186970400⟩,
⟨64,217723941,217724068⟩]
theorem checked57019 : checkPrefixCuts (2^48) 7477526529 10 Manual.Count131072.C057019.packed 64 cuts57019 = true := by
 decide +kernel
def pointBounds57019 : List (Nat × Nat × Nat) := [(7477639168,113287146992608,113287535040875)]
theorem point_links_checked57019 : (cuts57019.take 1).map (fun c => (7477526529-1+2*2^10*c.k,113286960022317+c.lower,113287348070475+c.upper)) = pointBounds57019 := by
 decide +kernel
def cuts57020 : List PrefixCut := [⟨64,216553232,216553354⟩]
theorem checked57020 : checkPrefixCuts (2^48) 7477657601 10 Manual.Count131072.C057020.packed 64 cuts57020 = true := by
 decide +kernel
def cuts57021 : List PrefixCut := [⟨42,140288920,140289000⟩,
⟨64,213124091,213124212⟩]
theorem checked57021 : checkPrefixCuts (2^48) 7477788673 10 Manual.Count131072.C057021.packed 64 cuts57021 = true := by
 decide +kernel
def pointBounds57021 : List (Nat × Nat × Nat) := [(7477874688,113287534588410,113287922636897)]
theorem point_links_checked57021 : (cuts57021.take 1).map (fun c => (7477788673-1+2*2^10*c.k,113287394299490+c.lower,113287782347897+c.upper)) = pointBounds57021 := by
 decide +kernel
def cuts57022 : List PrefixCut := [⟨64,218841705,218841830⟩]
theorem checked57022 : checkPrefixCuts (2^48) 7477919745 10 Manual.Count131072.C057022.packed 64 cuts57022 = true := by
 decide +kernel
def cuts57023 : List PrefixCut := [⟨29,98993178,98993235⟩,
⟨64,217558121,217558248⟩]
theorem checked57023 : checkPrefixCuts (2^48) 7478050817 10 Manual.Count131072.C057023.packed 64 cuts57023 = true := by
 decide +kernel
def pointBounds57023 : List (Nat × Nat × Nat) := [(7478110208,113287925258464,113288313307174)]
theorem point_links_checked57023 : (cuts57023.take 1).map (fun c => (7478050817-1+2*2^10*c.k,113287826265286+c.lower,113288214313939+c.upper)) = pointBounds57023 := by
 decide +kernel
def cuts57024 : List PrefixCut := [⟨64,217403760,217403882⟩]
theorem checked57024 : checkPrefixCuts (2^48) 7478181889 10 Manual.Count131072.C057024.packed 64 cuts57024 = true := by
 decide +kernel
def cuts57025 : List PrefixCut := [⟨16,55328952,55328984⟩,
⟨64,217249392,217249514⟩]
theorem checked57025 : checkPrefixCuts (2^48) 7478312961 10 Manual.Count131072.C057025.packed 64 cuts57025 = true := by
 decide +kernel
def pointBounds57025 : List (Nat × Nat × Nat) := [(7478345728,113288316556119,113288704605053)]
theorem point_links_checked57025 : (cuts57025.take 1).map (fun c => (7478312961-1+2*2^10*c.k,113288261227167+c.lower,113288649276069+c.upper)) = pointBounds57025 := by
 decide +kernel
def cuts57026 : List PrefixCut := [⟨64,217960687,217960809⟩]
theorem checked57026 : checkPrefixCuts (2^48) 7478444033 10 Manual.Count131072.C057026.packed 64 cuts57026 = true := by
 decide +kernel
def cuts57027 : List PrefixCut := [⟨3,9785746,9785752⟩,
⟨64,215021167,215021290⟩]
theorem checked57027 : checkPrefixCuts (2^48) 7478575105 10 Manual.Count131072.C057027.packed 64 cuts57027 = true := by
 decide +kernel
def pointBounds57027 : List (Nat × Nat × Nat) := [(7478581248,113288706222992,113289094272144)]
theorem point_links_checked57027 : (cuts57027.take 1).map (fun c => (7478575105-1+2*2^10*c.k,113288696437246+c.lower,113289084486392+c.upper)) = pointBounds57027 := by
 decide +kernel
def cuts57028 : List PrefixCut := [⟨54,183478248,183478349⟩,
⟨64,217915402,217915523⟩]
theorem checked57028 : checkPrefixCuts (2^48) 7478706177 10 Manual.Count131072.C057028.packed 64 cuts57028 = true := by
 decide +kernel
def pointBounds57028 : List (Nat × Nat × Nat) := [(7478816768,113289094936661,113289482986031)]
theorem point_links_checked57028 : (cuts57028.take 1).map (fun c => (7478706177-1+2*2^10*c.k,113288911458413+c.lower,113289299507682+c.upper)) = pointBounds57028 := by
 decide +kernel
def cuts57029 : List PrefixCut := [⟨64,214674915,214675034⟩]
theorem checked57029 : checkPrefixCuts (2^48) 7478837249 10 Manual.Count131072.C057029.packed 64 cuts57029 = true := by
 decide +kernel
def cuts57030 : List PrefixCut := [⟨41,137105440,137105519⟩,
⟨64,215536745,215536870⟩]
theorem checked57030 : checkPrefixCuts (2^48) 7478968321 10 Manual.Count131072.C057030.packed 64 cuts57030 = true := by
 decide +kernel
def pointBounds57030 : List (Nat × Nat × Nat) := [(7479052288,113289481154170,113289869203758)]
theorem point_links_checked57030 : (cuts57030.take 1).map (fun c => (7478968321-1+2*2^10*c.k,113289344048730+c.lower,113289732098239+c.upper)) = pointBounds57030 := by
 decide +kernel
def cuts57031 : List PrefixCut := [⟨64,217452355,217452482⟩]
theorem checked57031 : checkPrefixCuts (2^48) 7479099393 10 Manual.Count131072.C057031.packed 64 cuts57031 = true := by
 decide +kernel
def cuts57032 : List PrefixCut := [⟨28,95552882,95552935⟩,
⟨64,217599073,217599198⟩]
theorem checked57032 : checkPrefixCuts (2^48) 7479230465 10 Manual.Count131072.C057032.packed 64 cuts57032 = true := by
 decide +kernel
def pointBounds57032 : List (Nat × Nat × Nat) := [(7479287808,113289872590712,113290260640526)]
theorem point_links_checked57032 : (cuts57032.take 1).map (fun c => (7479230465-1+2*2^10*c.k,113289777037830+c.lower,113290165087591+c.upper)) = pointBounds57032 := by
 decide +kernel
def cuts57033 : List PrefixCut := [⟨64,216692062,216692188⟩]
theorem checked57033 : checkPrefixCuts (2^48) 7479361537 10 Manual.Count131072.C057033.packed 64 cuts57033 = true := by
 decide +kernel
def cuts57034 : List PrefixCut := [⟨15,50804293,50804323⟩,
⟨64,220188081,220188205⟩]
theorem checked57034 : checkPrefixCuts (2^48) 7479492609 10 Manual.Count131072.C057034.packed 64 cuts57034 = true := by
 decide +kernel
def pointBounds57034 : List (Nat × Nat × Nat) := [(7479523328,113290262133258,113290650183300)]
theorem point_links_checked57034 : (cuts57034.take 1).map (fun c => (7479492609-1+2*2^10*c.k,113290211328965+c.lower,113290599378977+c.upper)) = pointBounds57034 := by
 decide +kernel
def cuts57035 : List PrefixCut := [⟨64,217136042,217136164⟩]
theorem checked57035 : checkPrefixCuts (2^48) 7479623681 10 Manual.Count131072.C057035.packed 64 cuts57035 = true := by
 decide +kernel
def cuts57036 : List PrefixCut := [⟨2,6623154,6623158⟩,
⟨64,215551731,215551855⟩]
theorem checked57036 : checkPrefixCuts (2^48) 7479754753 10 Manual.Count131072.C057036.packed 64 cuts57036 = true := by
 decide +kernel
def pointBounds57036 : List (Nat × Nat × Nat) := [(7479758848,113290655276242,113291043326504)]
theorem point_links_checked57036 : (cuts57036.take 1).map (fun c => (7479754753-1+2*2^10*c.k,113290648653088+c.lower,113291036703346+c.upper)) = pointBounds57036 := by
 decide +kernel
def cuts57037 : List PrefixCut := [⟨53,180476535,180476639⟩,
⟨64,217580016,217580141⟩]
theorem checked57037 : checkPrefixCuts (2^48) 7479885825 10 Manual.Count131072.C057037.packed 64 cuts57037 = true := by
 decide +kernel
def pointBounds57037 : List (Nat × Nat × Nat) := [(7479994368,113291044681354,113291432731840)]
theorem point_links_checked57037 : (cuts57037.take 1).map (fun c => (7479885825-1+2*2^10*c.k,113290864204819+c.lower,113291252255201+c.upper)) = pointBounds57037 := by
 decide +kernel
def cuts57038 : List PrefixCut := [⟨64,215995740,215995862⟩]
theorem checked57038 : checkPrefixCuts (2^48) 7480016897 10 Manual.Count131072.C057038.packed 64 cuts57038 = true := by
 decide +kernel
def cuts57039 : List PrefixCut := [⟨40,133659567,133659644⟩,
⟨64,216180086,216180208⟩]
theorem checked57039 : checkPrefixCuts (2^48) 7480147969 10 Manual.Count131072.C057039.packed 64 cuts57039 = true := by
 decide +kernel
def pointBounds57039 : List (Nat × Nat × Nat) := [(7480229888,113291431440142,113291819490848)]
theorem point_links_checked57039 : (cuts57039.take 1).map (fun c => (7480147969-1+2*2^10*c.k,113291297780575+c.lower,113291685831204+c.upper)) = pointBounds57039 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S6.B000219
