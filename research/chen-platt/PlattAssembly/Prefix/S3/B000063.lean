import PlattAssemblyKernel
import PlattCertificates.Count131072.C022016
import PlattCertificates.Count131072.C022017
import PlattCertificates.Count131072.C022018
import PlattCertificates.Count131072.C022019
import PlattCertificates.Count131072.C022020
import PlattCertificates.Count131072.C022021
import PlattCertificates.Count131072.C022022
import PlattCertificates.Count131072.C022023
import PlattCertificates.Count131072.C022024
import PlattCertificates.Count131072.C022025
import PlattCertificates.Count131072.C022026
import PlattCertificates.Count131072.C022027
import PlattCertificates.Count131072.C022028
import PlattCertificates.Count131072.C022029
import PlattCertificates.Count131072.C022030
import PlattCertificates.Count131072.C022031
import PlattCertificates.Count131072.C022032
import PlattCertificates.Count131072.C022033
import PlattCertificates.Count131072.C022034
import PlattCertificates.Count131072.C022035
import PlattCertificates.Count131072.C022036
import PlattCertificates.Count131072.C022037
import PlattCertificates.Count131072.C022038
import PlattCertificates.Count131072.C022039
import PlattCertificates.Count131072.C022040
import PlattCertificates.Count131072.C022041
import PlattCertificates.Count131072.C022042
import PlattCertificates.Count131072.C022043
import PlattCertificates.Count131072.C022044
import PlattCertificates.Count131072.C022045
import PlattCertificates.Count131072.C022046
import PlattCertificates.Count131072.C022047
namespace ChenEffective.PlattWindow.Assembly.Prefix.S3.B000063
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts22016 : List PrefixCut := [⟨44,203096581,203096703⟩,
⟨128,588338259,588338593⟩]
theorem checked22016 : checkPrefixCuts (2^48) 2889613313 9 Manual.Count131072.C022016.packed 128 cuts22016 = true := by
 decide +kernel
def pointBounds22016 : List (Nat × Nat × Nat) := [(2889658368,101262862376626,101263243466366)]
theorem point_links_checked22016 : (cuts22016.take 1).map (fun c => (2889613313-1+2*2^9*c.k,101262659280045+c.lower,101263040369663+c.upper)) = pointBounds22016 := by
 decide +kernel
def cuts22017 : List PrefixCut := [⟨5,22695292,22695305⟩,
⟨94,430327155,430327404⟩,
⟨128,582564824,582565159⟩]
theorem checked22017 : checkPrefixCuts (2^48) 2889744385 9 Manual.Count131072.C022017.packed 128 cuts22017 = true := by
 decide +kernel
def pointBounds22017 : List (Nat × Nat × Nat) := [(2889749504,101263270313596,101263651403561),(2889840640,101263677945459,101264059035660)]
theorem point_links_checked22017 : (cuts22017.take 2).map (fun c => (2889744385-1+2*2^9*c.k,101263247618304+c.lower,101263628708256+c.upper)) = pointBounds22017 := by
 decide +kernel
def cuts22018 : List PrefixCut := [⟨55,255089004,255089151⟩,
⟨128,591888498,591888843⟩]
theorem checked22018 : checkPrefixCuts (2^48) 2889875457 9 Manual.Count131072.C022018.packed 128 cuts22018 = true := by
 decide +kernel
def pointBounds22018 : List (Nat × Nat × Nat) := [(2889931776,101264085272132,101264466362566)]
theorem point_links_checked22018 : (cuts22018.take 1).map (fun c => (2889875457-1+2*2^9*c.k,101263830183128+c.lower,101264211273415+c.upper)) = pointBounds22018 := by
 decide +kernel
def cuts22019 : List PrefixCut := [⟨16,71878000,71878040⟩,
⟨105,477718162,477718442⟩,
⟨128,586504936,586505280⟩]
theorem checked22019 : checkPrefixCuts (2^48) 2890006529 9 Manual.Count131072.C022019.packed 128 cuts22019 = true := by
 decide +kernel
def pointBounds22019 : List (Nat × Nat × Nat) := [(2890022912,101264493949626,101264875040298),(2890114048,101264899789788,101265280880700)]
theorem point_links_checked22019 : (cuts22019.take 2).map (fun c => (2890006529-1+2*2^9*c.k,101264422071626+c.lower,101264803162258+c.upper)) = pointBounds22019 := by
 decide +kernel
def cuts22020 : List PrefixCut := [⟨66,302202373,302202544⟩,
⟨128,590471383,590471723⟩]
theorem checked22020 : checkPrefixCuts (2^48) 2890137601 9 Manual.Count131072.C022020.packed 128 cuts22020 = true := by
 decide +kernel
def pointBounds22020 : List (Nat × Nat × Nat) := [(2890205184,101265310778935,101265691870082)]
theorem point_links_checked22020 : (cuts22020.take 1).map (fun c => (2890137601-1+2*2^9*c.k,101265008576562+c.lower,101265389667538+c.upper)) = pointBounds22020 := by
 decide +kernel
def cuts22021 : List PrefixCut := [⟨27,121635903,121635976⟩,
⟨116,523931823,523932126⟩,
⟨128,578271479,578271811⟩]
theorem checked22021 : checkPrefixCuts (2^48) 2890268673 9 Manual.Count131072.C022021.packed 128 cuts22021 = true := by
 decide +kernel
def pointBounds22021 : List (Nat × Nat × Nat) := [(2890296320,101265720683848,101266101775237),(2890387456,101266122979768,101266504071387)]
theorem point_links_checked22021 : (cuts22021.take 2).map (fun c => (2890268673-1+2*2^9*c.k,101265599047945+c.lower,101265980139261+c.upper)) = pointBounds22021 := by
 decide +kernel
def cuts22022 : List PrefixCut := [⟨77,356221081,356221284⟩,
⟨128,588372989,588373329⟩]
theorem checked22022 : checkPrefixCuts (2^48) 2890399745 9 Manual.Count131072.C022022.packed 128 cuts22022 = true := by
 decide +kernel
def pointBounds22022 : List (Nat × Nat × Nat) := [(2890478592,101266533540505,101266914632356)]
theorem point_links_checked22022 : (cuts22022.take 1).map (fun c => (2890399745-1+2*2^9*c.k,101266177319424+c.lower,101266558411072+c.upper)) = pointBounds22022 := by
 decide +kernel
def cuts22023 : List PrefixCut := [⟨38,175961360,175961460⟩,
⟨127,590196461,590196799⟩,
⟨128,594578285,594578626⟩]
theorem checked22023 : checkPrefixCuts (2^48) 2890530817 9 Manual.Count131072.C022023.packed 128 cuts22023 = true := by
 decide +kernel
def pointBounds22023 : List (Nat × Nat × Nat) := [(2890569728,101266941653773,101267322745861),(2890660864,101267355888874,101267736981200)]
theorem point_links_checked22023 : (cuts22023.take 2).map (fun c => (2890530817-1+2*2^9*c.k,101266765692413+c.lower,101267146784401+c.upper)) = pointBounds22023 := by
 decide +kernel
def cuts22024 : List PrefixCut := [⟨88,406919009,406919239⟩,
⟨128,590656441,590656776⟩]
theorem checked22024 : checkPrefixCuts (2^48) 2890661889 9 Manual.Count131072.C022024.packed 128 cuts22024 = true := by
 decide +kernel
def pointBounds22024 : List (Nat × Nat × Nat) := [(2890752000,101267767189707,101268148282266)]
theorem point_links_checked22024 : (cuts22024.take 1).map (fun c => (2890661889-1+2*2^9*c.k,101267360270698+c.lower,101267741363027+c.upper)) = pointBounds22024 := by
 decide +kernel
def cuts22025 : List PrefixCut := [⟨49,226674069,226674203⟩,
⟨128,579335122,579335461⟩]
theorem checked22025 : checkPrefixCuts (2^48) 2890792961 9 Manual.Count131072.C022025.packed 128 cuts22025 = true := by
 decide +kernel
def pointBounds22025 : List (Nat × Nat × Nat) := [(2890843136,101268177601208,101268558694006)]
theorem point_links_checked22025 : (cuts22025.take 1).map (fun c => (2890792961-1+2*2^9*c.k,101267950927139+c.lower,101268332019803+c.upper)) = pointBounds22025 := by
 decide +kernel
def cuts22026 : List PrefixCut := [⟨10,46248308,46248335⟩,
⟨99,450500078,450500337⟩,
⟨128,584371626,584371963⟩]
theorem checked22026 : checkPrefixCuts (2^48) 2890924033 9 Manual.Count131072.C022026.packed 128 cuts22026 = true := by
 decide +kernel
def pointBounds22026 : List (Nat × Nat × Nat) := [(2890934272,101268576510569,101268957603599),(2891025408,101268980762339,101269361855601)]
theorem point_links_checked22026 : (cuts22026.take 2).map (fun c => (2890924033-1+2*2^9*c.k,101268530262261+c.lower,101268911355264+c.upper)) = pointBounds22026 := by
 decide +kernel
def cuts22027 : List PrefixCut := [⟨60,272509422,272509576⟩,
⟨128,582982077,582982412⟩]
theorem checked22027 : checkPrefixCuts (2^48) 2891055105 9 Manual.Count131072.C022027.packed 128 cuts22027 = true := by
 decide +kernel
def pointBounds22027 : List (Nat × Nat × Nat) := [(2891116544,101269387143309,101269768236803)]
theorem point_links_checked22027 : (cuts22027.take 1).map (fun c => (2891055105-1+2*2^9*c.k,101269114633887+c.lower,101269495727227+c.upper)) = pointBounds22027 := by
 decide +kernel
def cuts22028 : List PrefixCut := [⟨21,95798135,95798193⟩,
⟨110,503029649,503029937⟩,
⟨128,585876283,585876620⟩]
theorem checked22028 : checkPrefixCuts (2^48) 2891186177 9 Manual.Count131072.C022028.packed 128 cuts22028 = true := by
 decide +kernel
def pointBounds22028 : List (Nat × Nat × Nat) := [(2891207680,101269793414099,101270174507832),(2891298816,101270200645613,101270581739576)]
theorem point_links_checked22028 : (cuts22028.take 2).map (fun c => (2891186177-1+2*2^9*c.k,101269697615964+c.lower,101270078709639+c.upper)) = pointBounds22028 := by
 decide +kernel
def cuts22029 : List PrefixCut := [⟨71,314150228,314150415⟩,
⟨128,573486240,573486575⟩]
theorem checked22029 : checkPrefixCuts (2^48) 2891317249 9 Manual.Count131072.C022029.packed 128 cuts22029 = true := by
 decide +kernel
def pointBounds22029 : List (Nat × Nat × Nat) := [(2891389952,101270597642475,101270978736674)]
theorem point_links_checked22029 : (cuts22029.take 1).map (fun c => (2891317249-1+2*2^9*c.k,101270283492247+c.lower,101270664586259+c.upper)) = pointBounds22029 := by
 decide +kernel
def cuts22030 : List PrefixCut := [⟨32,149037992,149038074⟩,
⟨121,551753177,551753499⟩,
⟨128,584265769,584266110⟩]
theorem checked22030 : checkPrefixCuts (2^48) 2891448321 9 Manual.Count131072.C022030.packed 128 cuts22030 = true := by
 decide +kernel
def pointBounds22030 : List (Nat × Nat × Nat) := [(2891481088,101271006016479,101271387110908),(2891572224,101271408731664,101271789826333)]
theorem point_links_checked22030 : (cuts22030.take 2).map (fun c => (2891448321-1+2*2^9*c.k,101270856978487+c.lower,101271238072834+c.upper)) = pointBounds22030 := by
 decide +kernel
def cuts22031 : List PrefixCut := [⟨82,373596833,373597045⟩,
⟨128,580929623,580929949⟩]
theorem checked22031 : checkPrefixCuts (2^48) 2891579393 9 Manual.Count131072.C022031.packed 128 cuts22031 = true := by
 decide +kernel
def pointBounds22031 : List (Nat × Nat × Nat) := [(2891663360,101271814841089,101272195935989)]
theorem point_links_checked22031 : (cuts22031.take 1).map (fun c => (2891579393-1+2*2^9*c.k,101271441244256+c.lower,101271822338944+c.upper)) = pointBounds22031 := by
 decide +kernel
def cuts22032 : List PrefixCut := [⟨43,193994229,193994345⟩,
⟨128,586743382,586743717⟩]
theorem checked22032 : checkPrefixCuts (2^48) 2891710465 9 Manual.Count131072.C022032.packed 128 cuts22032 = true := by
 decide +kernel
def pointBounds22032 : List (Nat × Nat × Nat) := [(2891754496,101272216168108,101272597263238)]
theorem point_links_checked22032 : (cuts22032.take 1).map (fun c => (2891710465-1+2*2^9*c.k,101272022173879+c.lower,101272403268893+c.upper)) = pointBounds22032 := by
 decide +kernel
def cuts22033 : List PrefixCut := [⟨4,17714800,17714809⟩,
⟨93,420573836,420574082⟩,
⟨128,579416939,579417276⟩]
theorem checked22033 : checkPrefixCuts (2^48) 2891841537 9 Manual.Count131072.C022033.packed 128 cuts22033 = true := by
 decide +kernel
def pointBounds22033 : List (Nat × Nat × Nat) := [(2891845632,101272626632061,101273007727419),(2891936768,101273029491097,101273410586692)]
theorem point_links_checked22033 : (cuts22033.take 2).map (fun c => (2891841537-1+2*2^9*c.k,101272608917261+c.lower,101272990012610+c.upper)) = pointBounds22033 := by
 decide +kernel
def cuts22034 : List PrefixCut := [⟨54,248675055,248675195⟩,
⟨128,586690343,586690673⟩]
theorem checked22034 : checkPrefixCuts (2^48) 2891972609 9 Manual.Count131072.C022034.packed 128 cuts22034 = true := by
 decide +kernel
def pointBounds22034 : List (Nat × Nat × Nat) := [(2892027904,101273437009255,101273818105081)]
theorem point_links_checked22034 : (cuts22034.take 1).map (fun c => (2891972609-1+2*2^9*c.k,101273188334200+c.lower,101273569429886+c.upper)) = pointBounds22034 := by
 decide +kernel
def cuts22035 : List PrefixCut := [⟨15,68127540,68127581⟩,
⟨104,480388896,480389177⟩,
⟨128,591821803,591822147⟩]
theorem checked22035 : checkPrefixCuts (2^48) 2892103681 9 Manual.Count131072.C022035.packed 128 cuts22035 = true := by
 decide +kernel
def pointBounds22035 : List (Nat × Nat × Nat) := [(2892119040,101273843152083,101274224248140),(2892210176,101274255413439,101274636509736)]
theorem point_links_checked22035 : (cuts22035.take 2).map (fun c => (2892103681-1+2*2^9*c.k,101273775024543+c.lower,101274156120559+c.upper)) = pointBounds22035 := by
 decide +kernel
def cuts22036 : List PrefixCut := [⟨65,298090529,298090708⟩,
⟨128,589653999,589654340⟩]
theorem checked22036 : checkPrefixCuts (2^48) 2892234753 9 Manual.Count131072.C022036.packed 128 cuts22036 = true := by
 decide +kernel
def pointBounds22036 : List (Nat × Nat × Nat) := [(2892301312,101274664936875,101275046033414)]
theorem point_links_checked22036 : (cuts22036.take 1).map (fun c => (2892234753-1+2*2^9*c.k,101274366846346+c.lower,101274747942706+c.upper)) = pointBounds22036 := by
 decide +kernel
def cuts22037 : List PrefixCut := [⟨26,118238992,118239061⟩,
⟨115,530072119,530072423⟩,
⟨128,590794997,590795335⟩]
theorem checked22037 : checkPrefixCuts (2^48) 2892365825 9 Manual.Count131072.C022037.packed 128 cuts22037 = true := by
 decide +kernel
def pointBounds22037 : List (Nat × Nat × Nat) := [(2892392448,101275074739337,101275455836107),(2892483584,101275486572464,101275867669469)]
theorem point_links_checked22037 : (cuts22037.take 2).map (fun c => (2892365825-1+2*2^9*c.k,101274956500345+c.lower,101275337597046+c.upper)) = pointBounds22037 := by
 decide +kernel
def cuts22038 : List PrefixCut := [⟨76,348567200,348567394⟩,
⟨128,587265136,587265465⟩]
theorem checked22038 : checkPrefixCuts (2^48) 2892496897 9 Manual.Count131072.C022038.packed 128 cuts22038 = true := by
 decide +kernel
def pointBounds22038 : List (Nat × Nat × Nat) := [(2892574720,101275895862542,101276276959775)]
theorem point_links_checked22038 : (cuts22038.take 1).map (fun c => (2892496897-1+2*2^9*c.k,101275547295342+c.lower,101275928392381+c.upper)) = pointBounds22038 := by
 decide +kernel
def cuts22039 : List PrefixCut := [⟨37,169508871,169508966⟩,
⟨126,568361478,568361801⟩,
⟨128,577994505,577994833⟩]
theorem checked22039 : checkPrefixCuts (2^48) 2892627969 9 Manual.Count131072.C022039.packed 128 cuts22039 = true := by
 decide +kernel
def pointBounds22039 : List (Nat × Nat × Nat) := [(2892665856,101276304069349,101276685166812),(2892756992,101276702921956,101277084019647)]
theorem point_links_checked22039 : (cuts22039.take 2).map (fun c => (2892627969-1+2*2^9*c.k,101276134560478+c.lower,101276515657846+c.upper)) = pointBounds22039 := by
 decide +kernel
def cuts22040 : List PrefixCut := [⟨87,392223374,392223607⟩,
⟨128,577384419,577384757⟩]
theorem checked22040 : checkPrefixCuts (2^48) 2892759041 9 Manual.Count131072.C022040.packed 128 cuts22040 = true := by
 decide +kernel
def pointBounds22040 : List (Nat × Nat × Nat) := [(2892848128,101277104778357,101277485876286)]
theorem point_links_checked22040 : (cuts22040.take 1).map (fun c => (2892759041-1+2*2^9*c.k,101276712554983+c.lower,101277093652679+c.upper)) = pointBounds22040 := by
 decide +kernel
def cuts22041 : List PrefixCut := [⟨48,213861064,213861190⟩,
⟨128,586017575,586017913⟩]
theorem checked22041 : checkPrefixCuts (2^48) 2892890113 9 Manual.Count131072.C022041.packed 128 cuts22041 = true := by
 decide +kernel
def pointBounds22041 : List (Nat × Nat × Nat) := [(2892939264,101277503800466,101277884898626)]
theorem point_links_checked22041 : (cuts22041.take 1).map (fun c => (2892890113-1+2*2^9*c.k,101277289939402+c.lower,101277671037436+c.upper)) = pointBounds22041 := by
 decide +kernel
def cuts22042 : List PrefixCut := [⟨9,44658084,44658109⟩,
⟨98,449589861,449590120⟩,
⟨128,592898837,592899173⟩]
theorem checked22042 : checkPrefixCuts (2^48) 2893021185 9 Manual.Count131072.C022042.packed 128 cuts22042 = true := by
 decide +kernel
def pointBounds22042 : List (Nat × Nat × Nat) := [(2893030400,101277920615061,101278301713458),(2893121536,101278325546838,101278706645469)]
theorem point_links_checked22042 : (cuts22042.take 2).map (fun c => (2893021185-1+2*2^9*c.k,101277875956977+c.lower,101278257055349+c.upper)) = pointBounds22042 := by
 decide +kernel
def cuts22043 : List PrefixCut := [⟨59,262193934,262194090⟩,
⟨128,578570660,578570996⟩]
theorem checked22043 : checkPrefixCuts (2^48) 2893152257 9 Manual.Count131072.C022043.packed 128 cuts22043 = true := by
 decide +kernel
def pointBounds22043 : List (Nat × Nat × Nat) := [(2893212672,101278731049748,101279112148612)]
theorem point_links_checked22043 : (cuts22043.take 1).map (fun c => (2893152257-1+2*2^9*c.k,101278468855814+c.lower,101278849954522+c.upper)) = pointBounds22043 := by
 decide +kernel
def cuts22044 : List PrefixCut := [⟨20,90378029,90378082⟩,
⟨109,490601942,490602226⟩,
⟨128,580003683,580004020⟩]
theorem checked22044 : checkPrefixCuts (2^48) 2893283329 9 Manual.Count131072.C022044.packed 128 cuts22044 = true := by
 decide +kernel
def pointBounds22044 : List (Nat × Nat × Nat) := [(2893303808,101279137804503,101279518903600),(2893394944,101279538028416,101279919127744)]
theorem point_links_checked22044 : (cuts22044.take 2).map (fun c => (2893283329-1+2*2^9*c.k,101279047426474+c.lower,101279428525518+c.upper)) = pointBounds22044 := by
 decide +kernel
def cuts22045 : List PrefixCut := [⟨70,326179910,326180094⟩,
⟨128,588343674,588344003⟩]
theorem checked22045 : checkPrefixCuts (2^48) 2893414401 9 Manual.Count131072.C022045.packed 128 cuts22045 = true := by
 decide +kernel
def pointBounds22045 : List (Nat × Nat × Nat) := [(2893486080,101279953610067,101280334709632)]
theorem point_links_checked22045 : (cuts22045.take 1).map (fun c => (2893414401-1+2*2^9*c.k,101279627430157+c.lower,101280008529538+c.upper)) = pointBounds22045 := by
 decide +kernel
def cuts22046 : List PrefixCut := [⟨31,142607029,142607108⟩,
⟨120,550769616,550769935⟩,
⟨128,587733185,587733525⟩]
theorem checked22046 : checkPrefixCuts (2^48) 2893545473 9 Manual.Count131072.C022046.packed 128 cuts22046 = true := by
 decide +kernel
def pointBounds22046 : List (Nat × Nat × Nat) := [(2893577216,101280358380860,101280739480649),(2893668352,101280766543447,101281147643476)]
theorem point_links_checked22046 : (cuts22046.take 2).map (fun c => (2893545473-1+2*2^9*c.k,101280215773831+c.lower,101280596873541+c.upper)) = pointBounds22046 := by
 decide +kernel
def cuts22047 : List PrefixCut := [⟨81,365349978,365350185⟩,
⟨128,578660506,578660833⟩]
theorem checked22047 : checkPrefixCuts (2^48) 2893676545 9 Manual.Count131072.C022047.packed 128 cuts22047 = true := by
 decide +kernel
def pointBounds22047 : List (Nat × Nat × Nat) := [(2893759488,101281168856994,101281549957251)]
theorem point_links_checked22047 : (cuts22047.take 1).map (fun c => (2893676545-1+2*2^9*c.k,101280803507016+c.lower,101281184607066+c.upper)) = pointBounds22047 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S3.B000063
