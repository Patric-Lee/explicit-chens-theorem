import PlattAssemblyKernel
import PlattCertificates.Count131072.C072016
import PlattCertificates.Count131072.C072017
import PlattCertificates.Count131072.C072018
import PlattCertificates.Count131072.C072019
import PlattCertificates.Count131072.C072020
import PlattCertificates.Count131072.C072021
import PlattCertificates.Count131072.C072022
import PlattCertificates.Count131072.C072023
import PlattCertificates.Count131072.C072024
import PlattCertificates.Count131072.C072025
import PlattCertificates.Count131072.C072026
import PlattCertificates.Count131072.C072027
import PlattCertificates.Count131072.C072028
import PlattCertificates.Count131072.C072029
import PlattCertificates.Count131072.C072030
import PlattCertificates.Count131072.C072031
import PlattCertificates.Count131072.C072032
import PlattCertificates.Count131072.C072033
import PlattCertificates.Count131072.C072034
import PlattCertificates.Count131072.C072035
import PlattCertificates.Count131072.C072036
import PlattCertificates.Count131072.C072037
import PlattCertificates.Count131072.C072038
import PlattCertificates.Count131072.C072039
import PlattCertificates.Count131072.C072040
import PlattCertificates.Count131072.C072041
import PlattCertificates.Count131072.C072042
import PlattCertificates.Count131072.C072043
import PlattCertificates.Count131072.C072044
import PlattCertificates.Count131072.C072045
import PlattCertificates.Count131072.C072046
import PlattCertificates.Count131072.C072047
namespace ChenEffective.PlattWindow.Assembly.Prefix.S8.B000063
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts72016 : List PrefixCut := [⟨64,167544595,167544695⟩]
theorem checked72016 : checkPrefixCuts (2^48) 9443213313 10 Manual.Count131072.C072016.packed 64 cuts72016 = true := by
 decide +kernel
def cuts72017 : List PrefixCut := [⟨50,136424509,136424588⟩,
⟨64,174010291,174010390⟩]
theorem checked72017 : checkPrefixCuts (2^48) 9443344385 10 Manual.Count131072.C072017.packed 64 cuts72017 = true := by
 decide +kernel
def pointBounds72017 : List (Nat × Nat × Nat) := [(9443446784,116162090647398,116162480358410)]
theorem point_links_checked72017 : (cuts72017.take 1).map (fun c => (9443344385-1+2*2^10*c.k,116161954222889+c.lower,116162343933822+c.upper)) = pointBounds72017 := by
 decide +kernel
def cuts72018 : List PrefixCut := [⟨64,167599576,167599674⟩]
theorem checked72018 : checkPrefixCuts (2^48) 9443475457 10 Manual.Count131072.C072018.packed 64 cuts72018 = true := by
 decide +kernel
def cuts72019 : List PrefixCut := [⟨64,170577800,170577904⟩]
theorem checked72019 : checkPrefixCuts (2^48) 9443606529 10 Manual.Count131072.C072019.packed 64 cuts72019 = true := by
 decide +kernel
def cuts72020 : List PrefixCut := [⟨3,7510972,7510977⟩,
⟨64,169800495,169800594⟩]
theorem checked72020 : checkPrefixCuts (2^48) 9443737601 10 Manual.Count131072.C072020.packed 64 cuts72020 = true := by
 decide +kernel
def pointBounds72020 : List (Nat × Nat × Nat) := [(9443743744,116162473921528,116162863632767)]
theorem point_links_checked72020 : (cuts72020.take 1).map (fun c => (9443737601-1+2*2^10*c.k,116162466410556+c.lower,116162856121790+c.upper)) = pointBounds72020 := by
 decide +kernel
def cuts72021 : List PrefixCut := [⟨64,168784774,168784868⟩]
theorem checked72021 : checkPrefixCuts (2^48) 9443868673 10 Manual.Count131072.C072021.packed 64 cuts72021 = true := by
 decide +kernel
def cuts72022 : List PrefixCut := [⟨20,53856843,53856876⟩,
⟨64,170838946,170839047⟩]
theorem checked72022 : checkPrefixCuts (2^48) 9443999745 10 Manual.Count131072.C072022.packed 64 cuts72022 = true := by
 decide +kernel
def pointBounds72022 : List (Nat × Nat × Nat) := [(9444040704,116162858852668,116163248564128)]
theorem point_links_checked72022 : (cuts72022.take 1).map (fun c => (9443999745-1+2*2^10*c.k,116162804995825+c.lower,116163194707252+c.upper)) = pointBounds72022 := by
 decide +kernel
def cuts72023 : List PrefixCut := [⟨64,170598127,170598231⟩]
theorem checked72023 : checkPrefixCuts (2^48) 9444130817 10 Manual.Count131072.C072023.packed 64 cuts72023 = true := by
 decide +kernel
def cuts72024 : List PrefixCut := [⟨37,97070586,97070645⟩,
⟨64,167973052,167973151⟩]
theorem checked72024 : checkPrefixCuts (2^48) 9444261889 10 Manual.Count131072.C072024.packed 64 cuts72024 = true := by
 decide +kernel
def pointBounds72024 : List (Nat × Nat × Nat) := [(9444337664,116163243503484,116163633215175)]
theorem point_links_checked72024 : (cuts72024.take 1).map (fun c => (9444261889-1+2*2^10*c.k,116163146432898+c.lower,116163536144530+c.upper)) = pointBounds72024 := by
 decide +kernel
def cuts72025 : List PrefixCut := [⟨64,172053760,172053858⟩]
theorem checked72025 : checkPrefixCuts (2^48) 9444392961 10 Manual.Count131072.C072025.packed 64 cuts72025 = true := by
 decide +kernel
def cuts72026 : List PrefixCut := [⟨54,143649487,143649576⟩,
⟨64,170591030,170591135⟩]
theorem checked72026 : checkPrefixCuts (2^48) 9444524033 10 Manual.Count131072.C072026.packed 64 cuts72026 = true := by
 decide +kernel
def pointBounds72026 : List (Nat × Nat × Nat) := [(9444634624,116163630109197,116164019821115)]
theorem point_links_checked72026 : (cuts72026.take 1).map (fun c => (9444524033-1+2*2^10*c.k,116163486459710+c.lower,116163876171539+c.upper)) = pointBounds72026 := by
 decide +kernel
def cuts72027 : List PrefixCut := [⟨64,175118629,175118724⟩]
theorem checked72027 : checkPrefixCuts (2^48) 9444655105 10 Manual.Count131072.C072027.packed 64 cuts72027 = true := by
 decide +kernel
def cuts72028 : List PrefixCut := [⟨64,168291551,168291652⟩]
theorem checked72028 : checkPrefixCuts (2^48) 9444786177 10 Manual.Count131072.C072028.packed 64 cuts72028 = true := by
 decide +kernel
def cuts72029 : List PrefixCut := [⟨7,18685672,18685684⟩,
⟨64,169451475,169451574⟩]
theorem checked72029 : checkPrefixCuts (2^48) 9444917249 10 Manual.Count131072.C072029.packed 64 cuts72029 = true := by
 decide +kernel
def pointBounds72029 : List (Nat × Nat × Nat) := [(9444931584,116164019146592,116164408858734)]
theorem point_links_checked72029 : (cuts72029.take 1).map (fun c => (9444917249-1+2*2^10*c.k,116164000460920+c.lower,116164390173050+c.upper)) = pointBounds72029 := by
 decide +kernel
def cuts72030 : List PrefixCut := [⟨64,170194148,170194257⟩]
theorem checked72030 : checkPrefixCuts (2^48) 9445048321 10 Manual.Count131072.C072030.packed 64 cuts72030 = true := by
 decide +kernel
def cuts72031 : List PrefixCut := [⟨24,63267158,63267196⟩,
⟨64,168820957,168821055⟩]
theorem checked72031 : checkPrefixCuts (2^48) 9445179393 10 Manual.Count131072.C072031.packed 64 cuts72031 = true := by
 decide +kernel
def pointBounds72031 : List (Nat × Nat × Nat) := [(9445228544,116164403373701,116164793086077)]
theorem point_links_checked72031 : (cuts72031.take 1).map (fun c => (9445179393-1+2*2^10*c.k,116164340106543+c.lower,116164729818881+c.upper)) = pointBounds72031 := by
 decide +kernel
def cuts72032 : List PrefixCut := [⟨64,168431201,168431312⟩]
theorem checked72032 : checkPrefixCuts (2^48) 9445310465 10 Manual.Count131072.C072032.packed 64 cuts72032 = true := by
 decide +kernel
def cuts72033 : List PrefixCut := [⟨41,109276398,109276466⟩,
⟨64,169442073,169442175⟩]
theorem checked72033 : checkPrefixCuts (2^48) 9445441537 10 Manual.Count131072.C072033.packed 64 cuts72033 = true := by
 decide +kernel
def pointBounds72033 : List (Nat × Nat × Nat) := [(9445525504,116164786635099,116165176347714)]
theorem point_links_checked72033 : (cuts72033.take 1).map (fun c => (9445441537-1+2*2^10*c.k,116164677358701+c.lower,116165067071248+c.upper)) = pointBounds72033 := by
 decide +kernel
def cuts72034 : List PrefixCut := [⟨64,169499316,169499419⟩]
theorem checked72034 : checkPrefixCuts (2^48) 9445572609 10 Manual.Count131072.C072034.packed 64 cuts72034 = true := by
 decide +kernel
def cuts72035 : List PrefixCut := [⟨58,154835932,154836022⟩,
⟨64,170808119,170808219⟩]
theorem checked72035 : checkPrefixCuts (2^48) 9445703681 10 Manual.Count131072.C072035.packed 64 cuts72035 = true := by
 decide +kernel
def pointBounds72035 : List (Nat × Nat × Nat) := [(9445822464,116165171136022,116165560848864)]
theorem point_links_checked72035 : (cuts72035.take 1).map (fun c => (9445703681-1+2*2^10*c.k,116165016300090+c.lower,116165406012842+c.upper)) = pointBounds72035 := by
 decide +kernel
def cuts72036 : List PrefixCut := [⟨64,171789110,171789204⟩]
theorem checked72036 : checkPrefixCuts (2^48) 9445834753 10 Manual.Count131072.C072036.packed 64 cuts72036 = true := by
 decide +kernel
def cuts72037 : List PrefixCut := [⟨64,168359919,168360024⟩]
theorem checked72037 : checkPrefixCuts (2^48) 9445965825 10 Manual.Count131072.C072037.packed 64 cuts72037 = true := by
 decide +kernel
def cuts72038 : List PrefixCut := [⟨11,28397470,28397487⟩,
⟨64,168268197,168268295⟩]
theorem checked72038 : checkPrefixCuts (2^48) 9446096897 10 Manual.Count131072.C072038.packed 64 cuts72038 = true := by
 decide +kernel
def pointBounds72038 : List (Nat × Nat × Nat) := [(9446119424,116165555654708,116165945367776)]
theorem point_links_checked72038 : (cuts72038.take 1).map (fun c => (9446096897-1+2*2^10*c.k,116165527257238+c.lower,116165916970289+c.upper)) = pointBounds72038 := by
 decide +kernel
def cuts72039 : List PrefixCut := [⟨64,170768844,170768944⟩]
theorem checked72039 : checkPrefixCuts (2^48) 9446227969 10 Manual.Count131072.C072039.packed 64 cuts72039 = true := by
 decide +kernel
def cuts72040 : List PrefixCut := [⟨28,74492737,74492780⟩,
⟨64,171690179,171690277⟩]
theorem checked72040 : checkPrefixCuts (2^48) 9446359041 10 Manual.Count131072.C072040.packed 64 cuts72040 = true := by
 decide +kernel
def pointBounds72040 : List (Nat × Nat × Nat) := [(9446416384,116165940787016,116166330500308)]
theorem point_links_checked72040 : (cuts72040.take 1).map (fun c => (9446359041-1+2*2^10*c.k,116165866294279+c.lower,116166256007528+c.upper)) = pointBounds72040 := by
 decide +kernel
def cuts72041 : List PrefixCut := [⟨64,170734299,170734402⟩]
theorem checked72041 : checkPrefixCuts (2^48) 9446490113 10 Manual.Count131072.C072041.packed 64 cuts72041 = true := by
 decide +kernel
def cuts72042 : List PrefixCut := [⟨45,120585264,120585337⟩,
⟨64,171536433,171536534⟩]
theorem checked72042 : checkPrefixCuts (2^48) 9446621185 10 Manual.Count131072.C072042.packed 64 cuts72042 = true := by
 decide +kernel
def pointBounds72042 : List (Nat × Nat × Nat) := [(9446713344,116166329304021,116166719017544)]
theorem point_links_checked72042 : (cuts72042.take 1).map (fun c => (9446621185-1+2*2^10*c.k,116166208718757+c.lower,116166598432207+c.upper)) = pointBounds72042 := by
 decide +kernel
def cuts72043 : List PrefixCut := [⟨64,167213675,167213771⟩]
theorem checked72043 : checkPrefixCuts (2^48) 9446752257 10 Manual.Count131072.C072043.packed 64 cuts72043 = true := by
 decide +kernel
def cuts72044 : List PrefixCut := [⟨62,161103356,161103452⟩,
⟨64,166496273,166496372⟩]
theorem checked72044 : checkPrefixCuts (2^48) 9446883329 10 Manual.Count131072.C072044.packed 64 cuts72044 = true := by
 decide +kernel
def pointBounds72044 : List (Nat × Nat × Nat) := [(9447010304,116166708572221,116167098285964)]
theorem point_links_checked72044 : (cuts72044.take 1).map (fun c => (9446883329-1+2*2^10*c.k,116166547468865+c.lower,116166937182512+c.upper)) = pointBounds72044 := by
 decide +kernel
def cuts72045 : List PrefixCut := [⟨64,170844019,170844114⟩]
theorem checked72045 : checkPrefixCuts (2^48) 9447014401 10 Manual.Count131072.C072045.packed 64 cuts72045 = true := by
 decide +kernel
def cuts72046 : List PrefixCut := [⟨64,169888212,169888316⟩]
theorem checked72046 : checkPrefixCuts (2^48) 9447145473 10 Manual.Count131072.C072046.packed 64 cuts72046 = true := by
 decide +kernel
def cuts72047 : List PrefixCut := [⟨15,38970868,38970891⟩,
⟨64,168932445,168932551⟩]
theorem checked72047 : checkPrefixCuts (2^48) 9447276545 10 Manual.Count131072.C072047.packed 64 cuts72047 = true := by
 decide +kernel
def pointBounds72047 : List (Nat × Nat × Nat) := [(9447307264,116167093668237,116167483382205)]
theorem point_links_checked72047 : (cuts72047.take 1).map (fun c => (9447276545-1+2*2^10*c.k,116167054697369+c.lower,116167444411314+c.upper)) = pointBounds72047 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S8.B000063
