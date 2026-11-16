import PlattAssemblyKernel
import PlattCertificates.Count131072.C032016
import PlattCertificates.Count131072.C032017
import PlattCertificates.Count131072.C032018
import PlattCertificates.Count131072.C032019
import PlattCertificates.Count131072.C032020
import PlattCertificates.Count131072.C032021
import PlattCertificates.Count131072.C032022
import PlattCertificates.Count131072.C032023
import PlattCertificates.Count131072.C032024
import PlattCertificates.Count131072.C032025
import PlattCertificates.Count131072.C032026
import PlattCertificates.Count131072.C032027
import PlattCertificates.Count131072.C032028
import PlattCertificates.Count131072.C032029
import PlattCertificates.Count131072.C032030
import PlattCertificates.Count131072.C032031
import PlattCertificates.Count131072.C032032
import PlattCertificates.Count131072.C032033
import PlattCertificates.Count131072.C032034
import PlattCertificates.Count131072.C032035
import PlattCertificates.Count131072.C032036
import PlattCertificates.Count131072.C032037
import PlattCertificates.Count131072.C032038
import PlattCertificates.Count131072.C032039
import PlattCertificates.Count131072.C032040
import PlattCertificates.Count131072.C032041
import PlattCertificates.Count131072.C032042
import PlattCertificates.Count131072.C032043
import PlattCertificates.Count131072.C032044
import PlattCertificates.Count131072.C032045
import PlattCertificates.Count131072.C032046
import PlattCertificates.Count131072.C032047
namespace ChenEffective.PlattWindow.Assembly.Prefix.S4.B000063
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts32016 : List PrefixCut := [⟨20,62522524,62522559⟩,
⟨128,396439855,396440070⟩]
theorem checked32016 : checkPrefixCuts (2^48) 4200333313 9 Manual.Count131072.C032016.packed 128 cuts32016 = true := by
 decide +kernel
def pointBounds32016 : List (Nat × Nat × Nat) := [(4200353792,106054524544423,106054908331631)]
theorem point_links_checked32016 : (cuts32016.take 1).map (fun c => (4200333313-1+2*2^9*c.k,106054462021899+c.lower,106054845809072+c.upper)) = pointBounds32016 := by
 decide +kernel
def cuts32017 : List PrefixCut := [⟨21,66005100,66005138⟩,
⟨128,399174859,399175096⟩]
theorem checked32017 : checkPrefixCuts (2^48) 4200464385 9 Manual.Count131072.C032017.packed 128 cuts32017 = true := by
 decide +kernel
def pointBounds32017 : List (Nat × Nat × Nat) := [(4200485888,106054924466854,106055308254280)]
theorem point_links_checked32017 : (cuts32017.take 1).map (fun c => (4200464385-1+2*2^9*c.k,106054858461754+c.lower,106055242249142+c.upper)) = pointBounds32017 := by
 decide +kernel
def cuts32018 : List PrefixCut := [⟨22,68750371,68750410⟩,
⟨128,396348115,396348343⟩]
theorem checked32018 : checkPrefixCuts (2^48) 4200595457 9 Manual.Count131072.C032018.packed 128 cuts32018 = true := by
 decide +kernel
def pointBounds32018 : List (Nat × Nat × Nat) := [(4200617984,106055326386984,106055710174648)]
theorem point_links_checked32018 : (cuts32018.take 1).map (fun c => (4200595457-1+2*2^9*c.k,106055257636613+c.lower,106055641424238+c.upper)) = pointBounds32018 := by
 decide +kernel
def cuts32019 : List PrefixCut := [⟨23,71294442,71294483⟩,
⟨128,392784423,392784654⟩]
theorem checked32019 : checkPrefixCuts (2^48) 4200726529 9 Manual.Count131072.C032019.packed 128 cuts32019 = true := by
 decide +kernel
def pointBounds32019 : List (Nat × Nat × Nat) := [(4200750080,106055725279170,106056109067064)]
theorem point_links_checked32019 : (cuts32019.take 1).map (fun c => (4200726529-1+2*2^9*c.k,106055653984728+c.lower,106056037772581+c.upper)) = pointBounds32019 := by
 decide +kernel
def cuts32020 : List PrefixCut := [⟨24,75781474,75781513⟩,
⟨128,399740557,399740778⟩]
theorem checked32020 : checkPrefixCuts (2^48) 4200857601 9 Manual.Count131072.C032020.packed 128 cuts32020 = true := by
 decide +kernel
def pointBounds32020 : List (Nat × Nat × Nat) := [(4200882176,106056122550625,106056506338748)]
theorem point_links_checked32020 : (cuts32020.take 1).map (fun c => (4200857601-1+2*2^9*c.k,106056046769151+c.lower,106056430557235+c.upper)) = pointBounds32020 := by
 decide +kernel
def cuts32021 : List PrefixCut := [⟨25,77521148,77521191⟩,
⟨128,396512044,396512271⟩]
theorem checked32021 : checkPrefixCuts (2^48) 4200988673 9 Manual.Count131072.C032021.packed 128 cuts32021 = true := by
 decide +kernel
def pointBounds32021 : List (Nat × Nat × Nat) := [(4201014272,106056524030856,106056907819204)]
theorem point_links_checked32021 : (cuts32021.take 1).map (fun c => (4200988673-1+2*2^9*c.k,106056446509708+c.lower,106056830298013+c.upper)) = pointBounds32021 := by
 decide +kernel
def cuts32022 : List PrefixCut := [⟨26,81873706,81873752⟩,
⟨128,403199539,403199766⟩]
theorem checked32022 : checkPrefixCuts (2^48) 4201119745 9 Manual.Count131072.C032022.packed 128 cuts32022 = true := by
 decide +kernel
def pointBounds32022 : List (Nat × Nat × Nat) := [(4201146368,106056924895458,106057308684036)]
theorem point_links_checked32022 : (cuts32022.take 1).map (fun c => (4201119745-1+2*2^9*c.k,106056843021752+c.lower,106057226810284+c.upper)) = pointBounds32022 := by
 decide +kernel
def cuts32023 : List PrefixCut := [⟨27,81737138,81737189⟩,
⟨128,396554216,396554439⟩]
theorem checked32023 : checkPrefixCuts (2^48) 4201250817 9 Manual.Count131072.C032023.packed 128 cuts32023 = true := by
 decide +kernel
def pointBounds32023 : List (Nat × Nat × Nat) := [(4201278464,106057327958429,106057711747239)]
theorem point_links_checked32023 : (cuts32023.take 1).map (fun c => (4201250817-1+2*2^9*c.k,106057246221291+c.lower,106057630010050+c.upper)) = pointBounds32023 := by
 decide +kernel
def cuts32024 : List PrefixCut := [⟨28,88032170,88032218⟩,
⟨128,397077833,397078056⟩]
theorem checked32024 : checkPrefixCuts (2^48) 4201381889 9 Manual.Count131072.C032024.packed 128 cuts32024 = true := by
 decide +kernel
def pointBounds32024 : List (Nat × Nat × Nat) := [(4201410560,106057730807677,106058114596707)]
theorem point_links_checked32024 : (cuts32024.take 1).map (fun c => (4201381889-1+2*2^9*c.k,106057642775507+c.lower,106058026564489+c.upper)) = pointBounds32024 := by
 decide +kernel
def cuts32025 : List PrefixCut := [⟨29,91111107,91111155⟩,
⟨128,403898720,403898942⟩]
theorem checked32025 : checkPrefixCuts (2^48) 4201512961 9 Manual.Count131072.C032025.packed 128 cuts32025 = true := by
 decide +kernel
def pointBounds32025 : List (Nat × Nat × Nat) := [(4201542656,106058130964447,106058514753700)]
theorem point_links_checked32025 : (cuts32025.take 1).map (fun c => (4201512961-1+2*2^9*c.k,106058039853340+c.lower,106058423642545+c.upper)) = pointBounds32025 := by
 decide +kernel
def cuts32026 : List PrefixCut := [⟨30,90103384,90103438⟩,
⟨128,392631676,392631891⟩]
theorem checked32026 : checkPrefixCuts (2^48) 4201644033 9 Manual.Count131072.C032026.packed 128 cuts32026 = true := by
 decide +kernel
def pointBounds32026 : List (Nat × Nat × Nat) := [(4201674752,106058533855444,106058917644925)]
theorem point_links_checked32026 : (cuts32026.take 1).map (fun c => (4201644033-1+2*2^9*c.k,106058443752060+c.lower,106058827541487+c.upper)) = pointBounds32026 := by
 decide +kernel
def cuts32027 : List PrefixCut := [⟨31,93717983,93718038⟩,
⟨128,397777533,397777764⟩]
theorem checked32027 : checkPrefixCuts (2^48) 4201775105 9 Manual.Count131072.C032027.packed 128 cuts32027 = true := by
 decide +kernel
def pointBounds32027 : List (Nat × Nat × Nat) := [(4201806848,106058930101719,106059313891416)]
theorem point_links_checked32027 : (cuts32027.take 1).map (fun c => (4201775105-1+2*2^9*c.k,106058836383736+c.lower,106059220173378+c.upper)) = pointBounds32027 := by
 decide +kernel
def cuts32028 : List PrefixCut := [⟨32,98940047,98940105⟩,
⟨128,397430242,397430465⟩]
theorem checked32028 : checkPrefixCuts (2^48) 4201906177 9 Manual.Count131072.C032028.packed 128 cuts32028 = true := by
 decide +kernel
def pointBounds32028 : List (Nat × Nat × Nat) := [(4201938944,106059333101316,106059716891247)]
theorem point_links_checked32028 : (cuts32028.take 1).map (fun c => (4201906177-1+2*2^9*c.k,106059234161269+c.lower,106059617951142+c.upper)) = pointBounds32028 := by
 decide +kernel
def cuts32029 : List PrefixCut := [⟨33,100611577,100611638⟩,
⟨128,392327015,392327247⟩]
theorem checked32029 : checkPrefixCuts (2^48) 4202037249 9 Manual.Count131072.C032029.packed 128 cuts32029 = true := by
 decide +kernel
def pointBounds32029 : List (Nat × Nat × Nat) := [(4202071040,106059732203088,106060115993245)]
theorem point_links_checked32029 : (cuts32029.take 1).map (fun c => (4202037249-1+2*2^9*c.k,106059631591511+c.lower,106060015381607+c.upper)) = pointBounds32029 := by
 decide +kernel
def cuts32030 : List PrefixCut := [⟨34,105297236,105297296⟩,
⟨128,394860114,394860340⟩]
theorem checked32030 : checkPrefixCuts (2^48) 4202168321 9 Manual.Count131072.C032030.packed 128 cuts32030 = true := by
 decide +kernel
def pointBounds32030 : List (Nat × Nat × Nat) := [(4202203136,106060129215762,106060513006150)]
theorem point_links_checked32030 : (cuts32030.take 1).map (fun c => (4202168321-1+2*2^9*c.k,106060023918526+c.lower,106060407708854+c.upper)) = pointBounds32030 := by
 decide +kernel
def cuts32031 : List PrefixCut := [⟨35,110853356,110853415⟩,
⟨128,395249741,395249965⟩]
theorem checked32031 : checkPrefixCuts (2^48) 4202299393 9 Manual.Count131072.C032031.packed 128 cuts32031 = true := by
 decide +kernel
def pointBounds32031 : List (Nat × Nat × Nat) := [(4202335232,106060529631996,106060913422609)]
theorem point_links_checked32031 : (cuts32031.take 1).map (fun c => (4202299393-1+2*2^9*c.k,106060418778640+c.lower,106060802569194+c.upper)) = pointBounds32031 := by
 decide +kernel
def cuts32032 : List PrefixCut := [⟨36,111787580,111787639⟩,
⟨128,398653232,398653454⟩]
theorem checked32032 : checkPrefixCuts (2^48) 4202430465 9 Manual.Count131072.C032032.packed 128 cuts32032 = true := by
 decide +kernel
def pointBounds32032 : List (Nat × Nat × Nat) := [(4202467328,106060925815961,106061309606798)]
theorem point_links_checked32032 : (cuts32032.take 1).map (fun c => (4202430465-1+2*2^9*c.k,106060814028381+c.lower,106061197819159+c.upper)) = pointBounds32032 := by
 decide +kernel
def cuts32033 : List PrefixCut := [⟨37,116405478,116405544⟩,
⟨128,398171995,398172221⟩]
theorem checked32033 : checkPrefixCuts (2^48) 4202561537 9 Manual.Count131072.C032033.packed 128 cuts32033 = true := by
 decide +kernel
def pointBounds32033 : List (Nat × Nat × Nat) := [(4202599424,106061329087091,106061712878157)]
theorem point_links_checked32033 : (cuts32033.take 1).map (fun c => (4202561537-1+2*2^9*c.k,106061212681613+c.lower,106061596472613+c.upper)) = pointBounds32033 := by
 decide +kernel
def cuts32034 : List PrefixCut := [⟨38,118879895,118879966⟩,
⟨128,397021024,397021259⟩]
theorem checked32034 : checkPrefixCuts (2^48) 4202692609 9 Manual.Count131072.C032034.packed 128 cuts32034 = true := by
 decide +kernel
def pointBounds32034 : List (Nat × Nat × Nat) := [(4202731520,106061729733503,106062113524800)]
theorem point_links_checked32034 : (cuts32034.take 1).map (fun c => (4202692609-1+2*2^9*c.k,106061610853608+c.lower,106061994644834+c.upper)) = pointBounds32034 := by
 decide +kernel
def cuts32035 : List PrefixCut := [⟨39,121421124,121421193⟩,
⟨128,398147140,398147366⟩]
theorem checked32035 : checkPrefixCuts (2^48) 4202823681 9 Manual.Count131072.C032035.packed 128 cuts32035 = true := by
 decide +kernel
def pointBounds32035 : List (Nat × Nat × Nat) := [(4202863616,106062129295756,106062513087286)]
theorem point_links_checked32035 : (cuts32035.take 1).map (fun c => (4202823681-1+2*2^9*c.k,106062007874632+c.lower,106062391666093+c.upper)) = pointBounds32035 := by
 decide +kernel
def cuts32036 : List PrefixCut := [⟨40,123493400,123493470⟩,
⟨128,394317433,394317649⟩]
theorem checked32036 : checkPrefixCuts (2^48) 4202954753 9 Manual.Count131072.C032036.packed 128 cuts32036 = true := by
 decide +kernel
def pointBounds32036 : List (Nat × Nat × Nat) := [(4202995712,106062529515172,106062913306929)]
theorem point_links_checked32036 : (cuts32036.take 1).map (fun c => (4202954753-1+2*2^9*c.k,106062406021772+c.lower,106062789813459+c.upper)) = pointBounds32036 := by
 decide +kernel
def cuts32037 : List PrefixCut := [⟨41,126369179,126369253⟩,
⟨128,396381160,396381386⟩]
theorem checked32037 : checkPrefixCuts (2^48) 4203085825 9 Manual.Count131072.C032037.packed 128 cuts32037 = true := by
 decide +kernel
def pointBounds32037 : List (Nat × Nat × Nat) := [(4203127808,106062926708384,106063310500361)]
theorem point_links_checked32037 : (cuts32037.take 1).map (fun c => (4203085825-1+2*2^9*c.k,106062800339205+c.lower,106063184131108+c.upper)) = pointBounds32037 := by
 decide +kernel
def cuts32038 : List PrefixCut := [⟨42,131387687,131387763⟩,
⟨128,398310786,398311009⟩]
theorem checked32038 : checkPrefixCuts (2^48) 4203216897 9 Manual.Count131072.C032038.packed 128 cuts32038 = true := by
 decide +kernel
def pointBounds32038 : List (Nat × Nat × Nat) := [(4203259904,106063328108052,106063711900257)]
theorem point_links_checked32038 : (cuts32038.take 1).map (fun c => (4203216897-1+2*2^9*c.k,106063196720365+c.lower,106063580512494+c.upper)) = pointBounds32038 := by
 decide +kernel
def cuts32039 : List PrefixCut := [⟨43,135334444,135334522⟩,
⟨128,399168892,399169116⟩]
theorem checked32039 : checkPrefixCuts (2^48) 4203347969 9 Manual.Count131072.C032039.packed 128 cuts32039 = true := by
 decide +kernel
def pointBounds32039 : List (Nat × Nat × Nat) := [(4203392000,106063730365595,106064114158025)]
theorem point_links_checked32039 : (cuts32039.take 1).map (fun c => (4203347969-1+2*2^9*c.k,106063595031151+c.lower,106063978823503+c.upper)) = pointBounds32039 := by
 decide +kernel
def cuts32040 : List PrefixCut := [⟨44,137941733,137941810⟩,
⟨128,401767897,401768121⟩]
theorem checked32040 : checkPrefixCuts (2^48) 4203479041 9 Manual.Count131072.C032040.packed 128 cuts32040 = true := by
 decide +kernel
def pointBounds32040 : List (Nat × Nat × Nat) := [(4203524096,106064132141776,106064515934429)]
theorem point_links_checked32040 : (cuts32040.take 1).map (fun c => (4203479041-1+2*2^9*c.k,106063994200043+c.lower,106064377992619+c.upper)) = pointBounds32040 := by
 decide +kernel
def cuts32041 : List PrefixCut := [⟨45,136531254,136531334⟩,
⟨128,393653303,393653530⟩]
theorem checked32041 : checkPrefixCuts (2^48) 4203610113 9 Manual.Count131072.C032041.packed 128 cuts32041 = true := by
 decide +kernel
def pointBounds32041 : List (Nat × Nat × Nat) := [(4203656192,106064532499194,106064916292074)]
theorem point_links_checked32041 : (cuts32041.take 1).map (fun c => (4203610113-1+2*2^9*c.k,106064395967940+c.lower,106064779760740+c.upper)) = pointBounds32041 := by
 decide +kernel
def cuts32042 : List PrefixCut := [⟨46,144494968,144495051⟩,
⟨128,401475050,401475284⟩]
theorem checked32042 : checkPrefixCuts (2^48) 4203741185 9 Manual.Count131072.C032042.packed 128 cuts32042 = true := by
 decide +kernel
def pointBounds32042 : List (Nat × Nat × Nat) := [(4203788288,106064934116211,106065317909321)]
theorem point_links_checked32042 : (cuts32042.take 1).map (fun c => (4203741185-1+2*2^9*c.k,106064789621243+c.lower,106065173414270+c.upper)) = pointBounds32042 := by
 decide +kernel
def cuts32043 : List PrefixCut := [⟨47,143820890,143820973⟩,
⟨128,393829656,393829885⟩]
theorem checked32043 : checkPrefixCuts (2^48) 4203872257 9 Manual.Count131072.C032043.packed 128 cuts32043 = true := by
 decide +kernel
def pointBounds32043 : List (Nat × Nat × Nat) := [(4203920384,106065334917183,106065718710527)]
theorem point_links_checked32043 : (cuts32043.take 1).map (fun c => (4203872257-1+2*2^9*c.k,106065191096293+c.lower,106065574889554+c.upper)) = pointBounds32043 := by
 decide +kernel
def cuts32044 : List PrefixCut := [⟨48,148503143,148503228⟩,
⟨128,395491203,395491424⟩]
theorem checked32044 : checkPrefixCuts (2^48) 4204003329 9 Manual.Count131072.C032044.packed 128 cuts32044 = true := by
 decide +kernel
def pointBounds32044 : List (Nat × Nat × Nat) := [(4204052480,106065733429092,106066117222667)]
theorem point_links_checked32044 : (cuts32044.take 1).map (fun c => (4204003329-1+2*2^9*c.k,106065584925949+c.lower,106065968719439+c.upper)) = pointBounds32044 := by
 decide +kernel
def cuts32045 : List PrefixCut := [⟨49,151578251,151578336⟩,
⟨128,397286546,397286766⟩]
theorem checked32045 : checkPrefixCuts (2^48) 4204134401 9 Manual.Count131072.C032045.packed 128 cuts32045 = true := by
 decide +kernel
def pointBounds32045 : List (Nat × Nat × Nat) := [(4204184576,106066131995403,106066515789199)]
theorem point_links_checked32045 : (cuts32045.take 1).map (fun c => (4204134401-1+2*2^9*c.k,106065980417152+c.lower,106066364210863+c.upper)) = pointBounds32045 := by
 decide +kernel
def cuts32046 : List PrefixCut := [⟨50,157465052,157465144⟩,
⟨128,400487702,400487930⟩]
theorem checked32046 : checkPrefixCuts (2^48) 4204265473 9 Manual.Count131072.C032046.packed 128 cuts32046 = true := by
 decide +kernel
def pointBounds32046 : List (Nat × Nat × Nat) := [(4204316672,106066535168750,106066918962773)]
theorem point_links_checked32046 : (cuts32046.take 1).map (fun c => (4204265473-1+2*2^9*c.k,106066377703698+c.lower,106066761497629+c.upper)) = pointBounds32046 := by
 decide +kernel
def cuts32047 : List PrefixCut := [⟨51,158932977,158933072⟩,
⟨128,399270160,399270392⟩]
theorem checked32047 : checkPrefixCuts (2^48) 4204396545 9 Manual.Count131072.C032047.packed 128 cuts32047 = true := by
 decide +kernel
def pointBounds32047 : List (Nat × Nat × Nat) := [(4204448768,106066937124377,106067320918631)]
theorem point_links_checked32047 : (cuts32047.take 1).map (fun c => (4204396545-1+2*2^9*c.k,106066778191400+c.lower,106067161985559+c.upper)) = pointBounds32047 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S4.B000063
