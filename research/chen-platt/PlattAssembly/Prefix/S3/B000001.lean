import PlattAssemblyKernel
import PlattCertificates.Count131072.C020032
import PlattCertificates.Count131072.C020033
import PlattCertificates.Count131072.C020034
import PlattCertificates.Count131072.C020035
import PlattCertificates.Count131072.C020036
import PlattCertificates.Count131072.C020037
import PlattCertificates.Count131072.C020038
import PlattCertificates.Count131072.C020039
import PlattCertificates.Count131072.C020040
import PlattCertificates.Count131072.C020041
import PlattCertificates.Count131072.C020042
import PlattCertificates.Count131072.C020043
import PlattCertificates.Count131072.C020044
import PlattCertificates.Count131072.C020045
import PlattCertificates.Count131072.C020046
import PlattCertificates.Count131072.C020047
import PlattCertificates.Count131072.C020048
import PlattCertificates.Count131072.C020049
import PlattCertificates.Count131072.C020050
import PlattCertificates.Count131072.C020051
import PlattCertificates.Count131072.C020052
import PlattCertificates.Count131072.C020053
import PlattCertificates.Count131072.C020054
import PlattCertificates.Count131072.C020055
import PlattCertificates.Count131072.C020056
import PlattCertificates.Count131072.C020057
import PlattCertificates.Count131072.C020058
import PlattCertificates.Count131072.C020059
import PlattCertificates.Count131072.C020060
import PlattCertificates.Count131072.C020061
import PlattCertificates.Count131072.C020062
import PlattCertificates.Count131072.C020063
namespace ChenEffective.PlattWindow.Assembly.Prefix.S3.B000001
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts20032 : List PrefixCut := [⟨47,234420538,234420680⟩,
⟨128,648767227,648767616⟩]
theorem checked20032 : checkPrefixCuts (2^48) 2629566465 9 Manual.Count131072.C020032.packed 128 cuts20032 = true := by
 decide +kernel
def pointBounds20032 : List (Nat × Nat × Nat) := [(2629614592,100041805124840,100042185506898),(2629697536,100042219471529,100042599853834)]
theorem point_links_checked20032 : (cuts20032.take 2).map (fun c => (2629566465-1+2*2^9*c.k,100041570704302+c.lower,100041951086218+c.upper)) = pointBounds20032 := by
 decide +kernel
def cuts20033 : List PrefixCut := [⟨81,410052235,410052476⟩,
⟨128,642420085,642420466⟩]
theorem checked20033 : checkPrefixCuts (2^48) 2629697537 9 Manual.Count131072.C020033.packed 128 cuts20033 = true := by
 decide +kernel
def pointBounds20033 : List (Nat × Nat × Nat) := [(2629780480,100042629523764,100043009906310)]
theorem point_links_checked20033 : (cuts20033.take 1).map (fun c => (2629697537-1+2*2^9*c.k,100042219471529+c.lower,100042599853834+c.upper)) = pointBounds20033 := by
 decide +kernel
def cuts20034 : List PrefixCut := [⟨34,170821368,170821470⟩,
⟨115,584058609,584058955⟩,
⟨128,647846456,647846838⟩]
theorem checked20034 : checkPrefixCuts (2^48) 2629828609 9 Manual.Count131072.C020034.packed 128 cuts20034 = true := by
 decide +kernel
def pointBounds20034 : List (Nat × Nat × Nat) := [(2629863424,100043032712982,100043413095770),(2629946368,100043445950223,100043826333255)]
theorem point_links_checked20034 : (cuts20034.take 2).map (fun c => (2629828609-1+2*2^9*c.k,100042861891614+c.lower,100043242274300+c.upper)) = pointBounds20034 := by
 decide +kernel
def cuts20035 : List PrefixCut := [⟨68,342693758,342693960⟩,
⟨128,644175404,644175777⟩]
theorem checked20035 : checkPrefixCuts (2^48) 2629959681 9 Manual.Count131072.C020035.packed 128 cuts20035 = true := by
 decide +kernel
def pointBounds20035 : List (Nat × Nat × Nat) := [(2630029312,100043852431828,100044232815098)]
theorem point_links_checked20035 : (cuts20035.take 1).map (fun c => (2629959681-1+2*2^9*c.k,100043509738070+c.lower,100043890121138+c.upper)) = pointBounds20035 := by
 decide +kernel
def cuts20036 : List PrefixCut := [⟨21,109803071,109803134⟩,
⟨102,517222172,517222476⟩,
⟨128,646818793,646819173⟩]
theorem checked20036 : checkPrefixCuts (2^48) 2630090753 9 Manual.Count131072.C020036.packed 128 cuts20036 = true := by
 decide +kernel
def pointBounds20036 : List (Nat × Nat × Nat) := [(2630112256,100044263716545,100044644100049),(2630195200,100044671135646,100045051519391)]
theorem point_links_checked20036 : (cuts20036.take 2).map (fun c => (2630090753-1+2*2^9*c.k,100044153913474+c.lower,100044534296915+c.upper)) = pointBounds20036 := by
 decide +kernel
def cuts20037 : List PrefixCut := [⟨55,274278179,274278340⟩,
⟨128,647535550,647535925⟩]
theorem checked20037 : checkPrefixCuts (2^48) 2630221825 9 Manual.Count131072.C020037.packed 128 cuts20037 = true := by
 decide +kernel
def pointBounds20037 : List (Nat × Nat × Nat) := [(2630278144,100045075010446,100045455394428)]
theorem point_links_checked20037 : (cuts20037.take 1).map (fun c => (2630221825-1+2*2^9*c.k,100044800732267+c.lower,100045181116088+c.upper)) = pointBounds20037 := by
 decide +kernel
def cuts20038 : List PrefixCut := [⟨8,37346539,37346563⟩,
⟨89,445690184,445690446⟩,
⟨128,643008868,643009243⟩]
theorem checked20038 : checkPrefixCuts (2^48) 2630352897 9 Manual.Count131072.C020038.packed 128 cuts20038 = true := by
 decide +kernel
def pointBounds20038 : List (Nat × Nat × Nat) := [(2630361088,100045485614356,100045865998576),(2630444032,100045893958001,100046274342459)]
theorem point_links_checked20038 : (cuts20038.take 2).map (fun c => (2630352897-1+2*2^9*c.k,100045448267817+c.lower,100045828652013+c.upper)) = pointBounds20038 := by
 decide +kernel
def cuts20039 : List PrefixCut := [⟨42,218930403,218930528⟩,
⟨123,628211319,628211687⟩,
⟨128,654212260,654212643⟩]
theorem checked20039 : checkPrefixCuts (2^48) 2630483969 9 Manual.Count131072.C020039.packed 128 cuts20039 = true := by
 decide +kernel
def pointBounds20039 : List (Nat × Nat × Nat) := [(2630526976,100046310207088,100046690591784),(2630609920,100046719488004,100047099872943)]
theorem point_links_checked20039 : (cuts20039.take 2).map (fun c => (2630483969-1+2*2^9*c.k,100046091276685+c.lower,100046471661256+c.upper)) = pointBounds20039 := by
 decide +kernel
def cuts20040 : List PrefixCut := [⟨76,387333021,387333251⟩,
⟨128,650755671,650756053⟩]
theorem checked20040 : checkPrefixCuts (2^48) 2630615041 9 Manual.Count131072.C020040.packed 128 cuts20040 = true := by
 decide +kernel
def pointBounds20040 : List (Nat × Nat × Nat) := [(2630692864,100047132821966,100047513207150)]
theorem point_links_checked20040 : (cuts20040.take 1).map (fun c => (2630615041-1+2*2^9*c.k,100046745488945+c.lower,100047125873899+c.upper)) = pointBounds20040 := by
 decide +kernel
def cuts20041 : List PrefixCut := [⟨29,148400282,148400368⟩,
⟨110,559247341,559247663⟩,
⟨128,651472179,651472556⟩]
theorem checked20041 : checkPrefixCuts (2^48) 2630746113 9 Manual.Count131072.C020041.packed 128 cuts20041 = true := by
 decide +kernel
def pointBounds20041 : List (Nat × Nat × Nat) := [(2630775808,100047544644898,100047925030320),(2630858752,100047955491957,100048335877615)]
theorem point_links_checked20041 : (cuts20041.take 2).map (fun c => (2630746113-1+2*2^9*c.k,100047396244616+c.lower,100047776629952+c.upper)) = pointBounds20041 := by
 decide +kernel
def cuts20042 : List PrefixCut := [⟨63,324600635,324600823⟩,
⟨128,652830662,652831043⟩]
theorem checked20042 : checkPrefixCuts (2^48) 2630877185 9 Manual.Count131072.C020042.packed 128 cuts20042 = true := by
 decide +kernel
def pointBounds20042 : List (Nat × Nat × Nat) := [(2630941696,100048372317430,100048752703331)]
theorem point_links_checked20042 : (cuts20042.take 1).map (fun c => (2630877185-1+2*2^9*c.k,100048047716795+c.lower,100048428102508+c.upper)) = pointBounds20042 := by
 decide +kernel
def cuts20043 : List PrefixCut := [⟨16,82805086,82805135⟩,
⟨97,491366738,491367029⟩,
⟨128,649588638,649589022⟩]
theorem checked20043 : checkPrefixCuts (2^48) 2631008257 9 Manual.Count131072.C020043.packed 128 cuts20043 = true := by
 decide +kernel
def pointBounds20043 : List (Nat × Nat × Nat) := [(2631024640,100048783352543,100049163738686),(2631107584,100049191914195,100049572300580)]
theorem point_links_checked20043 : (cuts20043.take 2).map (fun c => (2631008257-1+2*2^9*c.k,100048700547457+c.lower,100049080933551+c.upper)) = pointBounds20043 := by
 decide +kernel
def cuts20044 : List PrefixCut := [⟨50,253536222,253536371⟩,
⟨128,645491294,645491670⟩]
theorem checked20044 : checkPrefixCuts (2^48) 2631139329 9 Manual.Count131072.C020044.packed 128 cuts20044 = true := by
 decide +kernel
def pointBounds20044 : List (Nat × Nat × Nat) := [(2631190528,100049603672317,100049984058944)]
theorem point_links_checked20044 : (cuts20044.take 1).map (fun c => (2631139329-1+2*2^9*c.k,100049350136095+c.lower,100049730522573+c.upper)) = pointBounds20044 := by
 decide +kernel
def cuts20045 : List PrefixCut := [⟨3,15831996,15832004⟩,
⟨84,427457162,427457413⟩,
⟨128,650165792,650166171⟩]
theorem checked20045 : checkPrefixCuts (2^48) 2631270401 9 Manual.Count131072.C020045.packed 128 cuts20045 = true := by
 decide +kernel
def pointBounds20045 : List (Nat × Nat × Nat) := [(2631273472,100050011459385,100050391846247),(2631356416,100050423084551,100050803471656)]
theorem point_links_checked20045 : (cuts20045.take 2).map (fun c => (2631270401-1+2*2^9*c.k,100049995627389+c.lower,100050376014243+c.upper)) = pointBounds20045 := by
 decide +kernel
def cuts20046 : List PrefixCut := [⟨37,185052747,185052856⟩,
⟨118,595903166,595903514⟩,
⟨128,649063558,649063936⟩]
theorem checked20046 : checkPrefixCuts (2^48) 2631401473 9 Manual.Count131072.C020046.packed 128 cuts20046 = true := by
 decide +kernel
def pointBounds20046 : List (Nat × Nat × Nat) := [(2631439360,100050830845928,100051211233270),(2631522304,100051241696347,100051622083928)]
theorem point_links_checked20046 : (cuts20046.take 2).map (fun c => (2631401473-1+2*2^9*c.k,100050645793181+c.lower,100051026180414+c.upper)) = pointBounds20046 := by
 decide +kernel
def cuts20047 : List PrefixCut := [⟨71,360351132,360351344⟩,
⟨128,649566098,649566478⟩]
theorem checked20047 : checkPrefixCuts (2^48) 2631532545 9 Manual.Count131072.C020047.packed 128 cuts20047 = true := by
 decide +kernel
def pointBounds20047 : List (Nat × Nat × Nat) := [(2631605248,100051655207871,100052035595694)]
theorem point_links_checked20047 : (cuts20047.take 1).map (fun c => (2631532545-1+2*2^9*c.k,100051294856739+c.lower,100051675244350+c.upper)) = pointBounds20047 := by
 decide +kernel
def cuts20048 : List PrefixCut := [⟨24,119149564,119149635⟩,
⟨105,533490707,533491021⟩,
⟨128,649106000,649106380⟩]
theorem checked20048 : checkPrefixCuts (2^48) 2631663617 9 Manual.Count131072.C020048.packed 128 cuts20048 = true := by
 decide +kernel
def pointBounds20048 : List (Nat × Nat × Nat) := [(2631688192,100052063572401,100052443960463),(2631771136,100052477913544,100052858301849)]
theorem point_links_checked20048 : (cuts20048.take 2).map (fun c => (2631663617-1+2*2^9*c.k,100051944422837+c.lower,100052324810828+c.upper)) = pointBounds20048 := by
 decide +kernel
def cuts20049 : List PrefixCut := [⟨58,291440053,291440224⟩,
⟨128,642656703,642657078⟩]
theorem checked20049 : checkPrefixCuts (2^48) 2631794689 9 Manual.Count131072.C020049.packed 128 cuts20049 = true := by
 decide +kernel
def pointBounds20049 : List (Nat × Nat × Nat) := [(2631854080,100052884968890,100053265357432)]
theorem point_links_checked20049 : (cuts20049.take 1).map (fun c => (2631794689-1+2*2^9*c.k,100052593528837+c.lower,100052973917208+c.upper)) = pointBounds20049 := by
 decide +kernel
def cuts20050 : List PrefixCut := [⟨11,53366120,53366152⟩,
⟨92,462320822,462321095⟩,
⟨128,645619053,645619434⟩]
theorem checked20050 : checkPrefixCuts (2^48) 2631925761 9 Manual.Count131072.C020050.packed 128 cuts20050 = true := by
 decide +kernel
def pointBounds20050 : List (Nat × Nat × Nat) := [(2631937024,100053289551660,100053669940438),(2632019968,100053698506362,100054078895381)]
theorem point_links_checked20050 : (cuts20050.take 2).map (fun c => (2631925761-1+2*2^9*c.k,100053236185540+c.lower,100053616574286+c.upper)) = pointBounds20050 := by
 decide +kernel
def cuts20051 : List PrefixCut := [⟨45,225643587,225643722⟩,
⟨126,634572519,634572897⟩,
⟨128,645266095,645266478⟩]
theorem checked20051 : checkPrefixCuts (2^48) 2632056833 9 Manual.Count131072.C020051.packed 128 cuts20051 = true := by
 decide +kernel
def pointBounds20051 : List (Nat × Nat × Nat) := [(2632102912,100054107448180,100054487837442),(2632185856,100054516377112,100054896766617)]
theorem point_links_checked20051 : (cuts20051.take 2).map (fun c => (2632056833-1+2*2^9*c.k,100053881804593+c.lower,100054262193720+c.upper)) = pointBounds20051 := by
 decide +kernel
def cuts20052 : List PrefixCut := [⟨79,412765459,412765700⟩,
⟨128,656996781,656997168⟩]
theorem checked20052 : checkPrefixCuts (2^48) 2632187905 9 Manual.Count131072.C020052.packed 128 cuts20052 = true := by
 decide +kernel
def pointBounds20052 : List (Nat × Nat × Nat) := [(2632268800,100054939836147,100055320225898)]
theorem point_links_checked20052 : (cuts20052.take 1).map (fun c => (2632187905-1+2*2^9*c.k,100054527070688+c.lower,100054907460198+c.upper)) = pointBounds20052 := by
 decide +kernel
def cuts20053 : List PrefixCut := [⟨32,157079765,157079856⟩,
⟨113,565328507,565328842⟩,
⟨128,639107016,639107395⟩]
theorem checked20053 : checkPrefixCuts (2^48) 2632318977 9 Manual.Count131072.C020053.packed 128 cuts20053 = true := by
 decide +kernel
def pointBounds20053 : List (Nat × Nat × Nat) := [(2632351744,100055341147234,100055721537222),(2632434688,100055749395976,100056129786208)]
theorem point_links_checked20053 : (cuts20053.take 2).map (fun c => (2632318977-1+2*2^9*c.k,100055184067469+c.lower,100055564457366+c.upper)) = pointBounds20053 := by
 decide +kernel
def cuts20054 : List PrefixCut := [⟨66,333708863,333709051⟩,
⟨128,651264392,651264767⟩]
theorem checked20054 : checkPrefixCuts (2^48) 2632450049 9 Manual.Count131072.C020054.packed 128 cuts20054 = true := by
 decide +kernel
def pointBounds20054 : List (Nat × Nat × Nat) := [(2632517632,100056156883348,100056537273812)]
theorem point_links_checked20054 : (cuts20054.take 1).map (fun c => (2632450049-1+2*2^9*c.k,100055823174485+c.lower,100056203564761+c.upper)) = pointBounds20054 := by
 decide +kernel
def cuts20055 : List PrefixCut := [⟨19,90346858,90346908⟩,
⟨100,501871384,501871684⟩,
⟨128,643213004,643213387⟩]
theorem checked20055 : checkPrefixCuts (2^48) 2632581121 9 Manual.Count131072.C020055.packed 128 cuts20055 = true := by
 decide +kernel
def pointBounds20055 : List (Nat × Nat × Nat) := [(2632600576,100056564785735,100056945176436),(2632683520,100056976310261,100057356701212)]
theorem point_links_checked20055 : (cuts20055.take 2).map (fun c => (2632581121-1+2*2^9*c.k,100056474438877+c.lower,100056854829528+c.upper)) = pointBounds20055 := by
 decide +kernel
def cuts20056 : List PrefixCut := [⟨53,270063028,270063185⟩,
⟨128,647885345,647885724⟩]
theorem checked20056 : checkPrefixCuts (2^48) 2632712193 9 Manual.Count131072.C020056.packed 128 cuts20056 = true := by
 decide +kernel
def pointBounds20056 : List (Nat × Nat × Nat) := [(2632766464,100057387714909,100057768106100)]
theorem point_links_checked20056 : (cuts20056.take 1).map (fun c => (2632712193-1+2*2^9*c.k,100057117651881+c.lower,100057498042915+c.upper)) = pointBounds20056 := by
 decide +kernel
def cuts20057 : List PrefixCut := [⟨6,30789786,30789803⟩,
⟨87,437250775,437251030⟩,
⟨128,643149082,643149457⟩]
theorem checked20057 : checkPrefixCuts (2^48) 2632843265 9 Manual.Count131072.C020057.packed 128 cuts20057 = true := by
 decide +kernel
def pointBounds20057 : List (Nat × Nat × Nat) := [(2632849408,100057796327012,100058176718442),(2632932352,100058202788001,100058583179669)]
theorem point_links_checked20057 : (cuts20057.take 2).map (fun c => (2632843265-1+2*2^9*c.k,100057765537226+c.lower,100058145928639+c.upper)) = pointBounds20057 := by
 decide +kernel
def cuts20058 : List PrefixCut := [⟨40,195525486,195525601⟩,
⟨121,603671282,603671632⟩,
⟨128,637878833,637879203⟩]
theorem checked20058 : checkPrefixCuts (2^48) 2632974337 9 Manual.Count131072.C020058.packed 128 cuts20058 = true := by
 decide +kernel
def pointBounds20058 : List (Nat × Nat × Nat) := [(2633015296,100058604211794,100058984603697),(2633098240,100059012357590,100059392749728)]
theorem point_links_checked20058 : (cuts20058.take 2).map (fun c => (2632974337-1+2*2^9*c.k,100058408686308+c.lower,100058789078096+c.upper)) = pointBounds20058 := by
 decide +kernel
def cuts20059 : List PrefixCut := [⟨74,369863302,369863516⟩,
⟨128,637419645,637420018⟩]
theorem checked20059 : checkPrefixCuts (2^48) 2633105409 9 Manual.Count131072.C020059.packed 128 cuts20059 = true := by
 decide +kernel
def pointBounds20059 : List (Nat × Nat × Nat) := [(2633181184,100059416428443,100059796820815)]
theorem point_links_checked20059 : (cuts20059.take 1).map (fun c => (2633105409-1+2*2^9*c.k,100059046565141+c.lower,100059426957299+c.upper)) = pointBounds20059 := by
 decide +kernel
def cuts20060 : List PrefixCut := [⟨27,135539780,135539861⟩,
⟨108,542791868,542792187⟩,
⟨128,647756126,647756506⟩]
theorem checked20060 : checkPrefixCuts (2^48) 2633236481 9 Manual.Count131072.C020060.packed 128 cuts20060 = true := by
 decide +kernel
def pointBounds20060 : List (Nat × Nat × Nat) := [(2633264128,100059819524566,100060199917178),(2633347072,100060226776654,100060607169504)]
theorem point_links_checked20060 : (cuts20060.take 2).map (fun c => (2633236481-1+2*2^9*c.k,100059683984786+c.lower,100060064377317+c.upper)) = pointBounds20060 := by
 decide +kernel
def cuts20061 : List PrefixCut := [⟨61,309543431,309543608⟩,
⟨128,650930590,650930967⟩]
theorem checked20061 : checkPrefixCuts (2^48) 2633367553 9 Manual.Count131072.C020061.packed 128 cuts20061 = true := by
 decide +kernel
def pointBounds20061 : List (Nat × Nat × Nat) := [(2633430016,100060641284343,100061021677431)]
theorem point_links_checked20061 : (cuts20061.take 1).map (fun c => (2633367553-1+2*2^9*c.k,100060331740912+c.lower,100060712133823+c.upper)) = pointBounds20061 := by
 decide +kernel
def cuts20062 : List PrefixCut := [⟨14,70328489,70328530⟩,
⟨95,477649091,477649364⟩,
⟨128,647050519,647050891⟩]
theorem checked20062 : checkPrefixCuts (2^48) 2633498625 9 Manual.Count131072.C020062.packed 128 cuts20062 = true := by
 decide +kernel
def pointBounds20062 : List (Nat × Nat × Nat) := [(2633512960,100061052999991,100061433393320),(2633595904,100061460320593,100061840714154)]
theorem point_links_checked20062 : (cuts20062.take 2).map (fun c => (2633498625-1+2*2^9*c.k,100060982671502+c.lower,100061363064790+c.upper)) = pointBounds20062 := by
 decide +kernel
def cuts20063 : List PrefixCut := [⟨48,242715802,242715944⟩,
⟨128,652789495,652789875⟩]
theorem checked20063 : checkPrefixCuts (2^48) 2633629697 9 Manual.Count131072.C020063.packed 128 cuts20063 = true := by
 decide +kernel
def pointBounds20063 : List (Nat × Nat × Nat) := [(2633678848,100061872437823,100062252831625)]
theorem point_links_checked20063 : (cuts20063.take 1).map (fun c => (2633629697-1+2*2^9*c.k,100061629722021+c.lower,100062010115681+c.upper)) = pointBounds20063 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S3.B000001
