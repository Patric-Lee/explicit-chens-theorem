import PlattAssemblyKernel
import PlattCertificates.Count131072.C019024
import PlattCertificates.Count131072.C019025
import PlattCertificates.Count131072.C019026
import PlattCertificates.Count131072.C019027
import PlattCertificates.Count131072.C019028
import PlattCertificates.Count131072.C019029
import PlattCertificates.Count131072.C019030
import PlattCertificates.Count131072.C019031
import PlattCertificates.Count131072.C019032
import PlattCertificates.Count131072.C019033
import PlattCertificates.Count131072.C019034
import PlattCertificates.Count131072.C019035
import PlattCertificates.Count131072.C019036
import PlattCertificates.Count131072.C019037
import PlattCertificates.Count131072.C019038
import PlattCertificates.Count131072.C019039
import PlattCertificates.Count131072.C019040
import PlattCertificates.Count131072.C019041
import PlattCertificates.Count131072.C019042
import PlattCertificates.Count131072.C019043
import PlattCertificates.Count131072.C019044
import PlattCertificates.Count131072.C019045
import PlattCertificates.Count131072.C019046
import PlattCertificates.Count131072.C019047
import PlattCertificates.Count131072.C019048
import PlattCertificates.Count131072.C019049
import PlattCertificates.Count131072.C019050
import PlattCertificates.Count131072.C019051
import PlattCertificates.Count131072.C019052
import PlattCertificates.Count131072.C019053
import PlattCertificates.Count131072.C019054
import PlattCertificates.Count131072.C019055
namespace ChenEffective.PlattWindow.Assembly.Prefix.S2.B000282
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts19024 : List PrefixCut := [⟨56,297087273,297087450⟩,
⟨128,679819413,679819812⟩]
theorem checked19024 : checkPrefixCuts (2^48) 2497445889 9 Manual.Count131072.C019024.packed 128 cuts19024 = true := by
 decide +kernel
def pointBounds19024 : List (Nat × Nat × Nat) := [(2497503232,99371961423268,99372341408387)]
theorem point_links_checked19024 : (cuts19024.take 1).map (fun c => (2497445889-1+2*2^9*c.k,99371664335995+c.lower,99372044320937+c.upper)) = pointBounds19024 := by
 decide +kernel
def cuts19025 : List PrefixCut := [⟨5,23441404,23441419⟩,
⟨82,438505032,438505297⟩,
⟨128,683615207,683615614⟩]
theorem checked19025 : checkPrefixCuts (2^48) 2497576961 9 Manual.Count131072.C019025.packed 128 cuts19025 = true := by
 decide +kernel
def pointBounds19025 : List (Nat × Nat × Nat) := [(2497582080,99372367596812,99372747582168),(2497660928,99372782660440,99373162646046)]
theorem point_links_checked19025 : (cuts19025.take 2).map (fun c => (2497576961-1+2*2^9*c.k,99372344155408+c.lower,99372724140749+c.upper)) = pointBounds19025 := by
 decide +kernel
def cuts19026 : List PrefixCut := [⟨31,166784985,166785082⟩,
⟨108,578103722,578104064⟩,
⟨128,678057812,678058215⟩]
theorem checked19026 : checkPrefixCuts (2^48) 2497708033 9 Manual.Count131072.C019026.packed 128 cuts19026 = true := by
 decide +kernel
def pointBounds19026 : List (Nat × Nat × Nat) := [(2497739776,99373194555600,99373574541445),(2497818624,99373605874337,99373985860427)]
theorem point_links_checked19026 : (cuts19026.take 2).map (fun c => (2497708033-1+2*2^9*c.k,99373027770615+c.lower,99373407756363+c.upper)) = pointBounds19026 := by
 decide +kernel
def cuts19027 : List PrefixCut := [⟨57,305266543,305266725⟩,
⟨128,680388547,680388952⟩]
theorem checked19027 : checkPrefixCuts (2^48) 2497839105 9 Manual.Count131072.C019027.packed 128 cuts19027 = true := by
 decide +kernel
def pointBounds19027 : List (Nat × Nat × Nat) := [(2497897472,99374011094970,99374391081303)]
theorem point_links_checked19027 : (cuts19027.take 1).map (fun c => (2497839105-1+2*2^9*c.k,99373705828427+c.lower,99374085814578+c.upper)) = pointBounds19027 := by
 decide +kernel
def cuts19028 : List PrefixCut := [⟨6,32902943,32902963⟩,
⟨83,446661643,446661912⟩,
⟨128,685648627,685649038⟩]
theorem checked19028 : checkPrefixCuts (2^48) 2497970177 9 Manual.Count131072.C019028.packed 128 cuts19028 = true := by
 decide +kernel
def pointBounds19028 : List (Nat × Nat × Nat) := [(2497976320,99374419119917,99374799106493),(2498055168,99374832878617,99375212865442)]
theorem point_links_checked19028 : (cuts19028.take 2).map (fun c => (2497970177-1+2*2^9*c.k,99374386216974+c.lower,99374766203530+c.upper)) = pointBounds19028 := by
 decide +kernel
def cuts19029 : List PrefixCut := [⟨32,170702313,170702411⟩,
⟨109,578688689,578689029⟩,
⟨128,682345153,682345555⟩]
theorem checked19029 : checkPrefixCuts (2^48) 2498101249 9 Manual.Count131072.C019029.packed 128 cuts19029 = true := by
 decide +kernel
def pointBounds19029 : List (Nat × Nat × Nat) := [(2498134016,99375242567914,99375622554979),(2498212864,99375650554290,99376030541597)]
theorem point_links_checked19029 : (cuts19029.take 2).map (fun c => (2498101249-1+2*2^9*c.k,99375071865601+c.lower,99375451852568+c.upper)) = pointBounds19029 := by
 decide +kernel
def cuts19030 : List PrefixCut := [⟨58,307697029,307697214⟩,
⟨128,679267307,679267713⟩]
theorem checked19030 : checkPrefixCuts (2^48) 2498232321 9 Manual.Count131072.C019030.packed 128 cuts19030 = true := by
 decide +kernel
def pointBounds19030 : List (Nat × Nat × Nat) := [(2498291712,99376061907783,99376441895337)]
theorem point_links_checked19030 : (cuts19030.take 1).map (fun c => (2498232321-1+2*2^9*c.k,99375754210754+c.lower,99376134198123+c.upper)) = pointBounds19030 := by
 decide +kernel
def cuts19031 : List PrefixCut := [⟨7,35489017,35489039⟩,
⟨84,449069789,449070062⟩,
⟨128,683625442,683625851⟩]
theorem checked19031 : checkPrefixCuts (2^48) 2498363393 9 Manual.Count131072.C019031.packed 128 cuts19031 = true := by
 decide +kernel
def pointBounds19031 : List (Nat × Nat × Nat) := [(2498370560,99376468967078,99376848954875),(2498449408,99376882547850,99377262535898)]
theorem point_links_checked19031 : (cuts19031.take 2).map (fun c => (2498363393-1+2*2^9*c.k,99376433478061+c.lower,99376813465836+c.upper)) = pointBounds19031 := by
 decide +kernel
def cuts19032 : List PrefixCut := [⟨33,175857648,175857755⟩,
⟨110,590764201,590764556⟩,
⟨128,686969279,686969690⟩]
theorem checked19032 : checkPrefixCuts (2^48) 2498494465 9 Manual.Count131072.C019032.packed 128 cuts19032 = true := by
 decide +kernel
def pointBounds19032 : List (Nat × Nat × Nat) := [(2498528256,99377292961151,99377672949442),(2498607104,99377707867704,99378087856243)]
theorem point_links_checked19032 : (cuts19032.take 2).map (fun c => (2498494465-1+2*2^9*c.k,99377117103503+c.lower,99377497091687+c.upper)) = pointBounds19032 := by
 decide +kernel
def cuts19033 : List PrefixCut := [⟨59,312492577,312492762⟩,
⟨128,680174269,680174674⟩]
theorem checked19033 : checkPrefixCuts (2^48) 2498625537 9 Manual.Count131072.C019033.packed 128 cuts19033 = true := by
 decide +kernel
def pointBounds19033 : List (Nat × Nat × Nat) := [(2498685952,99378116565359,99378496554139)]
theorem point_links_checked19033 : (cuts19033.take 1).map (fun c => (2498625537-1+2*2^9*c.k,99377804072782+c.lower,99378184061377+c.upper)) = pointBounds19033 := by
 decide +kernel
def cuts19034 : List PrefixCut := [⟨8,42918047,42918072⟩,
⟨85,454293319,454293587⟩,
⟨128,677322628,677323032⟩]
theorem checked19034 : checkPrefixCuts (2^48) 2498756609 9 Manual.Count131072.C019034.packed 128 cuts19034 = true := by
 decide +kernel
def pointBounds19034 : List (Nat × Nat × Nat) := [(2498764800,99378527165098,99378907154123),(2498843648,99378938540370,99379318529638)]
theorem point_links_checked19034 : (cuts19034.take 2).map (fun c => (2498756609-1+2*2^9*c.k,99378484247051+c.lower,99378864236051+c.upper)) = pointBounds19034 := by
 decide +kernel
def cuts19035 : List PrefixCut := [⟨34,174590896,174591003⟩,
⟨111,589094082,589094437⟩,
⟨128,676723761,676724170⟩]
theorem checked19035 : checkPrefixCuts (2^48) 2498887681 9 Manual.Count131072.C019035.packed 128 cuts19035 = true := by
 decide +kernel
def pointBounds19035 : List (Nat × Nat × Nat) := [(2498922496,99379336160575,99379716150086),(2499001344,99379750663761,99380130653520)]
theorem point_links_checked19035 : (cuts19035.take 2).map (fun c => (2498887681-1+2*2^9*c.k,99379161569679+c.lower,99379541559083+c.upper)) = pointBounds19035 := by
 decide +kernel
def cuts19036 : List PrefixCut := [⟨60,331590891,331591090⟩,
⟨128,696736739,696737155⟩]
theorem checked19036 : checkPrefixCuts (2^48) 2499018753 9 Manual.Count131072.C019036.packed 128 cuts19036 = true := by
 decide +kernel
def pointBounds19036 : List (Nat × Nat × Nat) := [(2499080192,99380169884331,99380549874343)]
theorem point_links_checked19036 : (cuts19036.take 1).map (fun c => (2499018753-1+2*2^9*c.k,99379838293440+c.lower,99380218283253+c.upper)) = pointBounds19036 := by
 decide +kernel
def cuts19037 : List PrefixCut := [⟨9,50457369,50457399⟩,
⟨86,459177327,459177599⟩,
⟨128,681946248,681946650⟩]
theorem checked19037 : checkPrefixCuts (2^48) 2499149825 9 Manual.Count131072.C019037.packed 128 cuts19037 = true := by
 decide +kernel
def pointBounds19037 : List (Nat × Nat × Nat) := [(2499159040,99380585487548,99380965477807),(2499237888,99380994207506,99381374198007)]
theorem point_links_checked19037 : (cuts19037.take 2).map (fun c => (2499149825-1+2*2^9*c.k,99380535030179+c.lower,99380915020408+c.upper)) = pointBounds19037 := by
 decide +kernel
def cuts19038 : List PrefixCut := [⟨35,191006144,191006257⟩,
⟨112,594182066,594182420⟩,
⟨128,680333931,680334335⟩]
theorem checked19038 : checkPrefixCuts (2^48) 2499280897 9 Manual.Count131072.C019038.packed 128 cuts19038 = true := by
 decide +kernel
def pointBounds19038 : List (Nat × Nat × Nat) := [(2499316736,99381407982571,99381787973315),(2499395584,99381811158493,99382191149478)]
theorem point_links_checked19038 : (cuts19038.take 2).map (fun c => (2499280897-1+2*2^9*c.k,99381216976427+c.lower,99381596967058+c.upper)) = pointBounds19038 := by
 decide +kernel
def cuts19039 : List PrefixCut := [⟨61,324443962,324444156⟩,
⟨128,682888227,682888628⟩]
theorem checked19039 : checkPrefixCuts (2^48) 2499411969 9 Manual.Count131072.C019039.packed 128 cuts19039 = true := by
 decide +kernel
def pointBounds19039 : List (Nat × Nat × Nat) := [(2499474432,99382221754320,99382601745549)]
theorem point_links_checked19039 : (cuts19039.take 1).map (fun c => (2499411969-1+2*2^9*c.k,99381897310358+c.lower,99382277301393+c.upper)) = pointBounds19039 := by
 decide +kernel
def cuts19040 : List PrefixCut := [⟨10,53152065,53152096⟩,
⟨87,460568874,460569149⟩,
⟨128,675758131,675758536⟩]
theorem checked19040 : checkPrefixCuts (2^48) 2499543041 9 Manual.Count131072.C019040.packed 128 cuts19040 = true := by
 decide +kernel
def pointBounds19040 : List (Nat × Nat × Nat) := [(2499553280,99382633350650,99383013342117),(2499632128,99383040767459,99383420759170)]
theorem point_links_checked19040 : (cuts19040.take 2).map (fun c => (2499543041-1+2*2^9*c.k,99382580198585+c.lower,99382960190021+c.upper)) = pointBounds19040 := by
 decide +kernel
def cuts19041 : List PrefixCut := [⟨36,190300438,190300553⟩,
⟨113,595326952,595327311⟩,
⟨128,678762870,678763276⟩]
theorem checked19041 : checkPrefixCuts (2^48) 2499674113 9 Manual.Count131072.C019041.packed 128 cuts19041 = true := by
 decide +kernel
def pointBounds19041 : List (Nat × Nat × Nat) := [(2499710976,99383446257154,99383826249110),(2499789824,99383851283668,99384231275868)]
theorem point_links_checked19041 : (cuts19041.take 2).map (fun c => (2499674113-1+2*2^9*c.k,99383255956716+c.lower,99383635948557+c.upper)) = pointBounds19041 := by
 decide +kernel
def cuts19042 : List PrefixCut := [⟨62,334301360,334301561⟩,
⟨128,691225404,691225822⟩]
theorem checked19042 : checkPrefixCuts (2^48) 2499805185 9 Manual.Count131072.C019042.packed 128 cuts19042 = true := by
 decide +kernel
def pointBounds19042 : List (Nat × Nat × Nat) := [(2499868672,99384269020946,99384649013394)]
theorem point_links_checked19042 : (cuts19042.take 1).map (fun c => (2499805185-1+2*2^9*c.k,99383934719586+c.lower,99384314711833+c.upper)) = pointBounds19042 := by
 decide +kernel
def cuts19043 : List PrefixCut := [⟨11,56408882,56408918⟩,
⟨88,464437005,464437289⟩,
⟨128,677115470,677115877⟩]
theorem checked19043 : checkPrefixCuts (2^48) 2499936257 9 Manual.Count131072.C019043.packed 128 cuts19043 = true := by
 decide +kernel
def pointBounds19043 : List (Nat × Nat × Nat) := [(2499947520,99384682353872,99385062346573),(2500026368,99385090381995,99385470374944)]
theorem point_links_checked19043 : (cuts19043.take 2).map (fun c => (2499936257-1+2*2^9*c.k,99384625944990+c.lower,99385005937655+c.upper)) = pointBounds19043 := by
 decide +kernel
def cuts19044 : List PrefixCut := [⟨37,198489233,198489349⟩,
⟨114,608855840,608856203⟩,
⟨128,683159529,683159937⟩]
theorem checked19044 : checkPrefixCuts (2^48) 2500067329 9 Manual.Count131072.C019044.packed 128 cuts19044 = true := by
 decide +kernel
def pointBounds19044 : List (Nat × Nat × Nat) := [(2500105216,99385501549693,99385881542881),(2500184064,99385911916300,99386291909735)]
theorem point_links_checked19044 : (cuts19044.take 2).map (fun c => (2500067329-1+2*2^9*c.k,99385303060460+c.lower,99385683053532+c.upper)) = pointBounds19044 := by
 decide +kernel
def cuts19045 : List PrefixCut := [⟨63,343142511,343142711⟩,
⟨128,682448460,682448867⟩]
theorem checked19045 : checkPrefixCuts (2^48) 2500198401 9 Manual.Count131072.C019045.packed 128 cuts19045 = true := by
 decide +kernel
def pointBounds19045 : List (Nat × Nat × Nat) := [(2500262912,99386329362500,99386709356180)]
theorem point_links_checked19045 : (cuts19045.take 1).map (fun c => (2500198401-1+2*2^9*c.k,99385986219989+c.lower,99386366213469+c.upper)) = pointBounds19045 := by
 decide +kernel
def cuts19046 : List PrefixCut := [⟨12,62929334,62929373⟩,
⟨89,468529085,468529368⟩,
⟨128,673519250,673519653⟩]
theorem checked19046 : checkPrefixCuts (2^48) 2500329473 9 Manual.Count131072.C019046.packed 128 cuts19046 = true := by
 decide +kernel
def pointBounds19046 : List (Nat × Nat × Nat) := [(2500341760,99386731597783,99387111591709),(2500420608,99387137197534,99387517191704)]
theorem point_links_checked19046 : (cuts19046.take 2).map (fun c => (2500329473-1+2*2^9*c.k,99386668668449+c.lower,99387048662336+c.upper)) = pointBounds19046 := by
 decide +kernel
def cuts19047 : List PrefixCut := [⟨38,204311553,204311674⟩,
⟨115,607071595,607071953⟩,
⟨128,675960525,675960924⟩]
theorem checked19047 : checkPrefixCuts (2^48) 2500460545 9 Manual.Count131072.C019047.packed 128 cuts19047 = true := by
 decide +kernel
def pointBounds19047 : List (Nat × Nat × Nat) := [(2500499456,99387546499252,99387926493663),(2500578304,99387949259294,99388329253942)]
theorem point_links_checked19047 : (cuts19047.take 2).map (fun c => (2500460545-1+2*2^9*c.k,99387342187699+c.lower,99387722181989+c.upper)) = pointBounds19047 := by
 decide +kernel
def cuts19048 : List PrefixCut := [⟨64,341287492,341287695⟩,
⟨128,687968905,687969312⟩]
theorem checked19048 : checkPrefixCuts (2^48) 2500591617 9 Manual.Count131072.C019048.packed 128 cuts19048 = true := by
 decide +kernel
def pointBounds19048 : List (Nat × Nat × Nat) := [(2500657152,99388359435716,99388739430608)]
theorem point_links_checked19048 : (cuts19048.take 1).map (fun c => (2500591617-1+2*2^9*c.k,99388018148224+c.lower,99388398142913+c.upper)) = pointBounds19048 := by
 decide +kernel
def cuts19049 : List PrefixCut := [⟨13,67871946,67871987⟩,
⟨90,481399231,481399522⟩,
⟨128,683543355,683543764⟩]
theorem checked19049 : checkPrefixCuts (2^48) 2500722689 9 Manual.Count131072.C019049.packed 128 cuts19049 = true := by
 decide +kernel
def pointBounds19049 : List (Nat × Nat × Nat) := [(2500736000,99388773989075,99389153984212),(2500814848,99389187516360,99389567511747)]
theorem point_links_checked19049 : (cuts19049.take 2).map (fun c => (2500722689-1+2*2^9*c.k,99388706117129+c.lower,99389086112225+c.upper)) = pointBounds19049 := by
 decide +kernel
def cuts19050 : List PrefixCut := [⟨39,209344148,209344274⟩,
⟨116,616655164,616655531⟩,
⟨128,681031414,681031821⟩]
theorem checked19050 : checkPrefixCuts (2^48) 2500853761 9 Manual.Count131072.C019050.packed 128 cuts19050 = true := by
 decide +kernel
def pointBounds19050 : List (Nat × Nat × Nat) := [(2500893696,99389599004632,99389979000263),(2500972544,99390006315648,99390386311520)]
theorem point_links_checked19050 : (cuts19050.take 2).map (fun c => (2500853761-1+2*2^9*c.k,99389389660484+c.lower,99389769655989+c.upper)) = pointBounds19050 := by
 decide +kernel
def cuts19051 : List PrefixCut := [⟨65,344947708,344947920⟩,
⟨128,681220747,681221158⟩]
theorem checked19051 : checkPrefixCuts (2^48) 2500984833 9 Manual.Count131072.C019051.packed 128 cuts19051 = true := by
 decide +kernel
def pointBounds19051 : List (Nat × Nat × Nat) := [(2501051392,99390415639606,99390795635730)]
theorem point_links_checked19051 : (cuts19051.take 1).map (fun c => (2500984833-1+2*2^9*c.k,99390070691898+c.lower,99390450687810+c.upper)) = pointBounds19051 := by
 decide +kernel
def cuts19052 : List PrefixCut := [⟨14,75739022,75739065⟩,
⟨91,485824972,485825261⟩,
⟨128,684336140,684336548⟩]
theorem checked19052 : checkPrefixCuts (2^48) 2501115905 9 Manual.Count131072.C019052.packed 128 cuts19052 = true := by
 decide +kernel
def pointBounds19052 : List (Nat × Nat × Nat) := [(2501130240,99390827651667,99391207648033),(2501209088,99391237737617,99391617734229)]
theorem point_links_checked19052 : (cuts19052.take 2).map (fun c => (2501115905-1+2*2^9*c.k,99390751912645+c.lower,99391131908968+c.upper)) = pointBounds19052 := by
 decide +kernel
def cuts19053 : List PrefixCut := [⟨40,214150134,214150263⟩,
⟨117,618808748,618809120⟩,
⟨128,677773518,677773924⟩]
theorem checked19053 : checkPrefixCuts (2^48) 2501246977 9 Manual.Count131072.C019053.packed 128 cuts19053 = true := by
 decide +kernel
def pointBounds19053 : List (Nat × Nat × Nat) := [(2501287936,99391650398919,99392030395779),(2501366784,99392055057533,99392435054636)]
theorem point_links_checked19053 : (cuts19053.take 2).map (fun c => (2501246977-1+2*2^9*c.k,99391436248785+c.lower,99391816245516+c.upper)) = pointBounds19053 := by
 decide +kernel
def cuts19054 : List PrefixCut := [⟨66,346131216,346131434⟩,
⟨128,677737875,677738292⟩]
theorem checked19054 : checkPrefixCuts (2^48) 2501378049 9 Manual.Count131072.C019054.packed 128 cuts19054 = true := by
 decide +kernel
def pointBounds19054 : List (Nat × Nat × Nat) := [(2501445632,99392460153519,99392840150874)]
theorem point_links_checked19054 : (cuts19054.take 1).map (fun c => (2501378049-1+2*2^9*c.k,99392114022303+c.lower,99392494019440+c.upper)) = pointBounds19054 := by
 decide +kernel
def cuts19055 : List PrefixCut := [⟨15,78877703,78877752⟩,
⟨92,486086032,486086323⟩,
⟨128,674664512,674664915⟩]
theorem checked19055 : checkPrefixCuts (2^48) 2501509121 9 Manual.Count131072.C019055.packed 128 cuts19055 = true := by
 decide +kernel
def pointBounds19055 : List (Nat × Nat × Nat) := [(2501524480,99392870637881,99393250635484),(2501603328,99393277846210,99393657844055)]
theorem point_links_checked19055 : (cuts19055.take 2).map (fun c => (2501509121-1+2*2^9*c.k,99392791760178+c.lower,99393171757732+c.upper)) = pointBounds19055 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S2.B000282
