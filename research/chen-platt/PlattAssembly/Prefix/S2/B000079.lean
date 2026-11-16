import PlattAssemblyKernel
import PlattCertificates.Count131072.C012528
import PlattCertificates.Count131072.C012529
import PlattCertificates.Count131072.C012530
import PlattCertificates.Count131072.C012531
import PlattCertificates.Count131072.C012532
import PlattCertificates.Count131072.C012533
import PlattCertificates.Count131072.C012534
import PlattCertificates.Count131072.C012535
import PlattCertificates.Count131072.C012536
import PlattCertificates.Count131072.C012537
import PlattCertificates.Count131072.C012538
import PlattCertificates.Count131072.C012539
import PlattCertificates.Count131072.C012540
import PlattCertificates.Count131072.C012541
import PlattCertificates.Count131072.C012542
import PlattCertificates.Count131072.C012543
import PlattCertificates.Count131072.C012544
import PlattCertificates.Count131072.C012545
import PlattCertificates.Count131072.C012546
import PlattCertificates.Count131072.C012547
import PlattCertificates.Count131072.C012548
import PlattCertificates.Count131072.C012549
import PlattCertificates.Count131072.C012550
import PlattCertificates.Count131072.C012551
import PlattCertificates.Count131072.C012552
import PlattCertificates.Count131072.C012553
import PlattCertificates.Count131072.C012554
import PlattCertificates.Count131072.C012555
import PlattCertificates.Count131072.C012556
import PlattCertificates.Count131072.C012557
import PlattCertificates.Count131072.C012558
import PlattCertificates.Count131072.C012559
namespace ChenEffective.PlattWindow.Assembly.Prefix.S2.B000079
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts12528 : List PrefixCut := [⟨9,72848003,72848059⟩,
⟨60,505994706,505995081⟩,
⟨111,915017254,915017934⟩,
⟨128,1059676870,1059677655⟩]
theorem checked12528 : checkPrefixCuts (2^48) 1646002177 9 Manual.Count131072.C012528.packed 128 cuts12528 = true := by
 decide +kernel
def pointBounds12528 : List (Nat × Nat × Nat) := [(1646011392,93895695426294,93896071792399),(1646063616,93896128572997,93896504939421),(1646115840,93896537595545,93896913962274)]
theorem point_links_checked12528 : (cuts12528.take 3).map (fun c => (1646002177-1+2*2^9*c.k,93895622578291+c.lower,93895998944340+c.upper)) = pointBounds12528 := by
 decide +kernel
def cuts12529 : List PrefixCut := [⟨34,279910145,279910355⟩,
⟨85,694720190,694720711⟩,
⟨128,1052068889,1052069679⟩]
theorem checked12529 : checkPrefixCuts (2^48) 1646133249 9 Manual.Count131072.C012529.packed 128 cuts12529 = true := by
 decide +kernel
def pointBounds12529 : List (Nat × Nat × Nat) := [(1646168064,93896962165306,93897338532350),(1646220288,93897376975351,93897753342706)]
theorem point_links_checked12529 : (cuts12529.take 2).map (fun c => (1646133249-1+2*2^9*c.k,93896682255161+c.lower,93897058621995+c.upper)) = pointBounds12529 := by
 decide +kernel
def cuts12530 : List PrefixCut := [⟨8,65997314,65997362⟩,
⟨59,485739332,485739691⟩,
⟨110,907861645,907862316⟩,
⟨128,1056601435,1056602216⟩]
theorem checked12530 : checkPrefixCuts (2^48) 1646264321 9 Manual.Count131072.C012530.packed 128 cuts12530 = true := by
 decide +kernel
def pointBounds12530 : List (Nat × Nat × Nat) := [(1646272512,93897800321364,93898176689036),(1646324736,93898220063382,93898596431365),(1646376960,93898642185695,93899018553990)]
theorem point_links_checked12530 : (cuts12530.take 3).map (fun c => (1646264321-1+2*2^9*c.k,93897734324050+c.lower,93898110691674+c.upper)) = pointBounds12530 := by
 decide +kernel
def cuts12531 : List PrefixCut := [⟨33,272343381,272343582⟩,
⟨84,685890994,685891501⟩,
⟨128,1050021017,1050021789⟩]
theorem checked12531 : checkPrefixCuts (2^48) 1646395393 9 Manual.Count131072.C012531.packed 128 cuts12531 = true := by
 decide +kernel
def pointBounds12531 : List (Nat × Nat × Nat) := [(1646429184,93899063268866,93899439637472),(1646481408,93899476816479,93899853185391)]
theorem point_links_checked12531 : (cuts12531.take 2).map (fun c => (1646395393-1+2*2^9*c.k,93898790925485+c.lower,93899167293890+c.upper)) = pointBounds12531 := by
 decide +kernel
def cuts12532 : List PrefixCut := [⟨7,55558859,55558901⟩,
⟨58,475063459,475063813⟩,
⟨109,897802662,897803327⟩,
⟨128,1055578547,1055579332⟩]
theorem checked12532 : checkPrefixCuts (2^48) 1646526465 9 Manual.Count131072.C012532.packed 128 cuts12532 = true := by
 decide +kernel
def pointBounds12532 : List (Nat × Nat × Nat) := [(1646533632,93899896505361,93900272874580),(1646585856,93900316009961,93900692379492),(1646638080,93900738749164,93901115119006)]
theorem point_links_checked12532 : (cuts12532.take 3).map (fun c => (1646526465-1+2*2^9*c.k,93899840946502+c.lower,93900217315679+c.upper)) = pointBounds12532 := by
 decide +kernel
def cuts12533 : List PrefixCut := [⟨32,268710464,268710659⟩,
⟨83,688516980,688517489⟩,
⟨128,1050025279,1050026056⟩]
theorem checked12533 : checkPrefixCuts (2^48) 1646657537 9 Manual.Count131072.C012533.packed 128 cuts12533 = true := by
 decide +kernel
def pointBounds12533 : List (Nat × Nat × Nat) := [(1646690304,93901165235513,93901541605670),(1646742528,93901585042029,93901961412500)]
theorem point_links_checked12533 : (cuts12533.take 2).map (fun c => (1646657537-1+2*2^9*c.k,93900896525049+c.lower,93901272895011+c.upper)) = pointBounds12533 := by
 decide +kernel
def cuts12534 : List PrefixCut := [⟨6,52131572,52131612⟩,
⟨57,464732849,464733197⟩,
⟨108,881081169,881081827⟩,
⟨128,1048232094,1048232875⟩]
theorem checked12534 : checkPrefixCuts (2^48) 1646788609 9 Manual.Count131072.C012534.packed 128 cuts12534 = true := by
 decide +kernel
def pointBounds12534 : List (Nat × Nat × Nat) := [(1646794752,93901998681900,93902375052679),(1646846976,93902411283177,93902787654264),(1646899200,93902827631497,93903204002894)]
theorem point_links_checked12534 : (cuts12534.take 3).map (fun c => (1646788609-1+2*2^9*c.k,93901946550328+c.lower,93902322921067+c.upper)) = pointBounds12534 := by
 decide +kernel
def cuts12535 : List PrefixCut := [⟨31,258413232,258413426⟩,
⟨82,682425780,682426288⟩,
⟨128,1061991876,1061992666⟩]
theorem checked12535 : checkPrefixCuts (2^48) 1646919681 9 Manual.Count131072.C012535.packed 128 cuts12535 = true := by
 decide +kernel
def pointBounds12535 : List (Nat × Nat × Nat) := [(1646951424,93903253195654,93903629567368),(1647003648,93903677208202,93904053580230)]
theorem point_links_checked12535 : (cuts12535.take 2).map (fun c => (1646919681-1+2*2^9*c.k,93902994782422+c.lower,93903371153942+c.upper)) = pointBounds12535 := by
 decide +kernel
def cuts12536 : List PrefixCut := [⟨5,41015050,41015079⟩,
⟨56,465684228,465684569⟩,
⟨107,886922243,886922896⟩,
⟨128,1056951610,1056952389⟩]
theorem checked12536 : checkPrefixCuts (2^48) 1647050753 9 Manual.Count131072.C012536.packed 128 cuts12536 = true := by
 decide +kernel
def pointBounds12536 : List (Nat × Nat × Nat) := [(1647055872,93904097789348,93904474161687),(1647108096,93904522458526,93904898831177),(1647160320,93904943696541,93905320069504)]
theorem point_links_checked12536 : (cuts12536.take 3).map (fun c => (1647050753-1+2*2^9*c.k,93904056774298+c.lower,93904433146608+c.upper)) = pointBounds12536 := by
 decide +kernel
def cuts12537 : List PrefixCut := [⟨30,247094105,247094289⟩,
⟨81,669672544,669673040⟩,
⟨128,1049690969,1049691748⟩]
theorem checked12537 : checkPrefixCuts (2^48) 1647181825 9 Manual.Count131072.C012537.packed 128 cuts12537 = true := by
 decide +kernel
def pointBounds12537 : List (Nat × Nat × Nat) := [(1647212544,93905360820013,93905737193286),(1647264768,93905783398452,93906159772037)]
theorem point_links_checked12537 : (cuts12537.take 2).map (fun c => (1647181825-1+2*2^9*c.k,93905113725908+c.lower,93905490098997+c.upper)) = pointBounds12537 := by
 decide +kernel
def cuts12538 : List PrefixCut := [⟨4,35369861,35369886⟩,
⟨55,457237953,457238290⟩,
⟨106,882680640,882681289⟩,
⟨128,1064642986,1064643769⟩]
theorem checked12538 : checkPrefixCuts (2^48) 1647312897 9 Manual.Count131072.C012538.packed 128 cuts12538 = true := by
 decide +kernel
def pointBounds12538 : List (Nat × Nat × Nat) := [(1647316992,93906198786738,93906575160631),(1647369216,93906620654830,93906997029035),(1647421440,93907046097517,93907422472034)]
theorem point_links_checked12538 : (cuts12538.take 3).map (fun c => (1647312897-1+2*2^9*c.k,93906163416877+c.lower,93906539790745+c.upper)) = pointBounds12538 := by
 decide +kernel
def cuts12539 : List PrefixCut := [⟨29,238683018,238683196⟩,
⟨80,659315052,659315541⟩,
⟨128,1046448592,1046449370⟩]
theorem checked12539 : checkPrefixCuts (2^48) 1647443969 9 Manual.Count131072.C012539.packed 128 cuts12539 = true := by
 decide +kernel
def pointBounds12539 : List (Nat × Nat × Nat) := [(1647473664,93907466742881,93907843117710),(1647525888,93907887374915,93908263750055)]
theorem point_links_checked12539 : (cuts12539.take 2).map (fun c => (1647443969-1+2*2^9*c.k,93907228059863+c.lower,93907604434514+c.upper)) = pointBounds12539 := by
 decide +kernel
def cuts12540 : List PrefixCut := [⟨3,26138787,26138807⟩,
⟨54,449306769,449307097⟩,
⟨105,869044653,869045292⟩,
⟨128,1057640492,1057641270⟩]
theorem checked12540 : checkPrefixCuts (2^48) 1647575041 9 Manual.Count131072.C012540.packed 128 cuts12540 = true := by
 decide +kernel
def pointBounds12540 : List (Nat × Nat × Nat) := [(1647578112,93908300647242,93908677022691),(1647630336,93908723815224,93909100190981),(1647682560,93909143553108,93909519929176)]
theorem point_links_checked12540 : (cuts12540.take 3).map (fun c => (1647575041-1+2*2^9*c.k,93908274508455+c.lower,93908650883884+c.upper)) = pointBounds12540 := by
 decide +kernel
def cuts12541 : List PrefixCut := [⟨28,235570184,235570358⟩,
⟨79,667068141,667068631⟩,
⟨128,1072930199,1072930991⟩]
theorem checked12541 : checkPrefixCuts (2^48) 1647706113 9 Manual.Count131072.C012541.packed 128 cuts12541 = true := by
 decide +kernel
def pointBounds12541 : List (Nat × Nat × Nat) := [(1647734784,93909567719131,93909944095512),(1647787008,93909999217088,93910375593785)]
theorem point_links_checked12541 : (cuts12541.take 2).map (fun c => (1647706113-1+2*2^9*c.k,93909332148947+c.lower,93909708525154+c.upper)) = pointBounds12541 := by
 decide +kernel
def cuts12542 : List PrefixCut := [⟨2,17935537,17935550⟩,
⟨53,439499120,439499447⟩,
⟨104,854558646,854559278⟩,
⟨128,1045515761,1045516536⟩]
theorem checked12542 : checkPrefixCuts (2^48) 1647837185 9 Manual.Count131072.C012542.packed 128 cuts12542 = true := by
 decide +kernel
def pointBounds12542 : List (Nat × Nat × Nat) := [(1647839232,93910423014683,93910799391695),(1647891456,93910844578266,93911220955592),(1647943680,93911259637792,93911636015423)]
theorem point_links_checked12542 : (cuts12542.take 3).map (fun c => (1647837185-1+2*2^9*c.k,93910405079146+c.lower,93910781456145+c.upper)) = pointBounds12542 := by
 decide +kernel
def cuts12543 : List PrefixCut := [⟨27,223064401,223064566⟩,
⟨78,644075551,644076029⟩,
⟨128,1052435006,1052435788⟩]
theorem checked12543 : checkPrefixCuts (2^48) 1647968257 9 Manual.Count131072.C012543.packed 128 cuts12543 = true := by
 decide +kernel
def pointBounds12543 : List (Nat × Nat × Nat) := [(1647995904,93911673659308,93912050037247),(1648048128,93912094670458,93912471048710)]
theorem point_links_checked12543 : (cuts12543.take 2).map (fun c => (1647968257-1+2*2^9*c.k,93911450594907+c.lower,93911826972681+c.upper)) = pointBounds12543 := by
 decide +kernel
def cuts12544 : List PrefixCut := [⟨1,9564101,9564108⟩,
⟨52,420130692,420131008⟩,
⟨103,849469953,849470585⟩,
⟨128,1056620390,1056621177⟩]
theorem checked12544 : checkPrefixCuts (2^48) 1648099329 9 Manual.Count131072.C012544.packed 128 cuts12544 = true := by
 decide +kernel
def pointBounds12544 : List (Nat × Nat × Nat) := [(1648100352,93912512594014,93912888972577),(1648152576,93912923160605,93913299539477),(1648204800,93913352499866,93913728879054)]
theorem point_links_checked12544 : (cuts12544.take 3).map (fun c => (1648099329-1+2*2^9*c.k,93912503029913+c.lower,93912879408469+c.upper)) = pointBounds12544 := by
 decide +kernel
def cuts12545 : List PrefixCut := [⟨26,208171794,208171949⟩,
⟨77,626383945,626384406⟩,
⟨128,1053120903,1053121681⟩]
theorem checked12545 : checkPrefixCuts (2^48) 1648230401 9 Manual.Count131072.C012545.packed 128 cuts12545 = true := by
 decide +kernel
def pointBounds12545 : List (Nat × Nat × Nat) := [(1648257024,93913767822097,93914144201595),(1648309248,93914186034248,93914562414052),(1648361472,93914612771206,93914989151327)]
theorem point_links_checked12545 : (cuts12545.take 3).map (fun c => (1648230401-1+2*2^9*c.k,93913559650303+c.lower,93913936029646+c.upper)) = pointBounds12545 := by
 decide +kernel
def cuts12546 : List PrefixCut := [⟨51,420234697,420235003⟩,
⟨102,845407907,845408524⟩,
⟨128,1051330246,1051331015⟩]
theorem checked12546 : checkPrefixCuts (2^48) 1648361473 9 Manual.Count131072.C012546.packed 128 cuts12546 = true := by
 decide +kernel
def pointBounds12546 : List (Nat × Nat × Nat) := [(1648413696,93915033005903,93915409386330),(1648465920,93915458179113,93915834559851)]
theorem point_links_checked12546 : (cuts12546.take 2).map (fun c => (1648361473-1+2*2^9*c.k,93914612771206+c.lower,93914989151327+c.upper)) = pointBounds12546 := by
 decide +kernel
def cuts12547 : List PrefixCut := [⟨25,208821776,208821933⟩,
⟨76,628675073,628675540⟩,
⟨127,1057564082,1057564864⟩,
⟨128,1065076347,1065077135⟩]
theorem checked12547 : checkPrefixCuts (2^48) 1648492545 9 Manual.Count131072.C012547.packed 128 cuts12547 = true := by
 decide +kernel
def pointBounds12547 : List (Nat × Nat × Nat) := [(1648518144,93915872923228,93916249304275),(1648570368,93916292776525,93916669157882),(1648622592,93916721665534,93917098047206)]
theorem point_links_checked12547 : (cuts12547.take 3).map (fun c => (1648492545-1+2*2^9*c.k,93915664101452+c.lower,93916040482342+c.upper)) = pointBounds12547 := by
 decide +kernel
def cuts12548 : List PrefixCut := [⟨50,416241209,416241521⟩,
⟨101,827176820,827177433⟩,
⟨128,1046894887,1046895668⟩]
theorem checked12548 : checkPrefixCuts (2^48) 1648623617 9 Manual.Count131072.C012548.packed 128 cuts12548 = true := by
 decide +kernel
def pointBounds12548 : List (Nat × Nat × Nat) := [(1648674816,93917145419008,93917521800998),(1648727040,93917556354619,93917932736910)]
theorem point_links_checked12548 : (cuts12548.take 2).map (fun c => (1648623617-1+2*2^9*c.k,93916729177799+c.lower,93917105559477+c.upper)) = pointBounds12548 := by
 decide +kernel
def cuts12549 : List PrefixCut := [⟨24,196326159,196326307⟩,
⟨75,611162239,611162700⟩,
⟨126,1034179144,1034179914⟩,
⟨128,1049884115,1049884897⟩]
theorem checked12549 : checkPrefixCuts (2^48) 1648754689 9 Manual.Count131072.C012549.packed 128 cuts12549 = true := by
 decide +kernel
def pointBounds12549 : List (Nat × Nat × Nat) := [(1648779264,93917972398845,93918348781452),(1648831488,93918387234925,93918763617845),(1648883712,93918810251830,93919186635059)]
theorem point_links_checked12549 : (cuts12549.take 3).map (fun c => (1648754689-1+2*2^9*c.k,93917776072686+c.lower,93918152455145+c.upper)) = pointBounds12549 := by
 decide +kernel
def cuts12550 : List PrefixCut := [⟨49,401494676,401494973⟩,
⟨100,821753653,821754261⟩,
⟨128,1055775209,1055775989⟩]
theorem checked12550 : checkPrefixCuts (2^48) 1648885761 9 Manual.Count131072.C012550.packed 128 cuts12550 = true := by
 decide +kernel
def pointBounds12550 : List (Nat × Nat × Nat) := [(1648935936,93919227451477,93919603835015),(1648988160,93919647710454,93920024094303)]
theorem point_links_checked12550 : (cuts12550.take 2).map (fun c => (1648885761-1+2*2^9*c.k,93918825956801+c.lower,93919202340042+c.upper)) = pointBounds12550 := by
 decide +kernel
def cuts12551 : List PrefixCut := [⟨23,188784594,188784736⟩,
⟨74,610211750,610212205⟩,
⟨125,1031796300,1031797067⟩,
⟨128,1054667303,1054668088⟩]
theorem checked12551 : checkPrefixCuts (2^48) 1649016833 9 Manual.Count131072.C012551.packed 128 cuts12551 = true := by
 decide +kernel
def pointBounds12551 : List (Nat × Nat × Nat) := [(1649040384,93920070516604,93920446900767),(1649092608,93920491943760,93920868328236),(1649144832,93920913528310,93921289913098)]
theorem point_links_checked12551 : (cuts12551.take 3).map (fun c => (1649016833-1+2*2^9*c.k,93919881732010+c.lower,93920258116031+c.upper)) = pointBounds12551 := by
 decide +kernel
def cuts12552 : List PrefixCut := [⟨48,400236275,400236570⟩,
⟨99,819234009,819234618⟩,
⟨128,1055607682,1055608467⟩]
theorem checked12552 : checkPrefixCuts (2^48) 1649147905 9 Manual.Count131072.C012552.packed 128 cuts12552 = true := by
 decide +kernel
def pointBounds12552 : List (Nat × Nat × Nat) := [(1649197056,93921336635588,93921713020689),(1649249280,93921755633322,93922132018737)]
theorem point_links_checked12552 : (cuts12552.take 2).map (fun c => (1649147905-1+2*2^9*c.k,93920936399313+c.lower,93921312784119+c.upper)) = pointBounds12552 := by
 decide +kernel
def cuts12553 : List PrefixCut := [⟨22,178856122,178856256⟩,
⟨73,599533903,599534350⟩,
⟨124,1019686453,1019687209⟩,
⟨128,1050574478,1050575257⟩]
theorem checked12553 : checkPrefixCuts (2^48) 1649278977 9 Manual.Count131072.C012553.packed 128 cuts12553 = true := by
 decide +kernel
def pointBounds12553 : List (Nat × Nat × Nat) := [(1649301504,93922170863117,93922547248842),(1649353728,93922591540898,93922967926936),(1649405952,93923011693448,93923388079795)]
theorem point_links_checked12553 : (cuts12553.take 3).map (fun c => (1649278977-1+2*2^9*c.k,93921992006995+c.lower,93922368392586+c.upper)) = pointBounds12553 := by
 decide +kernel
def cuts12554 : List PrefixCut := [⟨47,381230639,381230924⟩,
⟨98,819274217,819274827⟩,
⟨128,1069261675,1069262471⟩]
theorem checked12554 : checkPrefixCuts (2^48) 1649410049 9 Manual.Count131072.C012554.packed 128 cuts12554 = true := by
 decide +kernel
def pointBounds12554 : List (Nat × Nat × Nat) := [(1649458176,93923423812112,93923800198767),(1649510400,93923861855690,93924238242670)]
theorem point_links_checked12554 : (cuts12554.take 2).map (fun c => (1649410049-1+2*2^9*c.k,93923042581473+c.lower,93923418967843+c.upper)) = pointBounds12554 := by
 decide +kernel
def cuts12555 : List PrefixCut := [⟨21,176268171,176268300⟩,
⟨72,590736618,590737058⟩,
⟨123,1008092645,1008093387⟩,
⟨128,1049554514,1049555287⟩]
theorem checked12555 : checkPrefixCuts (2^48) 1649541121 9 Manual.Count131072.C012555.packed 128 cuts12555 = true := by
 decide +kernel
def pointBounds12555 : List (Nat × Nat × Nat) := [(1649562624,93924288111319,93924664498614),(1649614848,93924702579766,93925078967372),(1649667072,93925119935793,93925496323701)]
theorem point_links_checked12555 : (cuts12555.take 3).map (fun c => (1649541121-1+2*2^9*c.k,93924111843148+c.lower,93924488230314+c.upper)) = pointBounds12555 := by
 decide +kernel
def cuts12556 : List PrefixCut := [⟨46,378781504,378781780⟩,
⟨97,794916793,794917378⟩,
⟨128,1046911931,1046912705⟩]
theorem checked12556 : checkPrefixCuts (2^48) 1649672193 9 Manual.Count131072.C012556.packed 128 cuts12556 = true := by
 decide +kernel
def pointBounds12556 : List (Nat × Nat × Nat) := [(1649719296,93925540179166,93925916567381),(1649771520,93925956314455,93926332702979)]
theorem point_links_checked12556 : (cuts12556.take 2).map (fun c => (1649672193-1+2*2^9*c.k,93925161397662+c.lower,93925537785601+c.upper)) = pointBounds12556 := by
 decide +kernel
def cuts12557 : List PrefixCut := [⟨20,164297528,164297648⟩,
⟨71,581088976,581089408⟩,
⟨122,999573159,999573898⟩,
⟨128,1045975799,1045976573⟩]
theorem checked12557 : checkPrefixCuts (2^48) 1649803265 9 Manual.Count131072.C012557.packed 128 cuts12557 = true := by
 decide +kernel
def pointBounds12557 : List (Nat × Nat × Nat) := [(1649823744,93926372607121,93926748995954),(1649875968,93926789398569,93927165787714),(1649928192,93927207882752,93927584272204)]
theorem point_links_checked12557 : (cuts12557.take 3).map (fun c => (1649803265-1+2*2^9*c.k,93926208309593+c.lower,93926584698306+c.upper)) = pointBounds12557 := by
 decide +kernel
def cuts12558 : List PrefixCut := [⟨45,370362225,370362501⟩,
⟨96,791890501,791891085⟩,
⟨128,1054763154,1054763933⟩]
theorem checked12558 : checkPrefixCuts (2^48) 1649934337 9 Manual.Count131072.C012558.packed 128 cuts12558 = true := by
 decide +kernel
def pointBounds12558 : List (Nat × Nat × Nat) := [(1649980416,93927624647617,93928001037380),(1650032640,93928046175893,93928422565964)]
theorem point_links_checked12558 : (cuts12558.take 2).map (fun c => (1649934337-1+2*2^9*c.k,93927254285392+c.lower,93927630674879+c.upper)) = pointBounds12558 := by
 decide +kernel
def cuts12559 : List PrefixCut := [⟨19,156083501,156083618⟩,
⟨70,583555420,583555855⟩,
⟨121,1002996816,1002997564⟩,
⟨128,1059796922,1059797711⟩]
theorem checked12559 : checkPrefixCuts (2^48) 1650065409 9 Manual.Count131072.C012559.packed 128 cuts12559 = true := by
 decide +kernel
def pointBounds12559 : List (Nat × Nat × Nat) := [(1650084864,93928465132047,93928841522430),(1650137088,93928892603966,93929268994667),(1650189312,93929312045362,93929688436376)]
theorem point_links_checked12559 : (cuts12559.take 3).map (fun c => (1650065409-1+2*2^9*c.k,93928309048546+c.lower,93928685438812+c.upper)) = pointBounds12559 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S2.B000079
