import PlattAssemblyKernel
import PlattCertificates.Count131072.C016592
import PlattCertificates.Count131072.C016593
import PlattCertificates.Count131072.C016594
import PlattCertificates.Count131072.C016595
import PlattCertificates.Count131072.C016596
import PlattCertificates.Count131072.C016597
import PlattCertificates.Count131072.C016598
import PlattCertificates.Count131072.C016599
import PlattCertificates.Count131072.C016600
import PlattCertificates.Count131072.C016601
import PlattCertificates.Count131072.C016602
import PlattCertificates.Count131072.C016603
import PlattCertificates.Count131072.C016604
import PlattCertificates.Count131072.C016605
import PlattCertificates.Count131072.C016606
import PlattCertificates.Count131072.C016607
import PlattCertificates.Count131072.C016608
import PlattCertificates.Count131072.C016609
import PlattCertificates.Count131072.C016610
import PlattCertificates.Count131072.C016611
import PlattCertificates.Count131072.C016612
import PlattCertificates.Count131072.C016613
import PlattCertificates.Count131072.C016614
import PlattCertificates.Count131072.C016615
import PlattCertificates.Count131072.C016616
import PlattCertificates.Count131072.C016617
import PlattCertificates.Count131072.C016618
import PlattCertificates.Count131072.C016619
import PlattCertificates.Count131072.C016620
import PlattCertificates.Count131072.C016621
import PlattCertificates.Count131072.C016622
import PlattCertificates.Count131072.C016623
namespace ChenEffective.PlattWindow.Assembly.Prefix.S2.B000206
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts16592 : List PrefixCut := [⟨21,128419409,128419492⟩,
⟨88,543900613,543900956⟩,
⟨128,795301751,795302255⟩]
theorem checked16592 : checkPrefixCuts (2^48) 2178678785 9 Manual.Count131072.C016592.packed 128 cuts16592 = true := by
 decide +kernel
def pointBounds16592 : List (Nat × Nat × Nat) := [(2178700288,97590030065613,97590408956501),(2178768896,97590445546817,97590824437965)]
theorem point_links_checked16592 : (cuts16592.take 2).map (fun c => (2178678785-1+2*2^9*c.k,97589901646204+c.lower,97590280537009+c.upper)) = pointBounds16592 := by
 decide +kernel
def cuts16593 : List PrefixCut := [⟨27,162516766,162516869⟩,
⟨94,572675269,572675635⟩,
⟨128,783627374,783627872⟩]
theorem checked16593 : checkPrefixCuts (2^48) 2178809857 9 Manual.Count131072.C016593.packed 128 cuts16593 = true := by
 decide +kernel
def pointBounds16593 : List (Nat × Nat × Nat) := [(2178837504,97590859464721,97591238356133),(2178906112,97591269623224,97591648514899)]
theorem point_links_checked16593 : (cuts16593.take 2).map (fun c => (2178809857-1+2*2^9*c.k,97590696947955+c.lower,97591075839264+c.upper)) = pointBounds16593 := by
 decide +kernel
def cuts16594 : List PrefixCut := [⟨33,202810534,202810660⟩,
⟨100,614234918,614235309⟩,
⟨128,787843100,787843600⟩]
theorem checked16594 : checkPrefixCuts (2^48) 2178940929 9 Manual.Count131072.C016594.packed 128 cuts16594 = true := by
 decide +kernel
def pointBounds16594 : List (Nat × Nat × Nat) := [(2178974720,97591683385863,97592062277796),(2179043328,97592094810247,97592473702445)]
theorem point_links_checked16594 : (cuts16594.take 2).map (fun c => (2178940929-1+2*2^9*c.k,97591480575329+c.lower,97591859467136+c.upper)) = pointBounds16594 := by
 decide +kernel
def cuts16595 : List PrefixCut := [⟨39,234961562,234961713⟩,
⟨106,649589245,649589654⟩,
⟨128,784695646,784696140⟩]
theorem checked16595 : checkPrefixCuts (2^48) 2179072001 9 Manual.Count131072.C016595.packed 128 cuts16595 = true := by
 decide +kernel
def pointBounds16595 : List (Nat × Nat × Nat) := [(2179111936,97592503379991,97592882272449),(2179180544,97592918007674,97593296900390)]
theorem point_links_checked16595 : (cuts16595.take 2).map (fun c => (2179072001-1+2*2^9*c.k,97592268418429+c.lower,97592647310736+c.upper)) = pointBounds16595 := by
 decide +kernel
def cuts16596 : List PrefixCut := [⟨45,272016808,272016980⟩,
⟨112,682356128,682356558⟩,
⟨128,781031968,781032462⟩]
theorem checked16596 : checkPrefixCuts (2^48) 2179203073 9 Manual.Count131072.C016596.packed 128 cuts16596 = true := by
 decide +kernel
def pointBounds16596 : List (Nat × Nat × Nat) := [(2179249152,97593325130883,97593704023856),(2179317760,97593735470203,97594114363434)]
theorem point_links_checked16596 : (cuts16596.take 2).map (fun c => (2179203073-1+2*2^9*c.k,97593053114075+c.lower,97593432006876+c.upper)) = pointBounds16596 := by
 decide +kernel
def cuts16597 : List PrefixCut := [⟨51,316687619,316687819⟩,
⟨118,728292634,728293098⟩,
⟨128,793125386,793125892⟩]
theorem checked16597 : checkPrefixCuts (2^48) 2179334145 9 Manual.Count131072.C016597.packed 128 cuts16597 = true := by
 decide +kernel
def pointBounds16597 : List (Nat × Nat × Nat) := [(2179386368,97594150833662,97594529727157),(2179454976,97594562438677,97594941332436)]
theorem point_links_checked16597 : (cuts16597.take 2).map (fun c => (2179334145-1+2*2^9*c.k,97593834146043+c.lower,97594213039338+c.upper)) = pointBounds16597 := by
 decide +kernel
def cuts16598 : List PrefixCut := [⟨57,344563773,344563989⟩,
⟨124,751752024,751752493⟩,
⟨128,775513960,775514444⟩]
theorem checked16598 : checkPrefixCuts (2^48) 2179465217 9 Manual.Count131072.C016598.packed 128 cuts16598 = true := by
 decide +kernel
def pointBounds16598 : List (Nat × Nat × Nat) := [(2179523584,97594971835202,97595350729219),(2179592192,97595379023453,97595757917723)]
theorem point_links_checked16598 : (cuts16598.take 2).map (fun c => (2179465217-1+2*2^9*c.k,97594627271429+c.lower,97595006165230+c.upper)) = pointBounds16598 := by
 decide +kernel
def cuts16599 : List PrefixCut := [⟨63,381734718,381734961⟩,
⟨128,784894302,784894805⟩]
theorem checked16599 : checkPrefixCuts (2^48) 2179596289 9 Manual.Count131072.C016599.packed 128 cuts16599 = true := by
 decide +kernel
def pointBounds16599 : List (Nat × Nat × Nat) := [(2179660800,97595784520107,97596163414635)]
theorem point_links_checked16599 : (cuts16599.take 1).map (fun c => (2179596289-1+2*2^9*c.k,97595402785389+c.lower,97595781679674+c.upper)) = pointBounds16599 := by
 decide +kernel
def cuts16600 : List PrefixCut := [⟨2,13429833,13429841⟩,
⟨69,421096121,421096392⟩,
⟨128,783426663,783427160⟩]
theorem checked16600 : checkPrefixCuts (2^48) 2179727361 9 Manual.Count131072.C016600.packed 128 cuts16600 = true := by
 decide +kernel
def pointBounds16600 : List (Nat × Nat × Nat) := [(2179729408,97596201109524,97596580004320),(2179798016,97596608775812,97596987670871)]
theorem point_links_checked16600 : (cuts16600.take 2).map (fun c => (2179727361-1+2*2^9*c.k,97596187679691+c.lower,97596566574479+c.upper)) = pointBounds16600 := by
 decide +kernel
def cuts16601 : List PrefixCut := [⟨8,48938398,48938431⟩,
⟨75,462131259,462131555⟩,
⟨128,790739429,790739931⟩]
theorem checked16601 : checkPrefixCuts (2^48) 2179858433 9 Manual.Count131072.C016601.packed 128 cuts16601 = true := by
 decide +kernel
def pointBounds16601 : List (Nat × Nat × Nat) := [(2179866624,97597020044752,97597398940070),(2179935232,97597433237613,97597812133194)]
theorem point_links_checked16601 : (cuts16601.take 2).map (fun c => (2179858433-1+2*2^9*c.k,97596971106354+c.lower,97597350001639+c.upper)) = pointBounds16601 := by
 decide +kernel
def cuts16602 : List PrefixCut := [⟨14,87024934,87024988⟩,
⟨81,490766496,490766804⟩,
⟨128,779071802,779072295⟩]
theorem checked16602 : checkPrefixCuts (2^48) 2179989505 9 Manual.Count131072.C016602.packed 128 cuts16602 = true := by
 decide +kernel
def pointBounds16602 : List (Nat × Nat × Nat) := [(2180003840,97597848870717,97598227766558),(2180072448,97598252612279,97598631508374)]
theorem point_links_checked16602 : (cuts16602.take 2).map (fun c => (2179989505-1+2*2^9*c.k,97597761845783+c.lower,97598140741570+c.upper)) = pointBounds16602 := by
 decide +kernel
def cuts16603 : List PrefixCut := [⟨20,125623228,125623309⟩,
⟨87,535923777,535924119⟩,
⟨128,790386277,790386782⟩]
theorem checked16603 : checkPrefixCuts (2^48) 2180120577 9 Manual.Count131072.C016603.packed 128 cuts16603 = true := by
 decide +kernel
def pointBounds16603 : List (Nat × Nat × Nat) := [(2180141056,97598666540813,97599045437174),(2180209664,97599076841362,97599455737984)]
theorem point_links_checked16603 : (cuts16603.take 2).map (fun c => (2180120577-1+2*2^9*c.k,97598540917585+c.lower,97598919813865+c.upper)) = pointBounds16603 := by
 decide +kernel
def cuts16604 : List PrefixCut := [⟨26,160731029,160731132⟩,
⟨93,575524253,575524623⟩,
⟨128,792920760,792921265⟩]
theorem checked16604 : checkPrefixCuts (2^48) 2180251649 9 Manual.Count131072.C016604.packed 128 cuts16604 = true := by
 decide +kernel
def pointBounds16604 : List (Nat × Nat × Nat) := [(2180278272,97599492034891,97599870931779),(2180346880,97599906828115,97600285725270)]
theorem point_links_checked16604 : (cuts16604.take 2).map (fun c => (2180251649-1+2*2^9*c.k,97599331303862+c.lower,97599710200647+c.upper)) = pointBounds16604 := by
 decide +kernel
def cuts16605 : List PrefixCut := [⟨32,195576343,195576467⟩,
⟨99,605179827,605180211⟩,
⟨128,778027807,778028299⟩]
theorem checked16605 : checkPrefixCuts (2^48) 2180382721 9 Manual.Count131072.C016605.packed 128 cuts16605 = true := by
 decide +kernel
def pointBounds16605 : List (Nat × Nat × Nat) := [(2180415488,97600319800965,97600698698379),(2180484096,97600729404449,97601108302123)]
theorem point_links_checked16605 : (cuts16605.take 2).map (fun c => (2180382721-1+2*2^9*c.k,97600124224622+c.lower,97600503121912+c.upper)) = pointBounds16605 := by
 decide +kernel
def cuts16606 : List PrefixCut := [⟨38,233773573,233773718⟩,
⟨105,645674691,645675096⟩,
⟨128,786242204,786242697⟩]
theorem checked16606 : checkPrefixCuts (2^48) 2180513793 9 Manual.Count131072.C016606.packed 128 cuts16606 = true := by
 decide +kernel
def pointBounds16606 : List (Nat × Nat × Nat) := [(2180552704,97601136026002,97601514923929),(2180621312,97601547927120,97601926825307)]
theorem point_links_checked16606 : (cuts16606.take 2).map (fun c => (2180513793-1+2*2^9*c.k,97600902252429+c.lower,97601281150211+c.upper)) = pointBounds16606 := by
 decide +kernel
def cuts16607 : List PrefixCut := [⟨44,270159013,270159184⟩,
⟨111,678162011,678162441⟩,
⟨128,781419213,781419708⟩]
theorem checked16607 : checkPrefixCuts (2^48) 2180644865 9 Manual.Count131072.C016607.packed 128 cuts16607 = true := by
 decide +kernel
def pointBounds16607 : List (Nat × Nat × Nat) := [(2180689920,97601958653646,97602337552092),(2180758528,97602366656644,97602745555349)]
theorem point_links_checked16607 : (cuts16607.take 2).map (fun c => (2180644865-1+2*2^9*c.k,97601688494633+c.lower,97602067392908+c.upper)) = pointBounds16607 := by
 decide +kernel
def cuts16608 : List PrefixCut := [⟨50,313767863,313768064⟩,
⟨117,726133464,726133922⟩,
⟨128,792214003,792214501⟩]
theorem checked16608 : checkPrefixCuts (2^48) 2180775937 9 Manual.Count131072.C016608.packed 128 cuts16608 = true := by
 decide +kernel
def pointBounds16608 : List (Nat × Nat × Nat) := [(2180827136,97602783681709,97603162580680),(2180895744,97603196047310,97603574946538)]
theorem point_links_checked16608 : (cuts16608.take 2).map (fun c => (2180775937-1+2*2^9*c.k,97602469913846+c.lower,97602848812616+c.upper)) = pointBounds16608 := by
 decide +kernel
def cuts16609 : List PrefixCut := [⟨56,347433640,347433865⟩,
⟨123,764806567,764807057⟩,
⟨128,793715026,793715535⟩]
theorem checked16609 : checkPrefixCuts (2^48) 2180907009 9 Manual.Count131072.C016609.packed 128 cuts16609 = true := by
 decide +kernel
def pointBounds16609 : List (Nat × Nat × Nat) := [(2180964352,97603609561489,97603988460982),(2181032960,97604026934416,97604405834174)]
theorem point_links_checked16609 : (cuts16609.take 2).map (fun c => (2180907009-1+2*2^9*c.k,97603262127849+c.lower,97603641027117+c.upper)) = pointBounds16609 := by
 decide +kernel
def cuts16610 : List PrefixCut := [⟨62,381482398,381482637⟩,
⟨128,785924148,785924641⟩]
theorem checked16610 : checkPrefixCuts (2^48) 2181038081 9 Manual.Count131072.C016610.packed 128 cuts16610 = true := by
 decide +kernel
def pointBounds16610 : List (Nat × Nat × Nat) := [(2181101568,97604437325273,97604816225289)]
theorem point_links_checked16610 : (cuts16610.take 1).map (fun c => (2181038081-1+2*2^9*c.k,97604055842875+c.lower,97604434742652+c.upper)) = pointBounds16610 := by
 decide +kernel
def cuts16611 : List PrefixCut := [⟨1,6581432,6581436⟩,
⟨68,403912893,403913150⟩,
⟨128,763681372,763681855⟩]
theorem checked16611 : checkPrefixCuts (2^48) 2181169153 9 Manual.Count131072.C016611.packed 128 cuts16611 = true := by
 decide +kernel
def pointBounds16611 : List (Nat × Nat × Nat) := [(2181170176,97604848348455,97605227248729),(2181238784,97605245679916,97605624580443)]
theorem point_links_checked16611 : (cuts16611.take 2).map (fun c => (2181169153-1+2*2^9*c.k,97604841767023+c.lower,97605220667293+c.upper)) = pointBounds16611 := by
 decide +kernel
def cuts16612 : List PrefixCut := [⟨7,39228080,39228107⟩,
⟨74,456406398,456406691⟩,
⟨128,793313806,793314312⟩]
theorem checked16612 : checkPrefixCuts (2^48) 2181300225 9 Manual.Count131072.C016612.packed 128 cuts16612 = true := by
 decide +kernel
def pointBounds16612 : List (Nat × Nat × Nat) := [(2181307392,97605644676475,97606023577255),(2181376000,97606061854793,97606440755839)]
theorem point_links_checked16612 : (cuts16612.take 2).map (fun c => (2181300225-1+2*2^9*c.k,97605605448395+c.lower,97605984349148+c.upper)) = pointBounds16612 := by
 decide +kernel
def cuts16613 : List PrefixCut := [⟨13,80902953,80903005⟩,
⟨80,489022939,489023247⟩,
⟨128,781266576,781267067⟩]
theorem checked16613 : checkPrefixCuts (2^48) 2181431297 9 Manual.Count131072.C016613.packed 128 cuts16613 = true := by
 decide +kernel
def pointBounds16613 : List (Nat × Nat × Nat) := [(2181444608,97606479665154,97606858566465),(2181513216,97606887785140,97607266686707)]
theorem point_links_checked16613 : (cuts16613.take 2).map (fun c => (2181431297-1+2*2^9*c.k,97606398762201+c.lower,97606777663460+c.upper)) = pointBounds16613 := by
 decide +kernel
def cuts16614 : List PrefixCut := [⟨19,119605146,119605222⟩,
⟨86,525893110,525893438⟩,
⟨128,789863892,789864386⟩]
theorem checked16614 : checkPrefixCuts (2^48) 2181562369 9 Manual.Count131072.C016614.packed 128 cuts16614 = true := by
 decide +kernel
def pointBounds16614 : List (Nat × Nat × Nat) := [(2181581824,97607299633923,97607678535749),(2181650432,97607705921887,97608084823965)]
theorem point_links_checked16614 : (cuts16614.take 2).map (fun c => (2181562369-1+2*2^9*c.k,97607180028777+c.lower,97607558930527+c.upper)) = pointBounds16614 := by
 decide +kernel
def cuts16615 : List PrefixCut := [⟨25,151206686,151206782⟩,
⟨92,566887052,566887408⟩,
⟨128,779624617,779625109⟩]
theorem checked16615 : checkPrefixCuts (2^48) 2181693441 9 Manual.Count131072.C016615.packed 128 cuts16615 = true := by
 decide +kernel
def pointBounds16615 : List (Nat × Nat × Nat) := [(2181719040,97608121099355,97608500001695),(2181787648,97608536779721,97608915682321)]
theorem point_links_checked16615 : (cuts16615.take 2).map (fun c => (2181693441-1+2*2^9*c.k,97607969892669+c.lower,97608348794913+c.upper)) = pointBounds16615 := by
 decide +kernel
def cuts16616 : List PrefixCut := [⟨31,192995989,192996110⟩,
⟨98,607489153,607489535⟩,
⟨128,789511110,789511606⟩]
theorem checked16616 : checkPrefixCuts (2^48) 2181824513 9 Manual.Count131072.C016616.packed 128 cuts16616 = true := by
 decide +kernel
def pointBounds16616 : List (Nat × Nat × Nat) := [(2181856256,97608942513275,97609321416132),(2181924864,97609357006439,97609735909557)]
theorem point_links_checked16616 : (cuts16616.take 2).map (fun c => (2181824513-1+2*2^9*c.k,97608749517286+c.lower,97609128420022+c.upper)) = pointBounds16616 := by
 decide +kernel
def cuts16617 : List PrefixCut := [⟨37,230136149,230136300⟩,
⟨104,647570201,647570617⟩,
⟨128,794752562,794753070⟩]
theorem checked16617 : checkPrefixCuts (2^48) 2181955585 9 Manual.Count131072.C016617.packed 128 cuts16617 = true := by
 decide +kernel
def pointBounds16617 : List (Nat × Nat × Nat) := [(2181993472,97609769164545,97610148067928),(2182062080,97610186598597,97610565502245)]
theorem point_links_checked16617 : (cuts16617.take 2).map (fun c => (2181955585-1+2*2^9*c.k,97609539028396+c.lower,97609917931628+c.upper)) = pointBounds16617 := by
 decide +kernel
def cuts16618 : List PrefixCut := [⟨43,254243543,254243707⟩,
⟨110,656430686,656431107⟩,
⟨128,762586378,762586867⟩]
theorem checked16618 : checkPrefixCuts (2^48) 2182086657 9 Manual.Count131072.C016618.packed 128 cuts16618 = true := by
 decide +kernel
def pointBounds16618 : List (Nat × Nat × Nat) := [(2182130688,97610588024501,97610966928405),(2182199296,97610990211644,97611369115805)]
theorem point_links_checked16618 : (cuts16618.take 2).map (fun c => (2182086657-1+2*2^9*c.k,97610333780958+c.lower,97610712684698+c.upper)) = pointBounds16618 := by
 decide +kernel
def cuts16619 : List PrefixCut := [⟨49,299888280,299888472⟩,
⟨116,711465749,711466202⟩,
⟨128,782661783,782662281⟩]
theorem checked16619 : checkPrefixCuts (2^48) 2182217729 9 Manual.Count131072.C016619.packed 128 cuts16619 = true := by
 decide +kernel
def pointBounds16619 : List (Nat × Nat × Nat) := [(2182267904,97611396255616,97611775160037),(2182336512,97611807833085,97612186737767)]
theorem point_links_checked16619 : (cuts16619.take 2).map (fun c => (2182217729-1+2*2^9*c.k,97611096367336+c.lower,97611475271565+c.upper)) = pointBounds16619 := by
 decide +kernel
def cuts16620 : List PrefixCut := [⟨55,340626355,340626571⟩,
⟨122,745342381,745342853⟩,
⟨128,782614824,782615320⟩]
theorem checked16620 : checkPrefixCuts (2^48) 2182348801 9 Manual.Count131072.C016620.packed 128 cuts16620 = true := by
 decide +kernel
def pointBounds16620 : List (Nat × Nat × Nat) := [(2182405120,97612219655474,97612598560417),(2182473728,97612624371500,97613003276699)]
theorem point_links_checked16620 : (cuts16620.take 2).map (fun c => (2182348801-1+2*2^9*c.k,97611879029119+c.lower,97612257933846+c.upper)) = pointBounds16620 := by
 decide +kernel
def cuts16621 : List PrefixCut := [⟨61,370268202,370268436⟩,
⟨128,781922834,781923329⟩]
theorem checked16621 : checkPrefixCuts (2^48) 2182479873 9 Manual.Count131072.C016621.packed 128 cuts16621 = true := by
 decide +kernel
def pointBounds16621 : List (Nat × Nat × Nat) := [(2182542336,97613031912145,97613410817602),(2182610944,97613443566777,97613822472495)]
theorem point_links_checked16621 : (cuts16621.take 2).map (fun c => (2182479873-1+2*2^9*c.k,97612661643943+c.lower,97613040549166+c.upper)) = pointBounds16621 := by
 decide +kernel
def cuts16622 : List PrefixCut := [⟨67,406870183,406870439⟩,
⟨128,784584000,784584497⟩]
theorem checked16622 : checkPrefixCuts (2^48) 2182610945 9 Manual.Count131072.C016622.packed 128 cuts16622 = true := by
 decide +kernel
def pointBounds16622 : List (Nat × Nat × Nat) := [(2182679552,97613850436960,97614229342934)]
theorem point_links_checked16622 : (cuts16622.take 1).map (fun c => (2182610945-1+2*2^9*c.k,97613443566777+c.lower,97613822472495+c.upper)) = pointBounds16622 := by
 decide +kernel
def cuts16623 : List PrefixCut := [⟨6,38815316,38815342⟩,
⟨73,446175809,446176092⟩,
⟨128,783634407,783634905⟩]
theorem checked16623 : checkPrefixCuts (2^48) 2182742017 9 Manual.Count131072.C016623.packed 128 cuts16623 = true := by
 decide +kernel
def pointBounds16623 : List (Nat × Nat × Nat) := [(2182748160,97614266966093,97614645872334),(2182816768,97614674326586,97615053233084)]
theorem point_links_checked16623 : (cuts16623.take 2).map (fun c => (2182742017-1+2*2^9*c.k,97614228150777+c.lower,97614607056992+c.upper)) = pointBounds16623 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S2.B000206
