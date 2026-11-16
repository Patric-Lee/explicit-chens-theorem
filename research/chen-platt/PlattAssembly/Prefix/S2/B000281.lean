import PlattAssemblyKernel
import PlattCertificates.Count131072.C018992
import PlattCertificates.Count131072.C018993
import PlattCertificates.Count131072.C018994
import PlattCertificates.Count131072.C018995
import PlattCertificates.Count131072.C018996
import PlattCertificates.Count131072.C018997
import PlattCertificates.Count131072.C018998
import PlattCertificates.Count131072.C018999
import PlattCertificates.Count131072.C019000
import PlattCertificates.Count131072.C019001
import PlattCertificates.Count131072.C019002
import PlattCertificates.Count131072.C019003
import PlattCertificates.Count131072.C019004
import PlattCertificates.Count131072.C019005
import PlattCertificates.Count131072.C019006
import PlattCertificates.Count131072.C019007
import PlattCertificates.Count131072.C019008
import PlattCertificates.Count131072.C019009
import PlattCertificates.Count131072.C019010
import PlattCertificates.Count131072.C019011
import PlattCertificates.Count131072.C019012
import PlattCertificates.Count131072.C019013
import PlattCertificates.Count131072.C019014
import PlattCertificates.Count131072.C019015
import PlattCertificates.Count131072.C019016
import PlattCertificates.Count131072.C019017
import PlattCertificates.Count131072.C019018
import PlattCertificates.Count131072.C019019
import PlattCertificates.Count131072.C019020
import PlattCertificates.Count131072.C019021
import PlattCertificates.Count131072.C019022
import PlattCertificates.Count131072.C019023
namespace ChenEffective.PlattWindow.Assembly.Prefix.S2.B000281
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts18992 : List PrefixCut := [⟨71,378643314,378643539⟩,
⟨128,687284817,687285226⟩]
theorem checked18992 : checkPrefixCuts (2^48) 2493251585 9 Manual.Count131072.C018992.packed 128 cuts18992 = true := by
 decide +kernel
def pointBounds18992 : List (Nat × Nat × Nat) := [(2493324288,99350185288089,99350565260181)]
theorem point_links_checked18992 : (cuts18992.take 1).map (fun c => (2493251585-1+2*2^9*c.k,99349806644775+c.lower,99350186616642+c.upper)) = pointBounds18992 := by
 decide +kernel
def cuts18993 : List PrefixCut := [⟨20,112323870,112323938⟩,
⟨97,523567778,523568090⟩,
⟨128,686910290,686910700⟩]
theorem checked18993 : checkPrefixCuts (2^48) 2493382657 9 Manual.Count131072.C018993.packed 128 cuts18993 = true := by
 decide +kernel
def pointBounds18993 : List (Nat × Nat × Nat) := [(2493403136,99350606253462,99350986225806),(2493481984,99351017497370,99351397469958)]
theorem point_links_checked18993 : (cuts18993.take 2).map (fun c => (2493382657-1+2*2^9*c.k,99350493929592+c.lower,99350873901868+c.upper)) = pointBounds18993 := by
 decide +kernel
def cuts18994 : List PrefixCut := [⟨46,246985310,246985459⟩,
⟨123,658993357,658993748⟩,
⟨128,686648225,686648633⟩]
theorem checked18994 : checkPrefixCuts (2^48) 2493513729 9 Manual.Count131072.C018994.packed 128 cuts18994 = true := by
 decide +kernel
def pointBounds18994 : List (Nat × Nat × Nat) := [(2493560832,99351427825192,99351807798027),(2493639680,99351839833239,99352219806316)]
theorem point_links_checked18994 : (cuts18994.take 2).map (fun c => (2493513729-1+2*2^9*c.k,99351180839882+c.lower,99351560812568+c.upper)) = pointBounds18994 := by
 decide +kernel
def cuts18995 : List PrefixCut := [⟨72,381066768,381067003⟩,
⟨128,680629771,680630188⟩]
theorem checked18995 : checkPrefixCuts (2^48) 2493644801 9 Manual.Count131072.C018995.packed 128 cuts18995 = true := by
 decide +kernel
def pointBounds18995 : List (Nat × Nat × Nat) := [(2493718528,99352248554875,99352628528204)]
theorem point_links_checked18995 : (cuts18995.take 1).map (fun c => (2493644801-1+2*2^9*c.k,99351867488107+c.lower,99352247461201+c.upper)) = pointBounds18995 := by
 decide +kernel
def cuts18996 : List PrefixCut := [⟨21,111177422,111177491⟩,
⟨98,524613660,524613976⟩,
⟨128,680932699,680933107⟩]
theorem checked18996 : checkPrefixCuts (2^48) 2493775873 9 Manual.Count131072.C018996.packed 128 cuts18996 = true := by
 decide +kernel
def pointBounds18996 : List (Nat × Nat × Nat) := [(2493797376,99352659295300,99353039268880),(2493876224,99353072731538,99353452705365)]
theorem point_links_checked18996 : (cuts18996.take 2).map (fun c => (2493775873-1+2*2^9*c.k,99352548117878+c.lower,99352928091389+c.upper)) = pointBounds18996 := by
 decide +kernel
def cuts18997 : List PrefixCut := [⟨47,250106536,250106688⟩,
⟨124,668031031,668031431⟩,
⟨128,688458545,688458957⟩]
theorem checked18997 : checkPrefixCuts (2^48) 2493906945 9 Manual.Count131072.C018997.packed 128 cuts18997 = true := by
 decide +kernel
def pointBounds18997 : List (Nat × Nat × Nat) := [(2493955072,99353479157113,99353859131184),(2494033920,99353897081608,99354277055927)]
theorem point_links_checked18997 : (cuts18997.take 2).map (fun c => (2493906945-1+2*2^9*c.k,99353229050577+c.lower,99353609024496+c.upper)) = pointBounds18997 := by
 decide +kernel
def cuts18998 : List PrefixCut := [⟨73,381683759,381683992⟩,
⟨128,674653910,674654320⟩]
theorem checked18998 : checkPrefixCuts (2^48) 2494038017 9 Manual.Count131072.C018998.packed 128 cuts18998 = true := by
 decide +kernel
def pointBounds18998 : List (Nat × Nat × Nat) := [(2494112768,99354299192881,99354679167445)]
theorem point_links_checked18998 : (cuts18998.take 1).map (fun c => (2494038017-1+2*2^9*c.k,99353917509122+c.lower,99354297483453+c.upper)) = pointBounds18998 := by
 decide +kernel
def cuts18999 : List PrefixCut := [⟨22,118946704,118946774⟩,
⟨99,529947691,529948006⟩,
⟨128,688724714,688725124⟩]
theorem checked18999 : checkPrefixCuts (2^48) 2494169089 9 Manual.Count131072.C018999.packed 128 cuts18999 = true := by
 decide +kernel
def pointBounds18999 : List (Nat × Nat × Nat) := [(2494191616,99354711109736,99355091084547),(2494270464,99355122110723,99355502085779)]
theorem point_links_checked18999 : (cuts18999.take 2).map (fun c => (2494169089-1+2*2^9*c.k,99354592163032+c.lower,99354972137773+c.upper)) = pointBounds18999 := by
 decide +kernel
def cuts19000 : List PrefixCut := [⟨48,256612091,256612242⟩,
⟨125,667587153,667587554⟩,
⟨128,683610629,683611039⟩]
theorem checked19000 : checkPrefixCuts (2^48) 2494300161 9 Manual.Count131072.C019000.packed 128 cuts19000 = true := by
 decide +kernel
def pointBounds19000 : List (Nat × Nat × Nat) := [(2494349312,99355537499837,99355917475139),(2494428160,99355948474899,99356328450451)]
theorem point_links_checked19000 : (cuts19000.take 2).map (fun c => (2494300161-1+2*2^9*c.k,99355280887746+c.lower,99355660862897+c.upper)) = pointBounds19000 := by
 decide +kernel
def cuts19001 : List PrefixCut := [⟨74,391440599,391440830⟩,
⟨128,680528082,680528488⟩]
theorem checked19001 : checkPrefixCuts (2^48) 2494431233 9 Manual.Count131072.C019001.packed 128 cuts19001 = true := by
 decide +kernel
def pointBounds19001 : List (Nat × Nat × Nat) := [(2494507008,99356355938974,99356735914766)]
theorem point_links_checked19001 : (cuts19001.take 1).map (fun c => (2494431233-1+2*2^9*c.k,99355964498375+c.lower,99356344473936+c.upper)) = pointBounds19001 := by
 decide +kernel
def cuts19002 : List PrefixCut := [⟨23,125923697,125923773⟩,
⟨100,543065543,543065867⟩,
⟨128,692114101,692114514⟩]
theorem checked19002 : checkPrefixCuts (2^48) 2494562305 9 Manual.Count131072.C019002.packed 128 cuts19002 = true := by
 decide +kernel
def pointBounds19002 : List (Nat × Nat × Nat) := [(2494585856,99356770950154,99357150926197),(2494664704,99357188092000,99357568068291)]
theorem point_links_checked19002 : (cuts19002.take 2).map (fun c => (2494562305-1+2*2^9*c.k,99356645026457+c.lower,99357025002424+c.upper)) = pointBounds19002 := by
 decide +kernel
def cuts19003 : List PrefixCut := [⟨49,266162012,266162170⟩,
⟨126,684180192,684180595⟩,
⟨128,696590785,696591195⟩]
theorem checked19003 : checkPrefixCuts (2^48) 2494693377 9 Manual.Count131072.C019003.packed 128 cuts19003 = true := by
 decide +kernel
def pointBounds19003 : List (Nat × Nat × Nat) := [(2494743552,99357603302570,99357983279108),(2494822400,99358021320750,99358401297533)]
theorem point_links_checked19003 : (cuts19003.take 2).map (fun c => (2494693377-1+2*2^9*c.k,99357337140558+c.lower,99357717116938+c.upper)) = pointBounds19003 := by
 decide +kernel
def cuts19004 : List PrefixCut := [⟨75,397132709,397132950⟩,
⟨128,682790018,682790423⟩]
theorem checked19004 : checkPrefixCuts (2^48) 2494824449 9 Manual.Count131072.C019004.packed 128 cuts19004 = true := by
 decide +kernel
def pointBounds19004 : List (Nat × Nat × Nat) := [(2494901248,99358430864052,99358810841083)]
theorem point_links_checked19004 : (cuts19004.take 1).map (fun c => (2494824449-1+2*2^9*c.k,99358033731343+c.lower,99358413708133+c.upper)) = pointBounds19004 := by
 decide +kernel
def cuts19005 : List PrefixCut := [⟨24,131093404,131093479⟩,
⟨101,537339112,537339431⟩,
⟨128,681174788,681175189⟩]
theorem checked19005 : checkPrefixCuts (2^48) 2494955521 9 Manual.Count131072.C019005.packed 128 cuts19005 = true := by
 decide +kernel
def pointBounds19005 : List (Nat × Nat × Nat) := [(2494980096,99358847614765,99359227592035),(2495058944,99359253860473,99359633837987)]
theorem point_links_checked19005 : (cuts19005.take 2).map (fun c => (2494955521-1+2*2^9*c.k,99358716521361+c.lower,99359096498556+c.upper)) = pointBounds19005 := by
 decide +kernel
def cuts19006 : List PrefixCut := [⟨50,271986166,271986327⟩,
⟨127,669068848,669069247⟩,
⟨128,675385971,675386374⟩]
theorem checked19006 : checkPrefixCuts (2^48) 2495086593 9 Manual.Count131072.C019006.packed 128 cuts19006 = true := by
 decide +kernel
def pointBounds19006 : List (Nat × Nat × Nat) := [(2495137792,99359669682315,99360049660072),(2495216640,99360066764997,99360446742992)]
theorem point_links_checked19006 : (cuts19006.take 2).map (fun c => (2495086593-1+2*2^9*c.k,99359397696149+c.lower,99359777673745+c.upper)) = pointBounds19006 := by
 decide +kernel
def cuts19007 : List PrefixCut := [⟨76,405981553,405981799⟩,
⟨128,685051292,685051702⟩]
theorem checked19007 : checkPrefixCuts (2^48) 2495217665 9 Manual.Count131072.C019007.packed 128 cuts19007 = true := by
 decide +kernel
def pointBounds19007 : List (Nat × Nat × Nat) := [(2495295488,99360479063673,99360859041918)]
theorem point_links_checked19007 : (cuts19007.take 1).map (fun c => (2495217665-1+2*2^9*c.k,99360073082120+c.lower,99360453060119+c.upper)) = pointBounds19007 := by
 decide +kernel
def cuts19008 : List PrefixCut := [⟨25,133779904,133779984⟩,
⟨102,547744394,547744715⟩,
⟨128,688399132,688399539⟩]
theorem checked19008 : checkPrefixCuts (2^48) 2495348737 9 Manual.Count131072.C019008.packed 128 cuts19008 = true := by
 decide +kernel
def pointBounds19008 : List (Nat × Nat × Nat) := [(2495374336,99360891913316,99361271891805),(2495453184,99361305877806,99361685856536)]
theorem point_links_checked19008 : (cuts19008.take 2).map (fun c => (2495348737-1+2*2^9*c.k,99360758133412+c.lower,99361138111821+c.upper)) = pointBounds19008 := by
 decide +kernel
def cuts19009 : List PrefixCut := [⟨51,272281611,272281773⟩,
⟨128,679790968,679791376⟩]
theorem checked19009 : checkPrefixCuts (2^48) 2495479809 9 Manual.Count131072.C019009.packed 128 cuts19009 = true := by
 decide +kernel
def pointBounds19009 : List (Nat × Nat × Nat) := [(2495532032,99361718814155,99362098793133),(2495610880,99362126323512,99362506302736)]
theorem point_links_checked19009 : (cuts19009.take 2).map (fun c => (2495479809-1+2*2^9*c.k,99361446532544+c.lower,99361826511360+c.upper)) = pointBounds19009 := by
 decide +kernel
def cuts19010 : List PrefixCut := [⟨77,400052624,400052866⟩,
⟨128,670845163,670845568⟩]
theorem checked19010 : checkPrefixCuts (2^48) 2495610881 9 Manual.Count131072.C019010.packed 128 cuts19010 = true := by
 decide +kernel
def pointBounds19010 : List (Nat × Nat × Nat) := [(2495689728,99362526376136,99362906355602)]
theorem point_links_checked19010 : (cuts19010.take 1).map (fun c => (2495610881-1+2*2^9*c.k,99362126323512+c.lower,99362506302736+c.upper)) = pointBounds19010 := by
 decide +kernel
def cuts19011 : List PrefixCut := [⟨26,137706152,137706232⟩,
⟨103,549011444,549011776⟩,
⟨128,682313514,682313925⟩]
theorem checked19011 : checkPrefixCuts (2^48) 2495741953 9 Manual.Count131072.C019011.packed 128 cuts19011 = true := by
 decide +kernel
def pointBounds19011 : List (Nat × Nat × Nat) := [(2495768576,99362934874827,99363314854536),(2495847424,99363346180119,99363726160080)]
theorem point_links_checked19011 : (cuts19011.take 2).map (fun c => (2495741953-1+2*2^9*c.k,99362797168675+c.lower,99363177148304+c.upper)) = pointBounds19011 := by
 decide +kernel
def cuts19012 : List PrefixCut := [⟨52,278215776,278215942⟩,
⟨128,684082043,684082452⟩]
theorem checked19012 : checkPrefixCuts (2^48) 2495873025 9 Manual.Count131072.C019012.packed 128 cuts19012 = true := by
 decide +kernel
def pointBounds19012 : List (Nat × Nat × Nat) := [(2495926272,99363757697965,99364137678171)]
theorem point_links_checked19012 : (cuts19012.take 1).map (fun c => (2495873025-1+2*2^9*c.k,99363479482189+c.lower,99363859462229+c.upper)) = pointBounds19012 := by
 decide +kernel
def cuts19013 : List PrefixCut := [⟨1,4285267,4285270⟩,
⟨78,413296099,413296345⟩,
⟨128,679422587,679422994⟩]
theorem checked19013 : checkPrefixCuts (2^48) 2496004097 9 Manual.Count131072.C019013.packed 128 cuts19013 = true := by
 decide +kernel
def pointBounds19013 : List (Nat × Nat × Nat) := [(2496005120,99364167849499,99364547829951),(2496083968,99364576860331,99364956841026)]
theorem point_links_checked19013 : (cuts19013.take 2).map (fun c => (2496004097-1+2*2^9*c.k,99364163564232+c.lower,99364543544681+c.upper)) = pointBounds19013 := by
 decide +kernel
def cuts19014 : List PrefixCut := [⟨27,142758791,142758880⟩,
⟨104,551180092,551180428⟩,
⟨128,678259405,678259818⟩]
theorem checked19014 : checkPrefixCuts (2^48) 2496135169 9 Manual.Count131072.C019014.packed 128 cuts19014 = true := by
 decide +kernel
def pointBounds19014 : List (Nat × Nat × Nat) := [(2496162816,99364985745610,99365365726555),(2496241664,99365394166911,99365774148103)]
theorem point_links_checked19014 : (cuts19014.take 2).map (fun c => (2496135169-1+2*2^9*c.k,99364842986819+c.lower,99365222967675+c.upper)) = pointBounds19014 := by
 decide +kernel
def cuts19015 : List PrefixCut := [⟨53,282794957,282795127⟩,
⟨128,683410586,683410995⟩]
theorem checked19015 : checkPrefixCuts (2^48) 2496266241 9 Manual.Count131072.C019015.packed 128 cuts19015 = true := by
 decide +kernel
def pointBounds19015 : List (Nat × Nat × Nat) := [(2496320512,99365804041181,99366184022620)]
theorem point_links_checked19015 : (cuts19015.take 1).map (fun c => (2496266241-1+2*2^9*c.k,99365521246224+c.lower,99365901227493+c.upper)) = pointBounds19015 := by
 decide +kernel
def cuts19016 : List PrefixCut := [⟨2,10711477,10711484⟩,
⟨79,417741052,417741299⟩,
⟨128,676835175,676835583⟩]
theorem checked19016 : checkPrefixCuts (2^48) 2496397313 9 Manual.Count131072.C019016.packed 128 cuts19016 = true := by
 decide +kernel
def pointBounds19016 : List (Nat × Nat × Nat) := [(2496399360,99366215368287,99366595349972),(2496478208,99366622397862,99367002379787)]
theorem point_links_checked19016 : (cuts19016.take 2).map (fun c => (2496397313-1+2*2^9*c.k,99366204656810+c.lower,99366584638488+c.upper)) = pointBounds19016 := by
 decide +kernel
def cuts19017 : List PrefixCut := [⟨28,150290251,150290339⟩,
⟨105,564960633,564960970⟩,
⟨128,686721062,686721471⟩]
theorem checked19017 : checkPrefixCuts (2^48) 2496528385 9 Manual.Count131072.C019017.packed 128 cuts19017 = true := by
 decide +kernel
def pointBounds19017 : List (Nat × Nat × Nat) := [(2496557056,99367031782236,99367411764410),(2496635904,99367446452618,99367826435041)]
theorem point_links_checked19017 : (cuts19017.take 2).map (fun c => (2496528385-1+2*2^9*c.k,99366881491985+c.lower,99367261474071+c.upper)) = pointBounds19017 := by
 decide +kernel
def cuts19018 : List PrefixCut := [⟨54,291318511,291318686⟩,
⟨128,684430278,684430686⟩]
theorem checked19018 : checkPrefixCuts (2^48) 2496659457 9 Manual.Count131072.C019018.packed 128 cuts19018 = true := by
 decide +kernel
def pointBounds19018 : List (Nat × Nat × Nat) := [(2496714752,99367859531558,99368239514228)]
theorem point_links_checked19018 : (cuts19018.take 1).map (fun c => (2496659457-1+2*2^9*c.k,99367568213047+c.lower,99367948195542+c.upper)) = pointBounds19018 := by
 decide +kernel
def cuts19019 : List PrefixCut := [⟨3,15670112,15670121⟩,
⟨80,424777292,424777544⟩,
⟨128,679884952,679885357⟩]
theorem checked19019 : checkPrefixCuts (2^48) 2496790529 9 Manual.Count131072.C019019.packed 128 cuts19019 = true := by
 decide +kernel
def pointBounds19019 : List (Nat × Nat × Nat) := [(2496793600,99368268313437,99368648296349),(2496872448,99368677420617,99369057403772)]
theorem point_links_checked19019 : (cuts19019.take 2).map (fun c => (2496790529-1+2*2^9*c.k,99368252643325+c.lower,99368632626228+c.upper)) = pointBounds19019 := by
 decide +kernel
def cuts19020 : List PrefixCut := [⟨29,157368436,157368531⟩,
⟨106,565548025,565548366⟩,
⟨128,684020275,684020685⟩]
theorem checked19020 : checkPrefixCuts (2^48) 2496921601 9 Manual.Count131072.C019020.packed 128 cuts19020 = true := by
 decide +kernel
def pointBounds19020 : List (Nat × Nat × Nat) := [(2496951296,99369089896713,99369469880116),(2497030144,99369498076302,99369878059951)]
theorem point_links_checked19020 : (cuts19020.take 2).map (fun c => (2496921601-1+2*2^9*c.k,99368932528277+c.lower,99369312511585+c.upper)) = pointBounds19020 := by
 decide +kernel
def cuts19021 : List PrefixCut := [⟨55,292512535,292512708⟩,
⟨128,680602717,680603123⟩]
theorem checked19021 : checkPrefixCuts (2^48) 2497052673 9 Manual.Count131072.C019021.packed 128 cuts19021 = true := by
 decide +kernel
def pointBounds19021 : List (Nat × Nat × Nat) := [(2497108992,99369909061087,99370289044978)]
theorem point_links_checked19021 : (cuts19021.take 1).map (fun c => (2497052673-1+2*2^9*c.k,99369616548552+c.lower,99369996532270+c.upper)) = pointBounds19021 := by
 decide +kernel
def cuts19022 : List PrefixCut := [⟨4,21528916,21528930⟩,
⟨81,431360597,431360854⟩,
⟨128,682032330,682032735⟩]
theorem checked19022 : checkPrefixCuts (2^48) 2497183745 9 Manual.Count131072.C019022.packed 128 cuts19022 = true := by
 decide +kernel
def pointBounds19022 : List (Nat × Nat × Nat) := [(2497187840,99370318680185,99370698664323),(2497266688,99370728511866,99371108496247)]
theorem point_links_checked19022 : (cuts19022.take 2).map (fun c => (2497183745-1+2*2^9*c.k,99370297151269+c.lower,99370677135393+c.upper)) = pointBounds19022 := by
 decide +kernel
def cuts19023 : List PrefixCut := [⟨30,164444368,164444464⟩,
⟨107,575264448,575264793⟩,
⟨128,685152396,685152809⟩]
theorem checked19023 : checkPrefixCuts (2^48) 2497314817 9 Manual.Count131072.C019023.packed 128 cuts19023 = true := by
 decide +kernel
def pointBounds19023 : List (Nat × Nat × Nat) := [(2497345536,99371143627967,99371523612592),(2497424384,99371554448047,99371934432921)]
theorem point_links_checked19023 : (cuts19023.take 2).map (fun c => (2497314817-1+2*2^9*c.k,99370979183599+c.lower,99371359168128+c.upper)) = pointBounds19023 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S2.B000281
