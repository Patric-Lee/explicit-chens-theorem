import PlattAssemblyKernel
import PlattCertificates.Count131072.C018064
import PlattCertificates.Count131072.C018065
import PlattCertificates.Count131072.C018066
import PlattCertificates.Count131072.C018067
import PlattCertificates.Count131072.C018068
import PlattCertificates.Count131072.C018069
import PlattCertificates.Count131072.C018070
import PlattCertificates.Count131072.C018071
import PlattCertificates.Count131072.C018072
import PlattCertificates.Count131072.C018073
import PlattCertificates.Count131072.C018074
import PlattCertificates.Count131072.C018075
import PlattCertificates.Count131072.C018076
import PlattCertificates.Count131072.C018077
import PlattCertificates.Count131072.C018078
import PlattCertificates.Count131072.C018079
import PlattCertificates.Count131072.C018080
import PlattCertificates.Count131072.C018081
import PlattCertificates.Count131072.C018082
import PlattCertificates.Count131072.C018083
import PlattCertificates.Count131072.C018084
import PlattCertificates.Count131072.C018085
import PlattCertificates.Count131072.C018086
import PlattCertificates.Count131072.C018087
import PlattCertificates.Count131072.C018088
import PlattCertificates.Count131072.C018089
import PlattCertificates.Count131072.C018090
import PlattCertificates.Count131072.C018091
import PlattCertificates.Count131072.C018092
import PlattCertificates.Count131072.C018093
import PlattCertificates.Count131072.C018094
import PlattCertificates.Count131072.C018095
namespace ChenEffective.PlattWindow.Assembly.Prefix.S2.B000252
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts18064 : List PrefixCut := [⟨16,87114362,87114413⟩,
⟨89,492651213,492651504⟩,
⟨128,718379166,718379589⟩]
theorem checked18064 : checkPrefixCuts (2^48) 2371616769 9 Manual.Count131072.C018064.packed 128 cuts18064 = true := by
 decide +kernel
def pointBounds18064 : List (Nat × Nat × Nat) := [(2371633152,98698541996881,98698921575653),(2371707904,98698947533732,98699327112744)]
theorem point_links_checked18064 : (cuts18064.take 2).map (fun c => (2371616769-1+2*2^9*c.k,98698454882519+c.lower,98698834461240+c.upper)) = pointBounds18064 := by
 decide +kernel
def cuts18065 : List PrefixCut := [⟨34,189053105,189053217⟩,
⟨107,595276422,595276779⟩,
⟨128,712049898,712050325⟩]
theorem checked18065 : checkPrefixCuts (2^48) 2371747841 9 Manual.Count131072.C018065.packed 128 cuts18065 = true := by
 decide +kernel
def pointBounds18065 : List (Nat × Nat × Nat) := [(2371782656,98699362314790,98699741894046),(2371857408,98699768538107,98700148117608)]
theorem point_links_checked18065 : (cuts18065.take 2).map (fun c => (2371747841-1+2*2^9*c.k,98699173261685+c.lower,98699552840829+c.upper)) = pointBounds18065 := by
 decide +kernel
def cuts18066 : List PrefixCut := [⟨52,302016092,302016277⟩,
⟨125,716164408,716164841⟩,
⟨128,732302876,732303318⟩]
theorem checked18066 : checkPrefixCuts (2^48) 2371878913 9 Manual.Count131072.C018066.packed 128 cuts18066 = true := by
 decide +kernel
def pointBounds18066 : List (Nat × Nat × Nat) := [(2371932160,98700187327675,98700566907431),(2372006912,98700601475991,98700981055995)]
theorem point_links_checked18066 : (cuts18066.take 2).map (fun c => (2371878913-1+2*2^9*c.k,98699885311583+c.lower,98700264891154+c.upper)) = pointBounds18066 := by
 decide +kernel
def cuts18067 : List PrefixCut := [⟨70,396691557,396691797⟩,
⟨128,724549332,724549774⟩]
theorem checked18067 : checkPrefixCuts (2^48) 2372009985 9 Manual.Count131072.C018067.packed 128 cuts18067 = true := by
 decide +kernel
def pointBounds18067 : List (Nat × Nat × Nat) := [(2372081664,98701014306016,98701393886269)]
theorem point_links_checked18067 : (cuts18067.take 1).map (fun c => (2372009985-1+2*2^9*c.k,98700617614459+c.lower,98700997194472+c.upper)) = pointBounds18067 := by
 decide +kernel
def cuts18068 : List PrefixCut := [⟨15,84721960,84722010⟩,
⟨88,485423144,485423441⟩,
⟨128,712287801,712288236⟩]
theorem checked18068 : checkPrefixCuts (2^48) 2372141057 9 Manual.Count131072.C018068.packed 128 cuts18068 = true := by
 decide +kernel
def pointBounds18068 : List (Nat × Nat × Nat) := [(2372156416,98701426885751,98701806466256),(2372231168,98701827586935,98702207167687)]
theorem point_links_checked18068 : (cuts18068.take 2).map (fun c => (2372141057-1+2*2^9*c.k,98701342163791+c.lower,98701721744246+c.upper)) = pointBounds18068 := by
 decide +kernel
def cuts18069 : List PrefixCut := [⟨33,182129576,182129685⟩,
⟨106,596094047,596094412⟩,
⟨128,723757187,723757626⟩]
theorem checked18069 : checkPrefixCuts (2^48) 2372272129 9 Manual.Count131072.C018069.packed 128 cuts18069 = true := by
 decide +kernel
def pointBounds18069 : List (Nat × Nat × Nat) := [(2372305920,98702236581168,98702616162167),(2372380672,98702650545639,98703030126894)]
theorem point_links_checked18069 : (cuts18069.take 2).map (fun c => (2372272129-1+2*2^9*c.k,98702054451592+c.lower,98702434032482+c.upper)) = pointBounds18069 := by
 decide +kernel
def cuts18070 : List PrefixCut := [⟨51,287830765,287830941⟩,
⟨124,696904916,696905338⟩,
⟨128,718141301,718141737⟩]
theorem checked18070 : checkPrefixCuts (2^48) 2372403201 9 Manual.Count131072.C018070.packed 128 cuts18070 = true := by
 decide +kernel
def pointBounds18070 : List (Nat × Nat × Nat) := [(2372455424,98703066039544,98703445621049),(2372530176,98703475113695,98703854695446)]
theorem point_links_checked18070 : (cuts18070.take 2).map (fun c => (2372403201-1+2*2^9*c.k,98702778208779+c.lower,98703157790108+c.upper)) = pointBounds18070 := by
 decide +kernel
def cuts18071 : List PrefixCut := [⟨69,386875782,386876023⟩,
⟨128,722846910,722847356⟩]
theorem checked18071 : checkPrefixCuts (2^48) 2372534273 9 Manual.Count131072.C018071.packed 128 cuts18071 = true := by
 decide +kernel
def pointBounds18071 : List (Nat × Nat × Nat) := [(2372604928,98703883225862,98704262807868)]
theorem point_links_checked18071 : (cuts18071.take 1).map (fun c => (2372534273-1+2*2^9*c.k,98703496350080+c.lower,98703875931845+c.upper)) = pointBounds18071 := by
 decide +kernel
def cuts18072 : List PrefixCut := [⟨14,79957974,79958025⟩,
⟨87,494687698,494688001⟩,
⟨128,722569862,722570306⟩]
theorem checked18072 : checkPrefixCuts (2^48) 2372665345 9 Manual.Count131072.C018072.packed 128 cuts18072 = true := by
 decide +kernel
def pointBounds18072 : List (Nat × Nat × Nat) := [(2372679680,98704299154964,98704678737226),(2372754432,98704713884688,98705093467202)]
theorem point_links_checked18072 : (cuts18072.take 2).map (fun c => (2372665345-1+2*2^9*c.k,98704219196990+c.lower,98704598779201+c.upper)) = pointBounds18072 := by
 decide +kernel
def cuts18073 : List PrefixCut := [⟨32,189325471,189325584⟩,
⟨105,601300766,601301127⟩,
⟨128,725732973,725733410⟩]
theorem checked18073 : checkPrefixCuts (2^48) 2372796417 9 Manual.Count131072.C018073.packed 128 cuts18073 = true := by
 decide +kernel
def pointBounds18073 : List (Nat × Nat × Nat) := [(2372829184,98705131092323,98705510675091),(2372903936,98705543067618,98705922650634)]
theorem point_links_checked18073 : (cuts18073.take 2).map (fun c => (2372796417-1+2*2^9*c.k,98704941766852+c.lower,98705321349507+c.upper)) = pointBounds18073 := by
 decide +kernel
def cuts18074 : List PrefixCut := [⟨50,281954918,281955093⟩,
⟨123,690227137,690227557⟩,
⟨128,718456992,718457428⟩]
theorem checked18074 : checkPrefixCuts (2^48) 2372927489 9 Manual.Count131072.C018074.packed 128 cuts18074 = true := by
 decide +kernel
def pointBounds18074 : List (Nat × Nat × Nat) := [(2372978688,98705949454743,98706329038010),(2373053440,98706357726962,98706737310474)]
theorem point_links_checked18074 : (cuts18074.take 2).map (fun c => (2372927489-1+2*2^9*c.k,98705667499825+c.lower,98706047082917+c.upper)) = pointBounds18074 := by
 decide +kernel
def cuts18075 : List PrefixCut := [⟨68,384062263,384062498⟩,
⟨128,722212765,722213208⟩]
theorem checked18075 : checkPrefixCuts (2^48) 2373058561 9 Manual.Count131072.C018075.packed 128 cuts18075 = true := by
 decide +kernel
def pointBounds18075 : List (Nat × Nat × Nat) := [(2373128192,98706770019080,98707149602843)]
theorem point_links_checked18075 : (cuts18075.take 1).map (fun c => (2373058561-1+2*2^9*c.k,98706385956817+c.lower,98706765540345+c.upper)) = pointBounds18075 := by
 decide +kernel
def cuts18076 : List PrefixCut := [⟨13,74721658,74721704⟩,
⟨86,473704249,473704539⟩,
⟨128,716361253,716361686⟩]
theorem checked18076 : checkPrefixCuts (2^48) 2373189633 9 Manual.Count131072.C018076.packed 128 cuts18076 = true := by
 decide +kernel
def pointBounds18076 : List (Nat × Nat × Nat) := [(2373202944,98707182891240,98707562475257),(2373277696,98707581873831,98707961458092)]
theorem point_links_checked18076 : (cuts18076.take 2).map (fun c => (2373189633-1+2*2^9*c.k,98707108169582+c.lower,98707487753553+c.upper)) = pointBounds18076 := by
 decide +kernel
def cuts18077 : List PrefixCut := [⟨31,181693402,181693511⟩,
⟨104,578634693,578635055⟩,
⟨128,710036468,710036910⟩]
theorem checked18077 : checkPrefixCuts (2^48) 2373320705 9 Manual.Count131072.C018077.packed 128 cuts18077 = true := by
 decide +kernel
def pointBounds18077 : List (Nat × Nat × Nat) := [(2373352448,98708006224237,98708385808750),(2373427200,98708403165528,98708782750294)]
theorem point_links_checked18077 : (cuts18077.take 2).map (fun c => (2373320705-1+2*2^9*c.k,98707824530835+c.lower,98708204115239+c.upper)) = pointBounds18077 := by
 decide +kernel
def cuts18078 : List PrefixCut := [⟨49,276437464,276437634⟩,
⟨122,684382471,684382890⟩,
⟨128,718298255,718298695⟩]
theorem checked18078 : checkPrefixCuts (2^48) 2373451777 9 Manual.Count131072.C018078.packed 128 cuts18078 = true := by
 decide +kernel
def pointBounds18078 : List (Nat × Nat × Nat) := [(2373501952,98708811004767,98709190589783),(2373576704,98709218949774,98709598535039)]
theorem point_links_checked18078 : (cuts18078.take 2).map (fun c => (2373451777-1+2*2^9*c.k,98708534567303+c.lower,98708914152149+c.upper)) = pointBounds18078 := by
 decide +kernel
def cuts18079 : List PrefixCut := [⟨67,385874972,385875210⟩,
⟨128,730828595,730829044⟩]
theorem checked18079 : checkPrefixCuts (2^48) 2373582849 9 Manual.Count131072.C018079.packed 128 cuts18079 = true := by
 decide +kernel
def pointBounds18079 : List (Nat × Nat × Nat) := [(2373651456,98709638740530,98710018326054)]
theorem point_links_checked18079 : (cuts18079.take 1).map (fun c => (2373582849-1+2*2^9*c.k,98709252865558+c.lower,98709632450844+c.upper)) = pointBounds18079 := by
 decide +kernel
def cuts18080 : List PrefixCut := [⟨12,67590403,67590442⟩,
⟨85,473243957,473244245⟩,
⟨128,711460165,711460604⟩]
theorem checked18080 : checkPrefixCuts (2^48) 2373713921 9 Manual.Count131072.C018080.packed 128 cuts18080 = true := by
 decide +kernel
def pointBounds18080 : List (Nat × Nat × Nat) := [(2373726208,98710051284556,98710430870330),(2373800960,98710456938110,98710836524133)]
theorem point_links_checked18080 : (cuts18080.take 2).map (fun c => (2373713921-1+2*2^9*c.k,98709983694153+c.lower,98710363279888+c.upper)) = pointBounds18080 := by
 decide +kernel
def cuts18081 : List PrefixCut := [⟨30,166594554,166594655⟩,
⟨103,581115273,581115625⟩,
⟨128,725886189,725886631⟩]
theorem checked18081 : checkPrefixCuts (2^48) 2373844993 9 Manual.Count131072.C018081.packed 128 cuts18081 = true := by
 decide +kernel
def pointBounds18081 : List (Nat × Nat × Nat) := [(2373875712,98710861748872,98711241335147),(2373950464,98711276269591,98711655856117)]
theorem point_links_checked18081 : (cuts18081.take 2).map (fun c => (2373844993-1+2*2^9*c.k,98710695154318+c.lower,98711074740492+c.upper)) = pointBounds18081 := by
 decide +kernel
def cuts18082 : List PrefixCut := [⟨48,276732233,276732396⟩,
⟨121,684231746,684232160⟩,
⟨128,724779436,724779874⟩]
theorem checked18082 : checkPrefixCuts (2^48) 2373976065 9 Manual.Count131072.C018082.packed 128 cuts18082 = true := by
 decide +kernel
def pointBounds18082 : List (Nat × Nat × Nat) := [(2374025216,98711697772740,98712077359519),(2374099968,98712105272253,98712484859283)]
theorem point_links_checked18082 : (cuts18082.take 2).map (fun c => (2373976065-1+2*2^9*c.k,98711421040507+c.lower,98711800627123+c.upper)) = pointBounds18082 := by
 decide +kernel
def cuts18083 : List PrefixCut := [⟨66,366583236,366583465⟩,
⟨128,713001918,713002361⟩]
theorem checked18083 : checkPrefixCuts (2^48) 2374107137 9 Manual.Count131072.C018083.packed 128 cuts18083 = true := by
 decide +kernel
def pointBounds18083 : List (Nat × Nat × Nat) := [(2374174720,98712512403179,98712891990462)]
theorem point_links_checked18083 : (cuts18083.take 1).map (fun c => (2374107137-1+2*2^9*c.k,98712145819943+c.lower,98712525406997+c.upper)) = pointBounds18083 := by
 decide +kernel
def cuts18084 : List PrefixCut := [⟨11,60462276,60462314⟩,
⟨84,474917760,474918049⟩,
⟨128,724462039,724462474⟩]
theorem checked18084 : checkPrefixCuts (2^48) 2374238209 9 Manual.Count131072.C018084.packed 128 cuts18084 = true := by
 decide +kernel
def pointBounds18084 : List (Nat × Nat × Nat) := [(2374249472,98712919284137,98713298871672),(2374324224,98713333739621,98713713327407)]
theorem point_links_checked18084 : (cuts18084.take 2).map (fun c => (2374238209-1+2*2^9*c.k,98712858821861+c.lower,98713238409358+c.upper)) = pointBounds18084 := by
 decide +kernel
def cuts18085 : List PrefixCut := [⟨29,166320720,166320817⟩,
⟨102,580512974,580513322⟩,
⟨128,724303626,724304065⟩]
theorem checked18085 : checkPrefixCuts (2^48) 2374369281 9 Manual.Count131072.C018085.packed 128 cuts18085 = true := by
 decide +kernel
def pointBounds18085 : List (Nat × Nat × Nat) := [(2374398976,98713749604620,98714129192649),(2374473728,98714163796874,98714543385154)]
theorem point_links_checked18085 : (cuts18085.take 2).map (fun c => (2374369281-1+2*2^9*c.k,98713583283900+c.lower,98713962871832+c.upper)) = pointBounds18085 := by
 decide +kernel
def cuts18086 : List PrefixCut := [⟨47,264580147,264580309⟩,
⟨120,676968353,676968764⟩,
⟨128,724974764,724975203⟩]
theorem checked18086 : checkPrefixCuts (2^48) 2374500353 9 Manual.Count131072.C018086.packed 128 cuts18086 = true := by
 decide +kernel
def pointBounds18086 : List (Nat × Nat × Nat) := [(2374548480,98714572167673,98714951756206),(2374623232,98714984555879,98715364144661)]
theorem point_links_checked18086 : (cuts18086.take 2).map (fun c => (2374500353-1+2*2^9*c.k,98714307587526+c.lower,98714687175897+c.upper)) = pointBounds18086 := by
 decide +kernel
def cuts18087 : List PrefixCut := [⟨65,361405502,361405720⟩,
⟨128,715452207,715452638⟩]
theorem checked18087 : checkPrefixCuts (2^48) 2374631425 9 Manual.Count131072.C018087.packed 128 cuts18087 = true := by
 decide +kernel
def pointBounds18087 : List (Nat × Nat × Nat) := [(2374697984,98715393967792,98715773556820)]
theorem point_links_checked18087 : (cuts18087.take 1).map (fun c => (2374631425-1+2*2^9*c.k,98715032562290+c.lower,98715412151100+c.upper)) = pointBounds18087 := by
 decide +kernel
def cuts18088 : List PrefixCut := [⟨10,56774597,56774633⟩,
⟨83,469360929,469361218⟩,
⟨128,723353973,723354417⟩]
theorem checked18088 : checkPrefixCuts (2^48) 2374762497 9 Manual.Count131072.C018088.packed 128 cuts18088 = true := by
 decide +kernel
def pointBounds18088 : List (Nat × Nat × Nat) := [(2374772736,98715804789094,98716184378371),(2374847488,98716217375426,98716596964956)]
theorem point_links_checked18088 : (cuts18088.take 2).map (fun c => (2374762497-1+2*2^9*c.k,98715748014497+c.lower,98716127603738+c.upper)) = pointBounds18088 := by
 decide +kernel
def cuts18089 : List PrefixCut := [⟨28,153128289,153128382⟩,
⟨101,560947932,560948276⟩,
⟨128,711699269,711699705⟩]
theorem checked18089 : checkPrefixCuts (2^48) 2374893569 9 Manual.Count131072.C018089.packed 128 cuts18089 = true := by
 decide +kernel
def pointBounds18089 : List (Nat × Nat × Nat) := [(2374922240,98716624496759,98717004086537),(2374996992,98717032316402,98717411906431)]
theorem point_links_checked18089 : (cuts18089.take 2).map (fun c => (2374893569-1+2*2^9*c.k,98716471368470+c.lower,98716850958155+c.upper)) = pointBounds18089 := by
 decide +kernel
def cuts18090 : List PrefixCut := [⟨46,255870306,255870460⟩,
⟨119,671130431,671130836⟩,
⟨128,717585648,717586083⟩]
theorem checked18090 : checkPrefixCuts (2^48) 2375024641 9 Manual.Count131072.C018090.packed 128 cuts18090 = true := by
 decide +kernel
def pointBounds18090 : List (Nat × Nat × Nat) := [(2375071744,98717438938045,98717818528320),(2375146496,98717854198170,98718233788696)]
theorem point_links_checked18090 : (cuts18090.take 2).map (fun c => (2375024641-1+2*2^9*c.k,98717183067739+c.lower,98717562657860+c.upper)) = pointBounds18090 := by
 decide +kernel
def cuts18091 : List PrefixCut := [⟨64,359903749,359903967⟩,
⟨128,721812077,721812519⟩]
theorem checked18091 : checkPrefixCuts (2^48) 2375155713 9 Manual.Count131072.C018091.packed 128 cuts18091 = true := by
 decide +kernel
def pointBounds18091 : List (Nat × Nat × Nat) := [(2375221248,98718260557136,98718640147910)]
theorem point_links_checked18091 : (cuts18091.take 1).map (fun c => (2375155713-1+2*2^9*c.k,98717900653387+c.lower,98718280243943+c.upper)) = pointBounds18091 := by
 decide +kernel
def cuts18092 : List PrefixCut := [⟨9,48348493,48348524⟩,
⟨82,458118494,458118779⟩,
⟨128,719757776,719758218⟩]
theorem checked18092 : checkPrefixCuts (2^48) 2375286785 9 Manual.Count131072.C018092.packed 128 cuts18092 = true := by
 decide +kernel
def pointBounds18092 : List (Nat × Nat × Nat) := [(2375296000,98718670813957,98719050404986),(2375370752,98719080583958,98719460175241)]
theorem point_links_checked18092 : (cuts18092.take 2).map (fun c => (2375286785-1+2*2^9*c.k,98718622465464+c.lower,98719002056462+c.upper)) = pointBounds18092 := by
 decide +kernel
def cuts18093 : List PrefixCut := [⟨27,150961604,150961699⟩,
⟨100,566274862,566275211⟩,
⟨128,723391374,723391820⟩]
theorem checked18093 : checkPrefixCuts (2^48) 2375417857 9 Manual.Count131072.C018093.packed 128 cuts18093 = true := by
 decide +kernel
def pointBounds18093 : List (Nat × Nat × Nat) := [(2375445504,98719493184844,98719872776379),(2375520256,98719908498102,98720288089891)]
theorem point_links_checked18093 : (cuts18093.take 2).map (fun c => (2375417857-1+2*2^9*c.k,98719342223240+c.lower,98719721814680+c.upper)) = pointBounds18093 := by
 decide +kernel
def cuts18094 : List PrefixCut := [⟨45,245979453,245979604⟩,
⟨118,649181188,649181586⟩,
⟨128,704749283,704749715⟩]
theorem checked18094 : checkPrefixCuts (2^48) 2375548929 9 Manual.Count131072.C018094.packed 128 cuts18094 = true := by
 decide +kernel
def pointBounds18094 : List (Nat × Nat × Nat) := [(2375595008,98720311594067,98720691186104),(2375669760,98720714795802,98721094388086)]
theorem point_links_checked18094 : (cuts18094.take 2).map (fun c => (2375548929-1+2*2^9*c.k,98720065614614+c.lower,98720445206500+c.upper)) = pointBounds18094 := by
 decide +kernel
def cuts18095 : List PrefixCut := [⟨63,350701417,350701628⟩,
⟨128,717387612,717388047⟩]
theorem checked18095 : checkPrefixCuts (2^48) 2375680001 9 Manual.Count131072.C018095.packed 128 cuts18095 = true := by
 decide +kernel
def pointBounds18095 : List (Nat × Nat × Nat) := [(2375744512,98721121065314,98721500657843)]
theorem point_links_checked18095 : (cuts18095.take 1).map (fun c => (2375680001-1+2*2^9*c.k,98720770363897+c.lower,98721149956215+c.upper)) = pointBounds18095 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S2.B000252
