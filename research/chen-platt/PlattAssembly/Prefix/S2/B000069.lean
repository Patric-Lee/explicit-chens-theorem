import PlattAssemblyKernel
import PlattCertificates.Count131072.C012208
import PlattCertificates.Count131072.C012209
import PlattCertificates.Count131072.C012210
import PlattCertificates.Count131072.C012211
import PlattCertificates.Count131072.C012212
import PlattCertificates.Count131072.C012213
import PlattCertificates.Count131072.C012214
import PlattCertificates.Count131072.C012215
import PlattCertificates.Count131072.C012216
import PlattCertificates.Count131072.C012217
import PlattCertificates.Count131072.C012218
import PlattCertificates.Count131072.C012219
import PlattCertificates.Count131072.C012220
import PlattCertificates.Count131072.C012221
import PlattCertificates.Count131072.C012222
import PlattCertificates.Count131072.C012223
import PlattCertificates.Count131072.C012224
import PlattCertificates.Count131072.C012225
import PlattCertificates.Count131072.C012226
import PlattCertificates.Count131072.C012227
import PlattCertificates.Count131072.C012228
import PlattCertificates.Count131072.C012229
import PlattCertificates.Count131072.C012230
import PlattCertificates.Count131072.C012231
import PlattCertificates.Count131072.C012232
import PlattCertificates.Count131072.C012233
import PlattCertificates.Count131072.C012234
import PlattCertificates.Count131072.C012235
import PlattCertificates.Count131072.C012236
import PlattCertificates.Count131072.C012237
import PlattCertificates.Count131072.C012238
import PlattCertificates.Count131072.C012239
namespace ChenEffective.PlattWindow.Assembly.Prefix.S2.B000069
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts12208 : List PrefixCut := [⟨6,48431455,48431492⟩,
⟨55,461144345,461144697⟩,
⟨104,882442244,882442918⟩,
⟨128,1088962945,1088963774⟩]
theorem checked12208 : checkPrefixCuts (2^48) 1604059137 9 Manual.Count131072.C012208.packed 128 cuts12208 = true := by
 decide +kernel
def pointBounds12208 : List (Nat × Nat × Nat) := [(1604065280,93553113893876,93553490003105),(1604115456,93553526606766,93553902716310),(1604165632,93553947904665,93554324014531)]
theorem point_links_checked12208 : (cuts12208.take 3).map (fun c => (1604059137-1+2*2^9*c.k,93553065462421+c.lower,93553441571613+c.upper)) = pointBounds12208 := by
 decide +kernel
def cuts12209 : List PrefixCut := [⟨25,217746971,217747133⟩,
⟨74,626736591,626737064⟩,
⟨123,1042556110,1042556895⟩,
⟨128,1086944514,1086945331⟩]
theorem checked12209 : checkPrefixCuts (2^48) 1604190209 9 Manual.Count131072.C012209.packed 128 cuts12209 = true := by
 decide +kernel
def pointBounds12209 : List (Nat × Nat × Nat) := [(1604215808,93554372172337,93554748282520),(1604265984,93554781161957,93555157272451),(1604316160,93555196981476,93555573092282)]
theorem point_links_checked12209 : (cuts12209.take 3).map (fun c => (1604190209-1+2*2^9*c.k,93554154425366+c.lower,93554530535387+c.upper)) = pointBounds12209 := by
 decide +kernel
def cuts12210 : List PrefixCut := [⟨44,373347969,373348250⟩,
⟨93,784053634,784054233⟩,
⟨128,1078259109,1078259934⟩]
theorem checked12210 : checkPrefixCuts (2^48) 1604321281 9 Manual.Count131072.C012210.packed 128 cuts12210 = true := by
 decide +kernel
def pointBounds12210 : List (Nat × Nat × Nat) := [(1604366336,93555614717849,93555990828968),(1604416512,93556025423514,93556401534951)]
theorem point_links_checked12210 : (cuts12210.take 2).map (fun c => (1604321281-1+2*2^9*c.k,93555241369880+c.lower,93555617480718+c.upper)) = pointBounds12210 := by
 decide +kernel
def cuts12211 : List PrefixCut := [⟨14,122978414,122978509⟩,
⟨63,541026490,541026896⟩,
⟨112,951518302,951519022⟩,
⟨128,1087468931,1087469754⟩]
theorem checked12211 : checkPrefixCuts (2^48) 1604452353 9 Manual.Count131072.C012211.packed 128 cuts12211 = true := by
 decide +kernel
def pointBounds12211 : List (Nat × Nat × Nat) := [(1604466688,93556442607403,93556818719161),(1604516864,93556860655479,93557236767548),(1604567040,93557271147291,93557647259674)]
theorem point_links_checked12211 : (cuts12211.take 3).map (fun c => (1604452353-1+2*2^9*c.k,93556319628989+c.lower,93556695740652+c.upper)) = pointBounds12211 := by
 decide +kernel
def cuts12212 : List PrefixCut := [⟨33,275054486,275054693⟩,
⟨82,684643461,684643976⟩,
⟨128,1087203703,1087204525⟩]
theorem checked12212 : checkPrefixCuts (2^48) 1604583425 9 Manual.Count131072.C012212.packed 128 cuts12212 = true := by
 decide +kernel
def pointBounds12212 : List (Nat × Nat × Nat) := [(1604617216,93557682152406,93558058265099),(1604667392,93558091741381,93558467854382)]
theorem point_links_checked12212 : (cuts12212.take 2).map (fun c => (1604583425-1+2*2^9*c.k,93557407097920+c.lower,93557783210406+c.upper)) = pointBounds12212 := by
 decide +kernel
def cuts12213 : List PrefixCut := [⟨3,23679646,23679664⟩,
⟨52,443416292,443416625⟩,
⟨101,858930336,858930981⟩,
⟨128,1089571051,1089571870⟩]
theorem checked12213 : checkPrefixCuts (2^48) 1604714497 9 Manual.Count131072.C012213.packed 128 cuts12213 = true := by
 decide +kernel
def pointBounds12213 : List (Nat × Nat × Nat) := [(1604717568,93558517981269,93558894094595),(1604767744,93558937717915,93559313831556),(1604817920,93559353231959,93559729345912)]
theorem point_links_checked12213 : (cuts12213.take 3).map (fun c => (1604714497-1+2*2^9*c.k,93558494301623+c.lower,93558870414931+c.upper)) = pointBounds12213 := by
 decide +kernel
def cuts12214 : List PrefixCut := [⟨22,187140465,187140609⟩,
⟨71,603505372,603505828⟩,
⟨120,1009159180,1009159945⟩,
⟨128,1080537526,1080538344⟩]
theorem checked12214 : checkPrefixCuts (2^48) 1604845569 9 Manual.Count131072.C012214.packed 128 cuts12214 = true := by
 decide +kernel
def pointBounds12214 : List (Nat × Nat × Nat) := [(1604868096,93559771013139,93560147127410),(1604918272,93560187378046,93560563492629),(1604968448,93560593031854,93560969146746)]
theorem point_links_checked12214 : (cuts12214.take 3).map (fun c => (1604845569-1+2*2^9*c.k,93559583872674+c.lower,93559959986801+c.upper)) = pointBounds12214 := by
 decide +kernel
def cuts12215 : List PrefixCut := [⟨41,347766700,347766964⟩,
⟨90,764969492,764970073⟩,
⟨128,1091322076,1091322899⟩]
theorem checked12215 : checkPrefixCuts (2^48) 1604976641 9 Manual.Count131072.C012215.packed 128 cuts12215 = true := by
 decide +kernel
def pointBounds12215 : List (Nat × Nat × Nat) := [(1605018624,93561012176900,93561388292109),(1605068800,93561429379692,93561805495218)]
theorem point_links_checked12215 : (cuts12215.take 2).map (fun c => (1604976641-1+2*2^9*c.k,93560664410200+c.lower,93561040525145+c.upper)) = pointBounds12215 := by
 decide +kernel
def cuts12216 : List PrefixCut := [⟨11,91187903,91187972⟩,
⟨60,497316955,497317327⟩,
⟨109,908693936,908694617⟩,
⟨128,1068436613,1068437419⟩]
theorem checked12216 : checkPrefixCuts (2^48) 1605107713 9 Manual.Count131072.C012216.packed 128 cuts12216 = true := by
 decide +kernel
def pointBounds12216 : List (Nat × Nat × Nat) := [(1605118976,93561846920179,93562223036016),(1605169152,93562253049231,93562629165371),(1605219328,93562664426212,93563040542661)]
theorem point_links_checked12216 : (cuts12216.take 3).map (fun c => (1605107713-1+2*2^9*c.k,93561755732276+c.lower,93562131848044+c.upper)) = pointBounds12216 := by
 decide +kernel
def cuts12217 : List PrefixCut := [⟨30,260564130,260564324⟩,
⟨79,677000286,677000791⟩,
⟨128,1093949530,1093950352⟩]
theorem checked12217 : checkPrefixCuts (2^48) 1605238785 9 Manual.Count131072.C012217.packed 128 cuts12217 = true := by
 decide +kernel
def pointBounds12217 : List (Nat × Nat × Nat) := [(1605269504,93563084733019,93563460849787),(1605319680,93563501169175,93563877286254),(1605369856,93563918118419,93564294235815)]
theorem point_links_checked12217 : (cuts12217.take 3).map (fun c => (1605238785-1+2*2^9*c.k,93562824168889+c.lower,93563200285463+c.upper)) = pointBounds12217 := by
 decide +kernel
def cuts12218 : List PrefixCut := [⟨49,414656989,414657305⟩,
⟨98,830352924,830353551⟩,
⟨128,1091931404,1091932227⟩]
theorem checked12218 : checkPrefixCuts (2^48) 1605369857 9 Manual.Count131072.C012218.packed 128 cuts12218 = true := by
 decide +kernel
def pointBounds12218 : List (Nat × Nat × Nat) := [(1605420032,93564332775408,93564708893120),(1605470208,93564748471343,93565124589366)]
theorem point_links_checked12218 : (cuts12218.take 2).map (fun c => (1605369857-1+2*2^9*c.k,93563918118419+c.lower,93564294235815+c.upper)) = pointBounds12218 := by
 decide +kernel
def cuts12219 : List PrefixCut := [⟨19,161818497,161818619⟩,
⟨68,569423997,569424431⟩,
⟨117,984730371,984731111⟩,
⟨128,1077992800,1077993609⟩]
theorem checked12219 : checkPrefixCuts (2^48) 1605500929 9 Manual.Count131072.C012219.packed 128 cuts12219 = true := by
 decide +kernel
def pointBounds12219 : List (Nat × Nat × Nat) := [(1605520384,93565171868320,93565547986661),(1605570560,93565579473820,93565955592473),(1605620736,93565994780194,93566370899153)]
theorem point_links_checked12219 : (cuts12219.take 3).map (fun c => (1605500929-1+2*2^9*c.k,93565010049823+c.lower,93565386168042+c.upper)) = pointBounds12219 := by
 decide +kernel
def cuts12220 : List PrefixCut := [⟨38,326238161,326238411⟩,
⟨88,743972529,743973094⟩,
⟨128,1085617880,1085618705⟩]
theorem checked12220 : checkPrefixCuts (2^48) 1605632001 9 Manual.Count131072.C012220.packed 128 cuts12220 = true := by
 decide +kernel
def pointBounds12220 : List (Nat × Nat × Nat) := [(1605670912,93566414280784,93566790400062),(1605722112,93566832015152,93567208134745)]
theorem point_links_checked12220 : (cuts12220.take 2).map (fun c => (1605632001-1+2*2^9*c.k,93566088042623+c.lower,93566464161651+c.upper)) = pointBounds12220 := by
 decide +kernel
def cuts12221 : List PrefixCut := [⟨10,85366171,85366236⟩,
⟨60,504826821,504827203⟩,
⟨110,929883047,929883749⟩,
⟨128,1083425803,1083426619⟩]
theorem checked12221 : checkPrefixCuts (2^48) 1605763073 9 Manual.Count131072.C012221.packed 128 cuts12221 = true := by
 decide +kernel
def pointBounds12221 : List (Nat × Nat × Nat) := [(1605773312,93567259026674,93567635146592),(1605824512,93567678487324,93568054607559),(1605875712,93568103543550,93568479664105)]
theorem point_links_checked12221 : (cuts12221.take 3).map (fun c => (1605763073-1+2*2^9*c.k,93567173660503+c.lower,93567549780356+c.upper)) = pointBounds12221 := by
 decide +kernel
def cuts12222 : List PrefixCut := [⟨32,266942786,266942982⟩,
⟨82,683558820,683559330⟩,
⟨128,1074047900,1074048707⟩]
theorem checked12222 : checkPrefixCuts (2^48) 1605894145 9 Manual.Count131072.C012222.packed 128 cuts12222 = true := by
 decide +kernel
def pointBounds12222 : List (Nat × Nat × Nat) := [(1605926912,93568524029092,93568900149957),(1605978112,93568940645126,93569316766305)]
theorem point_links_checked12222 : (cuts12222.take 2).map (fun c => (1605894145-1+2*2^9*c.k,93568257086306+c.lower,93568633206975+c.upper)) = pointBounds12222 := by
 decide +kernel
def cuts12223 : List PrefixCut := [⟨4,33299698,33299723⟩,
⟨54,460054287,460054632⟩,
⟨104,885743766,885744435⟩,
⟨128,1088506684,1088507508⟩]
theorem checked12223 : checkPrefixCuts (2^48) 1606025217 9 Manual.Count131072.C012223.packed 128 cuts12223 = true := by
 decide +kernel
def pointBounds12223 : List (Nat × Nat × Nat) := [(1606029312,93569364433904,93569740555405),(1606080512,93569791188493,93570167310314),(1606131712,93570216877972,93570593000117)]
theorem point_links_checked12223 : (cuts12223.take 3).map (fun c => (1606025217-1+2*2^9*c.k,93569331134206+c.lower,93569707255682+c.upper)) = pointBounds12223 := by
 decide +kernel
def cuts12224 : List PrefixCut := [⟨26,216078381,216078544⟩,
⟨76,631401479,631401955⟩,
⟨126,1059503548,1059504344⟩,
⟨128,1078779212,1078780022⟩]
theorem checked12224 : checkPrefixCuts (2^48) 1606156289 9 Manual.Count131072.C012224.packed 128 cuts12224 = true := by
 decide +kernel
def pointBounds12224 : List (Nat × Nat × Nat) := [(1606182912,93570635719271,93571011841734),(1606234112,93571051042369,93571427165145),(1606285312,93571479144438,93571855267534)]
theorem point_links_checked12224 : (cuts12224.take 3).map (fun c => (1606156289-1+2*2^9*c.k,93570419640890+c.lower,93570795763190+c.upper)) = pointBounds12224 := by
 decide +kernel
def cuts12225 : List PrefixCut := [⟨48,406885325,406885634⟩,
⟨98,828827220,828827853⟩,
⟨128,1076764338,1076765157⟩]
theorem checked12225 : checkPrefixCuts (2^48) 1606287361 9 Manual.Count131072.C012225.packed 128 cuts12225 = true := by
 decide +kernel
def pointBounds12225 : List (Nat × Nat × Nat) := [(1606336512,93571905305427,93572281428846),(1606387712,93572327247322,93572703371065)]
theorem point_links_checked12225 : (cuts12225.take 2).map (fun c => (1606287361-1+2*2^9*c.k,93571498420102+c.lower,93571874543212+c.upper)) = pointBounds12225 := by
 decide +kernel
def cuts12226 : List PrefixCut := [⟨20,173290384,173290515⟩,
⟨70,598359234,598359685⟩,
⟨120,1028495554,1028496331⟩,
⟨128,1095774287,1095775116⟩]
theorem checked12226 : checkPrefixCuts (2^48) 1606418433 9 Manual.Count131072.C012226.packed 128 cuts12226 = true := by
 decide +kernel
def pointBounds12226 : List (Nat × Nat × Nat) := [(1606438912,93572748474824,93573124598884),(1606490112,93573173543674,93573549668054),(1606541312,93573603679994,93573979804700)]
theorem point_links_checked12226 : (cuts12226.take 3).map (fun c => (1606418433-1+2*2^9*c.k,93572575184440+c.lower,93572951308369+c.upper)) = pointBounds12226 := by
 decide +kernel
def cuts12227 : List PrefixCut := [⟨42,349703637,349703901⟩,
⟨92,783141282,783141875⟩,
⟨128,1089202261,1089203082⟩]
theorem checked12227 : checkPrefixCuts (2^48) 1606549505 9 Manual.Count131072.C012227.packed 128 cuts12227 = true := by
 decide +kernel
def pointBounds12227 : List (Nat × Nat × Nat) := [(1606592512,93574020662364,93574396787386),(1606643712,93574454100009,93574830225360)]
theorem point_links_checked12227 : (cuts12227.take 2).map (fun c => (1606549505-1+2*2^9*c.k,93573670958727+c.lower,93574047083485+c.upper)) = pointBounds12227 := by
 decide +kernel
def cuts12228 : List PrefixCut := [⟨14,122282303,122282393⟩,
⟨64,548684973,548685388⟩,
⟨114,968592376,968593108⟩,
⟨128,1087887775,1087888597⟩]
theorem checked12228 : checkPrefixCuts (2^48) 1606680577 9 Manual.Count131072.C012228.packed 128 cuts12228 = true := by
 decide +kernel
def pointBounds12228 : List (Nat × Nat × Nat) := [(1606694912,93574882443291,93575258568960),(1606746112,93575308845961,93575684971955),(1606797312,93575728753364,93576104879675)]
theorem point_links_checked12228 : (cuts12228.take 3).map (fun c => (1606680577-1+2*2^9*c.k,93574760160988+c.lower,93575136286567+c.upper)) = pointBounds12228 := by
 decide +kernel
def cuts12229 : List PrefixCut := [⟨36,305153120,305153350⟩,
⟨86,722231058,722231604⟩,
⟨128,1076062459,1076063274⟩]
theorem checked12229 : checkPrefixCuts (2^48) 1606811649 9 Manual.Count131072.C012229.packed 128 cuts12229 = true := by
 decide +kernel
def pointBounds12229 : List (Nat × Nat × Nat) := [(1606848512,93576153201883,93576529328514),(1606899712,93576570279821,93576946406768)]
theorem point_links_checked12229 : (cuts12229.take 2).map (fun c => (1606811649-1+2*2^9*c.k,93575848048763+c.lower,93576224175164+c.upper)) = pointBounds12229 := by
 decide +kernel
def cuts12230 : List PrefixCut := [⟨8,67787417,67787471⟩,
⟨58,493421593,493421974⟩,
⟨108,916589950,916590649⟩,
⟨128,1086659224,1086660055⟩]
theorem checked12230 : checkPrefixCuts (2^48) 1606942721 9 Manual.Count131072.C012230.packed 128 cuts12230 = true := by
 decide +kernel
def pointBounds12230 : List (Nat × Nat × Nat) := [(1606950912,93576991898639,93577368025909),(1607002112,93577417532815,93577793660412),(1607053312,93577840701172,93578216829087)]
theorem point_links_checked12230 : (cuts12230.take 3).map (fun c => (1606942721-1+2*2^9*c.k,93576924111222+c.lower,93577300238438+c.upper)) = pointBounds12230 := by
 decide +kernel
def cuts12231 : List PrefixCut := [⟨30,247831290,247831479⟩,
⟨80,679729780,679730295⟩,
⟨128,1093050392,1093051218⟩]
theorem checked12231 : checkPrefixCuts (2^48) 1607073793 9 Manual.Count131072.C012231.packed 128 cuts12231 = true := by
 decide +kernel
def pointBounds12231 : List (Nat × Nat × Nat) := [(1607104512,93578258601736,93578634729972),(1607155712,93578690500226,93579066628788)]
theorem point_links_checked12231 : (cuts12231.take 2).map (fun c => (1607073793-1+2*2^9*c.k,93578010770446+c.lower,93578386898493+c.upper)) = pointBounds12231 := by
 decide +kernel
def cuts12232 : List PrefixCut := [⟨2,15937107,15937119⟩,
⟨52,432046332,432046658⟩,
⟨102,857949298,857949941⟩,
⟨128,1080527248,1080528057⟩]
theorem checked12232 : checkPrefixCuts (2^48) 1607204865 9 Manual.Count131072.C012232.packed 128 cuts12232 = true := by
 decide +kernel
def pointBounds12232 : List (Nat × Nat × Nat) := [(1607206912,93579119757945,93579495886830),(1607258112,93579535867170,93579911996369),(1607309312,93579961770136,93580337899652)]
theorem point_links_checked12232 : (cuts12232.take 3).map (fun c => (1607204865-1+2*2^9*c.k,93579103820838+c.lower,93579479949711+c.upper)) = pointBounds12232 := by
 decide +kernel
def cuts12233 : List PrefixCut := [⟨24,199809124,199809273⟩,
⟨74,627611245,627611716⟩,
⟨124,1055399713,1055400507⟩,
⟨128,1089194943,1089195763⟩]
theorem checked12233 : checkPrefixCuts (2^48) 1607335937 9 Manual.Count131072.C012233.packed 128 cuts12233 = true := by
 decide +kernel
def pointBounds12233 : List (Nat × Nat × Nat) := [(1607360512,93580384157210,93580760287041),(1607411712,93580811959331,93581188089484),(1607462912,93581239747799,93581615878275)]
theorem point_links_checked12233 : (cuts12233.take 3).map (fun c => (1607335937-1+2*2^9*c.k,93580184348086+c.lower,93580560477768+c.upper)) = pointBounds12233 := by
 decide +kernel
def cuts12234 : List PrefixCut := [⟨46,388026087,388026376⟩,
⟨96,807732765,807733367⟩,
⟨128,1067044185,1067044985⟩]
theorem checked12234 : checkPrefixCuts (2^48) 1607467009 9 Manual.Count131072.C012234.packed 128 cuts12234 = true := by
 decide +kernel
def pointBounds12234 : List (Nat × Nat × Nat) := [(1607514112,93581661569116,93582037699907),(1607565312,93582081275794,93582457406898)]
theorem point_links_checked12234 : (cuts12234.take 2).map (fun c => (1607467009-1+2*2^9*c.k,93581273543029+c.lower,93581649673531+c.upper)) = pointBounds12234 := by
 decide +kernel
def cuts12235 : List PrefixCut := [⟨18,154428769,154428886⟩,
⟨68,583563379,583563819⟩,
⟨118,1015485515,1015486279⟩,
⟨128,1101623206,1101624036⟩]
theorem checked12235 : checkPrefixCuts (2^48) 1607598081 9 Manual.Count131072.C012235.packed 128 cuts12235 = true := by
 decide +kernel
def pointBounds12235 : List (Nat × Nat × Nat) := [(1607616512,93582495015983,93582871147402),(1607667712,93582924150593,93583300282335),(1607718912,93583356072729,93583732204795)]
theorem point_links_checked12235 : (cuts12235.take 3).map (fun c => (1607598081-1+2*2^9*c.k,93582340587214+c.lower,93582716718516+c.upper)) = pointBounds12235 := by
 decide +kernel
def cuts12236 : List PrefixCut := [⟨40,335966604,335966855⟩,
⟨90,751930074,751930637⟩,
⟨128,1073347373,1073348177⟩]
theorem checked12236 : checkPrefixCuts (2^48) 1607729153 9 Manual.Count131072.C012236.packed 128 cuts12236 = true := by
 decide +kernel
def pointBounds12236 : List (Nat × Nat × Nat) := [(1607770112,93583778177024,93584154309407),(1607821312,93584194140494,93584570273189)]
theorem point_links_checked12236 : (cuts12236.take 2).map (fun c => (1607729153-1+2*2^9*c.k,93583442210420+c.lower,93583818342552+c.upper)) = pointBounds12236 := by
 decide +kernel
def cuts12237 : List PrefixCut := [⟨12,97158916,97158990⟩,
⟨62,512045490,512045880⟩,
⟨112,931120054,931120764⟩,
⟨128,1065382177,1065382989⟩]
theorem checked12237 : checkPrefixCuts (2^48) 1607860225 9 Manual.Count131072.C012237.packed 128 cuts12237 = true := by
 decide +kernel
def pointBounds12237 : List (Nat × Nat × Nat) := [(1607872512,93584612716709,93584988849719),(1607923712,93585027603283,93585403736609),(1607974912,93585446677847,93585822811493)]
theorem point_links_checked12237 : (cuts12237.take 3).map (fun c => (1607860225-1+2*2^9*c.k,93584515557793+c.lower,93584891690729+c.upper)) = pointBounds12237 := by
 decide +kernel
def cuts12238 : List PrefixCut := [⟨34,283573900,283574111⟩,
⟨84,711899042,711899574⟩,
⟨128,1078598736,1078599542⟩]
theorem checked12238 : checkPrefixCuts (2^48) 1607991297 9 Manual.Count131072.C012238.packed 128 cuts12238 = true := by
 decide +kernel
def pointBounds12238 : List (Nat × Nat × Nat) := [(1608026112,93585864513870,93586240647829),(1608077312,93586292839012,93586668973292)]
theorem point_links_checked12238 : (cuts12238.take 2).map (fun c => (1607991297-1+2*2^9*c.k,93585580939970+c.lower,93585957073718+c.upper)) = pointBounds12238 := by
 decide +kernel
def cuts12239 : List PrefixCut := [⟨6,53385038,53385078⟩,
⟨56,479057605,479057968⟩,
⟨106,903316262,903316941⟩,
⟨128,1089012687,1089013502⟩]
theorem checked12239 : checkPrefixCuts (2^48) 1608122369 9 Manual.Count131072.C012239.packed 128 cuts12239 = true := by
 decide +kernel
def pointBounds12239 : List (Nat × Nat × Nat) := [(1608128512,93586712923744,93587089058338),(1608179712,93587138596311,93587514731228),(1608230912,93587562854968,93587938990201)]
theorem point_links_checked12239 : (cuts12239.take 3).map (fun c => (1608122369-1+2*2^9*c.k,93586659538706+c.lower,93587035673260+c.upper)) = pointBounds12239 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S2.B000069
