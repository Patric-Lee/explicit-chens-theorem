import PlattAssemblyKernel
import PlattCertificates.Count131072.C013392
import PlattCertificates.Count131072.C013393
import PlattCertificates.Count131072.C013394
import PlattCertificates.Count131072.C013395
import PlattCertificates.Count131072.C013396
import PlattCertificates.Count131072.C013397
import PlattCertificates.Count131072.C013398
import PlattCertificates.Count131072.C013399
import PlattCertificates.Count131072.C013400
import PlattCertificates.Count131072.C013401
import PlattCertificates.Count131072.C013402
import PlattCertificates.Count131072.C013403
import PlattCertificates.Count131072.C013404
import PlattCertificates.Count131072.C013405
import PlattCertificates.Count131072.C013406
import PlattCertificates.Count131072.C013407
import PlattCertificates.Count131072.C013408
import PlattCertificates.Count131072.C013409
import PlattCertificates.Count131072.C013410
import PlattCertificates.Count131072.C013411
import PlattCertificates.Count131072.C013412
import PlattCertificates.Count131072.C013413
import PlattCertificates.Count131072.C013414
import PlattCertificates.Count131072.C013415
import PlattCertificates.Count131072.C013416
import PlattCertificates.Count131072.C013417
import PlattCertificates.Count131072.C013418
import PlattCertificates.Count131072.C013419
import PlattCertificates.Count131072.C013420
import PlattCertificates.Count131072.C013421
import PlattCertificates.Count131072.C013422
import PlattCertificates.Count131072.C013423
namespace ChenEffective.PlattWindow.Assembly.Prefix.S2.B000106
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts13392 : List PrefixCut := [⟨20,151036517,151036625⟩,
⟨74,569577890,569578296⟩,
⟨128,987466019,987466720⟩]
theorem checked13392 : checkPrefixCuts (2^48) 1759248385 9 Manual.Count131072.C013392.packed 128 cuts13392 = true := by
 decide +kernel
def pointBounds13392 : List (Nat × Nat × Nat) := [(1759268864,94776869355002,94777246362054),(1759324160,94777287896375,94777664903725),(1759379456,94777705784504,94778082792149)]
theorem point_links_checked13392 : (cuts13392.take 3).map (fun c => (1759248385-1+2*2^9*c.k,94776718318485+c.lower,94777095325429+c.upper)) = pointBounds13392 := by
 decide +kernel
def cuts13393 : List PrefixCut := [⟨54,414195460,414195760⟩,
⟨108,829337826,829338418⟩,
⟨128,977953983,977954680⟩]
theorem checked13393 : checkPrefixCuts (2^48) 1759379457 9 Manual.Count131072.C013393.packed 128 cuts13393 = true := by
 decide +kernel
def pointBounds13393 : List (Nat × Nat × Nat) := [(1759434752,94778119979964,94778496987909),(1759490048,94778535122330,94778912130567)]
theorem point_links_checked13393 : (cuts13393.take 2).map (fun c => (1759379457-1+2*2^9*c.k,94777705784504+c.lower,94778082792149+c.upper)) = pointBounds13393 := by
 decide +kernel
def cuts13394 : List PrefixCut := [⟨34,263953480,263953668⟩,
⟨88,683708832,683709315⟩,
⟨128,1000276294,1000277005⟩]
theorem checked13394 : checkPrefixCuts (2^48) 1759510529 9 Manual.Count131072.C013394.packed 128 cuts13394 = true := by
 decide +kernel
def pointBounds13394 : List (Nat × Nat × Nat) := [(1759545344,94778947691967,94779324700497),(1759600640,94779367447319,94779744456144)]
theorem point_links_checked13394 : (cuts13394.take 2).map (fun c => (1759510529-1+2*2^9*c.k,94778683738487+c.lower,94779060746829+c.upper)) = pointBounds13394 := by
 decide +kernel
def cuts13395 : List PrefixCut := [⟨14,106853838,106853918⟩,
⟨68,520664291,520664664⟩,
⟨122,932542367,932543039⟩,
⟨128,978607925,978608631⟩]
theorem checked13395 : checkPrefixCuts (2^48) 1759641601 9 Manual.Count131072.C013395.packed 128 cuts13395 = true := by
 decide +kernel
def pointBounds13395 : List (Nat × Nat × Nat) := [(1759655936,94779790868619,94780167877752),(1759711232,94780204679072,94780581688498),(1759766528,94780616557148,94780993566873)]
theorem point_links_checked13395 : (cuts13395.take 3).map (fun c => (1759641601-1+2*2^9*c.k,94779684014781+c.lower,94780061023834+c.upper)) = pointBounds13395 := by
 decide +kernel
def cuts13396 : List PrefixCut := [⟨48,379075157,379075426⟩,
⟨102,798764457,798765026⟩,
⟨128,994049836,994050545⟩]
theorem checked13396 : checkPrefixCuts (2^48) 1759772673 9 Manual.Count131072.C013396.packed 128 cuts13396 = true := by
 decide +kernel
def pointBounds13396 : List (Nat × Nat × Nat) := [(1759821824,94781041697863,94781418707891),(1759877120,94781461387163,94781838397491)]
theorem point_links_checked13396 : (cuts13396.take 2).map (fun c => (1759772673-1+2*2^9*c.k,94780662622706+c.lower,94781039632465+c.upper)) = pointBounds13396 := by
 decide +kernel
def cuts13397 : List PrefixCut := [⟨28,215434271,215434421⟩,
⟨82,629179855,629180296⟩,
⟨128,986778598,986779292⟩]
theorem checked13397 : checkPrefixCuts (2^48) 1759903745 9 Manual.Count131072.C013397.packed 128 cuts13397 = true := by
 decide +kernel
def pointBounds13397 : List (Nat × Nat × Nat) := [(1759932416,94781872106813,94782249117431),(1759987712,94782285852397,94782662863306)]
theorem point_links_checked13397 : (cuts13397.take 2).map (fun c => (1759903745-1+2*2^9*c.k,94781656672542+c.lower,94782033683010+c.upper)) = pointBounds13397 := by
 decide +kernel
def cuts13398 : List PrefixCut := [⟨8,61251420,61251464⟩,
⟨62,479288851,479289195⟩,
⟨116,890436567,890437204⟩,
⟨128,981427846,981428549⟩]
theorem checked13398 : checkPrefixCuts (2^48) 1760034817 9 Manual.Count131072.C013398.packed 128 cuts13398 = true := by
 decide +kernel
def pointBounds13398 : List (Nat × Nat × Nat) := [(1760043008,94782704702560,94783081713766),(1760098304,94783122739991,94783499751497),(1760153600,94783533887707,94783910899506)]
theorem point_links_checked13398 : (cuts13398.take 3).map (fun c => (1760034817-1+2*2^9*c.k,94782643451140+c.lower,94783020462302+c.upper)) = pointBounds13398 := by
 decide +kernel
def cuts13399 : List PrefixCut := [⟨42,325260773,325261006⟩,
⟨96,733984067,733984591⟩,
⟨128,980075429,980076125⟩]
theorem checked13399 : checkPrefixCuts (2^48) 1760165889 9 Manual.Count131072.C013399.packed 128 cuts13399 = true := by
 decide +kernel
def pointBounds13399 : List (Nat × Nat × Nat) := [(1760208896,94783950139759,94784327151857),(1760264192,94784358863053,94784735875442)]
theorem point_links_checked13399 : (cuts13399.take 2).map (fun c => (1760165889-1+2*2^9*c.k,94783624878986+c.lower,94784001890851+c.upper)) = pointBounds13399 := by
 decide +kernel
def cuts13400 : List PrefixCut := [⟨22,165497427,165497545⟩,
⟨76,573555562,573555970⟩,
⟨128,972807010,972807705⟩]
theorem checked13400 : checkPrefixCuts (2^48) 1760296961 9 Manual.Count131072.C013400.packed 128 cuts13400 = true := by
 decide +kernel
def pointBounds13400 : List (Nat × Nat × Nat) := [(1760319488,94784770451842,94785147464521),(1760374784,94785178509977,94785555522946)]
theorem point_links_checked13400 : (cuts13400.take 2).map (fun c => (1760296961-1+2*2^9*c.k,94784604954415+c.lower,94784981966976+c.upper)) = pointBounds13400 := by
 decide +kernel
def cuts13401 : List PrefixCut := [⟨2,15189543,15189554⟩,
⟨56,424021435,424021737⟩,
⟨110,840994501,840995097⟩,
⟨128,975452697,975453392⟩]
theorem checked13401 : checkPrefixCuts (2^48) 1760428033 9 Manual.Count131072.C013401.packed 128 cuts13401 = true := by
 decide +kernel
def pointBounds13401 : List (Nat × Nat × Nat) := [(1760430080,94785592950968,94785969964235),(1760485376,94786001782860,94786378796418),(1760540672,94786418755926,94786795769778)]
theorem point_links_checked13401 : (cuts13401.take 3).map (fun c => (1760428033-1+2*2^9*c.k,94785577761425+c.lower,94785954774681+c.upper)) = pointBounds13401 := by
 decide +kernel
def cuts13402 : List PrefixCut := [⟨36,273068972,273069164⟩,
⟨90,683141257,683141738⟩,
⟨128,982574009,982574705⟩]
theorem checked13402 : checkPrefixCuts (2^48) 1760559105 9 Manual.Count131072.C013402.packed 128 cuts13402 = true := by
 decide +kernel
def pointBounds13402 : List (Nat × Nat × Nat) := [(1760595968,94786826283094,94787203297237),(1760651264,94787236355379,94787613369811)]
theorem point_links_checked13402 : (cuts13402.take 2).map (fun c => (1760559105-1+2*2^9*c.k,94786553214122+c.lower,94786930228073+c.upper)) = pointBounds13402 := by
 decide +kernel
def cuts13403 : List PrefixCut := [⟨16,129970635,129970726⟩,
⟨70,543694146,543694531⟩,
⟨124,962679842,962680525⟩,
⟨128,991293799,991294503⟩]
theorem checked13403 : checkPrefixCuts (2^48) 1760690177 9 Manual.Count131072.C013403.packed 128 cuts13403 = true := by
 decide +kernel
def pointBounds13403 : List (Nat × Nat × Nat) := [(1760706560,94787665758766,94788042773504),(1760761856,94788079482277,94788456497309),(1760817152,94788498467973,94788875483303)]
theorem point_links_checked13403 : (cuts13403.take 3).map (fun c => (1760690177-1+2*2^9*c.k,94787535788131+c.lower,94787912802778+c.upper)) = pointBounds13403 := by
 decide +kernel
def cuts13404 : List PrefixCut := [⟨50,390358562,390358842⟩,
⟨104,808678572,808679150⟩,
⟨128,998412834,998413545⟩]
theorem checked13404 : checkPrefixCuts (2^48) 1760821249 9 Manual.Count131072.C013404.packed 128 cuts13404 = true := by
 decide +kernel
def pointBounds13404 : List (Nat × Nat × Nat) := [(1760872448,94788917440492,94789294456123),(1760927744,94789335760502,94789712776431)]
theorem point_links_checked13404 : (cuts13404.take 2).map (fun c => (1760821249-1+2*2^9*c.k,94788527081930+c.lower,94788904097281+c.upper)) = pointBounds13404 := by
 decide +kernel
def cuts13405 : List PrefixCut := [⟨30,230011196,230011356⟩,
⟨84,645427912,645428369⟩,
⟨128,982834391,982835091⟩]
theorem checked13405 : checkPrefixCuts (2^48) 1760952321 9 Manual.Count131072.C013405.packed 128 cuts13405 = true := by
 decide +kernel
def pointBounds13405 : List (Nat × Nat × Nat) := [(1760983040,94789755505960,94790132522182),(1761038336,94790170922676,94790547939195)]
theorem point_links_checked13405 : (cuts13405.take 2).map (fun c => (1760952321-1+2*2^9*c.k,94789525494764+c.lower,94789902510826+c.upper)) = pointBounds13405 := by
 decide +kernel
def cuts13406 : List PrefixCut := [⟨10,76718426,76718480⟩,
⟨64,485076664,485077008⟩,
⟨118,890705089,890705723⟩,
⟨128,972053012,972053706⟩]
theorem checked13406 : checkPrefixCuts (2^48) 1761083393 9 Manual.Count131072.C013406.packed 128 cuts13406 = true := by
 decide +kernel
def pointBounds13406 : List (Nat × Nat × Nat) := [(1761093632,94790585047581,94790962064397),(1761148928,94790993405819,94791370422925),(1761204224,94791399034244,94791776051640)]
theorem point_links_checked13406 : (cuts13406.take 3).map (fun c => (1761083393-1+2*2^9*c.k,94790508329155+c.lower,94790885345917+c.upper)) = pointBounds13406 := by
 decide +kernel
def cuts13407 : List PrefixCut := [⟨44,345203832,345204075⟩,
⟨98,763272111,763272651⟩,
⟨128,990359458,990360159⟩]
theorem checked13407 : checkPrefixCuts (2^48) 1761214465 9 Manual.Count131072.C013407.packed 128 cuts13407 = true := by
 decide +kernel
def pointBounds13407 : List (Nat × Nat × Nat) := [(1761259520,94791825585999,94792202603698),(1761314816,94792243654278,94792620672274)]
theorem point_links_checked13407 : (cuts13407.take 2).map (fun c => (1761214465-1+2*2^9*c.k,94791480382167+c.lower,94791857399623+c.upper)) = pointBounds13407 := by
 decide +kernel
def cuts13408 : List PrefixCut := [⟨24,192565778,192565911⟩,
⟨78,595586502,595586922⟩,
⟨128,977022339,977023032⟩]
theorem checked13408 : checkPrefixCuts (2^48) 1761345537 9 Manual.Count131072.C013408.packed 128 cuts13408 = true := by
 decide +kernel
def pointBounds13408 : List (Nat × Nat × Nat) := [(1761370112,94792663307403,94793040325693),(1761425408,94793066328127,94793443346704)]
theorem point_links_checked13408 : (cuts13408.take 2).map (fun c => (1761345537-1+2*2^9*c.k,94792470741625+c.lower,94792847759782+c.upper)) = pointBounds13408 := by
 decide +kernel
def cuts13409 : List PrefixCut := [⟨4,29721806,29721826⟩,
⟨58,444701495,444701813⟩,
⟨112,855034388,855035002⟩,
⟨128,980943934,980944636⟩]
theorem checked13409 : checkPrefixCuts (2^48) 1761476609 9 Manual.Count131072.C013409.packed 128 cuts13409 = true := by
 decide +kernel
def pointBounds13409 : List (Nat × Nat × Nat) := [(1761480704,94793477485770,94793854504640),(1761536000,94793892465459,94794269484627),(1761591296,94794302798352,94794679817816)]
theorem point_links_checked13409 : (cuts13409.take 3).map (fun c => (1761476609-1+2*2^9*c.k,94793447763964+c.lower,94793824782814+c.upper)) = pointBounds13409 := by
 decide +kernel
def cuts13410 : List PrefixCut := [⟨38,289843051,289843260⟩,
⟨92,699511012,699511513⟩,
⟨128,979752422,979753120⟩]
theorem checked13410 : checkPrefixCuts (2^48) 1761607681 9 Manual.Count131072.C013410.packed 128 cuts13410 = true := by
 decide +kernel
def pointBounds13410 : List (Nat × Nat × Nat) := [(1761646592,94794718550949,94795095570710),(1761701888,94795128218910,94795505238963)]
theorem point_links_checked13410 : (cuts13410.take 2).map (fun c => (1761607681-1+2*2^9*c.k,94794428707898+c.lower,94794805727450+c.upper)) = pointBounds13410 := by
 decide +kernel
def cuts13411 : List PrefixCut := [⟨18,137402410,137402507⟩,
⟨72,550239956,550240351⟩,
⟨126,970573457,970574149⟩,
⟨128,985271310,985272013⟩]
theorem checked13411 : checkPrefixCuts (2^48) 1761738753 9 Manual.Count131072.C013411.packed 128 cuts13411 = true := by
 decide +kernel
def pointBounds13411 : List (Nat × Nat × Nat) := [(1761757184,94795545862730,94795922883077),(1761812480,94795958700276,94796335720921),(1761867776,94796379033777,94796756054719)]
theorem point_links_checked13411 : (cuts13411.take 3).map (fun c => (1761738753-1+2*2^9*c.k,94795408460320+c.lower,94795785480570+c.upper)) = pointBounds13411 := by
 decide +kernel
def cuts13412 : List PrefixCut := [⟨52,399871228,399871510⟩,
⟨106,816983345,816983923⟩,
⟨128,981524111,981524807⟩]
theorem checked13412 : checkPrefixCuts (2^48) 1761869825 9 Manual.Count131072.C013412.packed 128 cuts13412 = true := by
 decide +kernel
def pointBounds13412 : List (Nat × Nat × Nat) := [(1761923072,94796793602858,94797170624093),(1761978368,94797210714975,94797587736506)]
theorem point_links_checked13412 : (cuts13412.take 2).map (fun c => (1761869825-1+2*2^9*c.k,94796393731630+c.lower,94796770752583+c.upper)) = pointBounds13412 := by
 decide +kernel
def cuts13413 : List PrefixCut := [⟨32,245209862,245210037⟩,
⟨86,659420492,659420963⟩,
⟨128,979214680,979215379⟩]
theorem checked13413 : checkPrefixCuts (2^48) 1762000897 9 Manual.Count131072.C013413.packed 128 cuts13413 = true := by
 decide +kernel
def pointBounds13413 : List (Nat × Nat × Nat) := [(1762033664,94797620465603,94797997487427),(1762088960,94798034676233,94798411698353)]
theorem point_links_checked13413 : (cuts13413.take 2).map (fun c => (1762000897-1+2*2^9*c.k,94797375255741+c.lower,94797752277390+c.upper)) = pointBounds13413 := by
 decide +kernel
def cuts13414 : List PrefixCut := [⟨12,89770980,89771044⟩,
⟨66,503636102,503636466⟩,
⟨120,916050578,916051233⟩,
⟨128,976585936,976586634⟩]
theorem checked13414 : checkPrefixCuts (2^48) 1762131969 9 Manual.Count131072.C013414.packed 128 cuts13414 = true := by
 decide +kernel
def pointBounds13414 : List (Nat × Nat × Nat) := [(1762144256,94798444241401,94798821263813),(1762199552,94798858106523,94799235129235),(1762254848,94799270520999,94799647544002)]
theorem point_links_checked13414 : (cuts13414.take 3).map (fun c => (1762131969-1+2*2^9*c.k,94798354470421+c.lower,94798731492769+c.upper)) = pointBounds13414 := by
 decide +kernel
def cuts13415 : List PrefixCut := [⟨46,352025951,352026202⟩,
⟨100,769365837,769366388⟩,
⟨128,988811455,988812160⟩]
theorem checked13415 : checkPrefixCuts (2^48) 1762263041 9 Manual.Count131072.C013415.packed 128 cuts13415 = true := by
 decide +kernel
def pointBounds13415 : List (Nat × Nat × Nat) := [(1762310144,94799683082308,94800060105605),(1762365440,94800100422194,94800477445791)]
theorem point_links_checked13415 : (cuts13415.take 2).map (fun c => (1762263041-1+2*2^9*c.k,94799331056357+c.lower,94799708079403+c.upper)) = pointBounds13415 := by
 decide +kernel
def cuts13416 : List PrefixCut := [⟨26,203790507,203790654⟩,
⟨80,613278513,613278953⟩,
⟨128,986981177,986981885⟩]
theorem checked13416 : checkPrefixCuts (2^48) 1762394113 9 Manual.Count131072.C013416.packed 128 cuts13416 = true := by
 decide +kernel
def pointBounds13416 : List (Nat × Nat × Nat) := [(1762420736,94800523658319,94800900682217),(1762476032,94800933146325,94801310170516)]
theorem point_links_checked13416 : (cuts13416.take 2).map (fun c => (1762394113-1+2*2^9*c.k,94800319867812+c.lower,94800696891563+c.upper)) = pointBounds13416 := by
 decide +kernel
def cuts13417 : List PrefixCut := [⟨6,46312853,46312885⟩,
⟨60,462642266,462642594⟩,
⟨114,871612614,871613231⟩,
⟨128,976847364,976848056⟩]
theorem checked13417 : checkPrefixCuts (2^48) 1762525185 9 Manual.Count131072.C013417.packed 128 cuts13417 = true := by
 decide +kernel
def pointBounds13417 : List (Nat × Nat × Nat) := [(1762531328,94801353161842,94801730186333),(1762586624,94801769491255,94802146516042),(1762641920,94802178461603,94802555486679)]
theorem point_links_checked13417 : (cuts13417.take 3).map (fun c => (1762525185-1+2*2^9*c.k,94801306848989+c.lower,94801683873448+c.upper)) = pointBounds13417 := by
 decide +kernel
def cuts13418 : List PrefixCut := [⟨40,307395699,307395922⟩,
⟨94,726400455,726400979⟩,
⟨128,981405591,981406298⟩]
theorem checked13418 : checkPrefixCuts (2^48) 1762656257 9 Manual.Count131072.C013418.packed 128 cuts13418 = true := by
 decide +kernel
def pointBounds13418 : List (Nat × Nat × Nat) := [(1762697216,94802591092052,94802968117426),(1762752512,94803010096808,94803387122483)]
theorem point_links_checked13418 : (cuts13418.take 2).map (fun c => (1762656257-1+2*2^9*c.k,94802283696353+c.lower,94802660721504+c.upper)) = pointBounds13418 := by
 decide +kernel
def cuts13419 : List PrefixCut := [⟨20,157758983,157759093⟩,
⟨74,577695517,577695926⟩,
⟨128,993148186,993148886⟩]
theorem checked13419 : checkPrefixCuts (2^48) 1762787329 9 Manual.Count131072.C013419.packed 128 cuts13419 = true := by
 decide +kernel
def pointBounds13419 : List (Nat × Nat × Nat) := [(1762807808,94803422860927,94803799886895),(1762863104,94803842797461,94804219823728),(1762918400,94804258250130,94804635276688)]
theorem point_links_checked13419 : (cuts13419.take 3).map (fun c => (1762787329-1+2*2^9*c.k,94803265101944+c.lower,94803642127802+c.upper)) = pointBounds13419 := by
 decide +kernel
def cuts13420 : List PrefixCut := [⟨54,407456531,407456818⟩,
⟨108,818572423,818573002⟩,
⟨128,976150135,976150825⟩]
theorem checked13420 : checkPrefixCuts (2^48) 1762918401 9 Manual.Count131072.C013420.packed 128 cuts13420 = true := by
 decide +kernel
def pointBounds13420 : List (Nat × Nat × Nat) := [(1762973696,94804665706661,94805042733506),(1763028992,94805076822553,94805453849690)]
theorem point_links_checked13420 : (cuts13420.take 2).map (fun c => (1762918401-1+2*2^9*c.k,94804258250130+c.lower,94804635276688+c.upper)) = pointBounds13420 := by
 decide +kernel
def cuts13421 : List PrefixCut := [⟨34,266776346,266776539⟩,
⟨88,678983974,678984457⟩,
⟨128,990924980,990925683⟩]
theorem checked13421 : checkPrefixCuts (2^48) 1763049473 9 Manual.Count131072.C013421.packed 128 cuts13421 = true := by
 decide +kernel
def pointBounds13421 : List (Nat × Nat × Nat) := [(1763084288,94805501176611,94805878204052),(1763139584,94805913384239,94806290411970)]
theorem point_links_checked13421 : (cuts13421.take 2).map (fun c => (1763049473-1+2*2^9*c.k,94805234400265+c.lower,94805611427513+c.upper)) = pointBounds13421 := by
 decide +kernel
def cuts13422 : List PrefixCut := [⟨14,111907483,111907563⟩,
⟨68,524089209,524089578⟩,
⟨122,946634077,946634746⟩,
⟨128,988456830,988457528⟩]
theorem checked13422 : checkPrefixCuts (2^48) 1763180545 9 Manual.Count131072.C013422.packed 128 cuts13422 = true := by
 decide +kernel
def pointBounds13422 : List (Nat × Nat × Nat) := [(1763194880,94806337232728,94806714260759),(1763250176,94806749414454,94807126442774),(1763305472,94807171959322,94807548987942)]
theorem point_links_checked13422 : (cuts13422.take 3).map (fun c => (1763180545-1+2*2^9*c.k,94806225325245+c.lower,94806602353196+c.upper)) = pointBounds13422 := by
 decide +kernel
def cuts13423 : List PrefixCut := [⟨48,374004543,374004810⟩,
⟨102,789978382,789978947⟩,
⟨128,985031457,985032159⟩]
theorem checked13423 : checkPrefixCuts (2^48) 1763311617 9 Manual.Count131072.C013423.packed 128 cuts13423 = true := by
 decide +kernel
def pointBounds13423 : List (Nat × Nat × Nat) := [(1763360768,94807587786618,94807964815534),(1763416064,94808003760457,94808380789671)]
theorem point_links_checked13423 : (cuts13423.take 2).map (fun c => (1763311617-1+2*2^9*c.k,94807213782075+c.lower,94807590810724+c.upper)) = pointBounds13423 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S2.B000106
