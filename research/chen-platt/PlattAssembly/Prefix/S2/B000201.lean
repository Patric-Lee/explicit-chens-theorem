import PlattAssemblyKernel
import PlattCertificates.Count131072.C016432
import PlattCertificates.Count131072.C016433
import PlattCertificates.Count131072.C016434
import PlattCertificates.Count131072.C016435
import PlattCertificates.Count131072.C016436
import PlattCertificates.Count131072.C016437
import PlattCertificates.Count131072.C016438
import PlattCertificates.Count131072.C016439
import PlattCertificates.Count131072.C016440
import PlattCertificates.Count131072.C016441
import PlattCertificates.Count131072.C016442
import PlattCertificates.Count131072.C016443
import PlattCertificates.Count131072.C016444
import PlattCertificates.Count131072.C016445
import PlattCertificates.Count131072.C016446
import PlattCertificates.Count131072.C016447
import PlattCertificates.Count131072.C016448
import PlattCertificates.Count131072.C016449
import PlattCertificates.Count131072.C016450
import PlattCertificates.Count131072.C016451
import PlattCertificates.Count131072.C016452
import PlattCertificates.Count131072.C016453
import PlattCertificates.Count131072.C016454
import PlattCertificates.Count131072.C016455
import PlattCertificates.Count131072.C016456
import PlattCertificates.Count131072.C016457
import PlattCertificates.Count131072.C016458
import PlattCertificates.Count131072.C016459
import PlattCertificates.Count131072.C016460
import PlattCertificates.Count131072.C016461
import PlattCertificates.Count131072.C016462
import PlattCertificates.Count131072.C016463
namespace ChenEffective.PlattWindow.Assembly.Prefix.S2.B000201
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts16432 : List PrefixCut := [⟨7,40309266,40309292⟩,
⟨73,453569863,453570152⟩,
⟨128,791943408,791943912⟩]
theorem checked16432 : checkPrefixCuts (2^48) 2157707265 9 Manual.Count131072.C016432.packed 128 cuts16432 = true := by
 decide +kernel
def pointBounds16432 : List (Nat × Nat × Nat) := [(2157714432,97463250810140,97463629620730),(2157782016,97463664070737,97464042881590)]
theorem point_links_checked16432 : (cuts16432.take 2).map (fun c => (2157707265-1+2*2^9*c.k,97463210500874+c.lower,97463589311438+c.upper)) = pointBounds16432 := by
 decide +kernel
def cuts16433 : List PrefixCut := [⟨11,64177779,64177822⟩,
⟨77,474542869,474543173⟩,
⟨128,790590825,790591330⟩]
theorem checked16433 : checkPrefixCuts (2^48) 2157838337 9 Manual.Count131072.C016433.packed 128 cuts16433 = true := by
 decide +kernel
def pointBounds16433 : List (Nat × Nat × Nat) := [(2157849600,97464066622061,97464445433172),(2157917184,97464476987151,97464855798523)]
theorem point_links_checked16433 : (cuts16433.take 2).map (fun c => (2157838337-1+2*2^9*c.k,97464002444282+c.lower,97464381255350+c.upper)) = pointBounds16433 := by
 decide +kernel
def cuts16434 : List PrefixCut := [⟨15,92217264,92217321⟩,
⟨81,503730540,503730859⟩,
⟨128,795629775,795630282⟩]
theorem checked16434 : checkPrefixCuts (2^48) 2157969409 9 Manual.Count131072.C016434.packed 128 cuts16434 = true := by
 decide +kernel
def pointBounds16434 : List (Nat × Nat × Nat) := [(2157984768,97464885252371,97465264064001),(2158052352,97465296765647,97465675577539)]
theorem point_links_checked16434 : (cuts16434.take 2).map (fun c => (2157969409-1+2*2^9*c.k,97464793035107+c.lower,97465171846680+c.upper)) = pointBounds16434 := by
 decide +kernel
def cuts16435 : List PrefixCut := [⟨19,120905429,120905507⟩,
⟨85,527175952,527176290⟩,
⟨128,795711910,795712415⟩]
theorem checked16435 : checkPrefixCuts (2^48) 2158100481 9 Manual.Count131072.C016435.packed 128 cuts16435 = true := by
 decide +kernel
def pointBounds16435 : List (Nat × Nat × Nat) := [(2158119936,97465709570311,97466088382469),(2158187520,97466115840834,97466494653252)]
theorem point_links_checked16435 : (cuts16435.take 2).map (fun c => (2158100481-1+2*2^9*c.k,97465588664882+c.lower,97465967476962+c.upper)) = pointBounds16435 := by
 decide +kernel
def cuts16436 : List PrefixCut := [⟨23,144242890,144242982⟩,
⟨89,549575029,549575380⟩,
⟨128,788360298,788360796⟩]
theorem checked16436 : checkPrefixCuts (2^48) 2158231553 9 Manual.Count131072.C016436.packed 128 cuts16436 = true := by
 decide +kernel
def pointBounds16436 : List (Nat × Nat × Nat) := [(2158255104,97466528619682,97466907432359),(2158322688,97466933951821,97467312764757)]
theorem point_links_checked16436 : (cuts16436.take 2).map (fun c => (2158231553-1+2*2^9*c.k,97466384376792+c.lower,97466763189377+c.upper)) = pointBounds16436 := by
 decide +kernel
def cuts16437 : List PrefixCut := [⟨27,162361030,162361137⟩,
⟨93,575883564,575883930⟩,
⟨128,784661091,784661591⟩]
theorem checked16437 : checkPrefixCuts (2^48) 2158362625 9 Manual.Count131072.C016437.packed 128 cuts16437 = true := by
 decide +kernel
def pointBounds16437 : List (Nat × Nat × Nat) := [(2158390272,97467335098120,97467713911310),(2158457856,97467748620654,97468127434103)]
theorem point_links_checked16437 : (cuts16437.take 2).map (fun c => (2158362625-1+2*2^9*c.k,97467172737090+c.lower,97467551550173+c.upper)) = pointBounds16437 := by
 decide +kernel
def cuts16438 : List PrefixCut := [⟨31,192995587,192995711⟩,
⟨97,605579340,605579722⟩,
⟨128,798305275,798305778⟩]
theorem checked16438 : checkPrefixCuts (2^48) 2158493697 9 Manual.Count131072.C016438.packed 128 cuts16438 = true := by
 decide +kernel
def pointBounds16438 : List (Nat × Nat × Nat) := [(2158525440,97468150393768,97468529207475),(2158593024,97468562977521,97468941791486)]
theorem point_links_checked16438 : (cuts16438.take 2).map (fun c => (2158493697-1+2*2^9*c.k,97467957398181+c.lower,97468336211764+c.upper)) = pointBounds16438 := by
 decide +kernel
def cuts16439 : List PrefixCut := [⟨35,215281142,215281280⟩,
⟨101,630316516,630316920⟩,
⟨128,799039091,799039603⟩]
theorem checked16439 : checkPrefixCuts (2^48) 2158624769 9 Manual.Count131072.C016439.packed 128 cuts16439 = true := by
 decide +kernel
def pointBounds16439 : List (Nat × Nat × Nat) := [(2158660608,97468970984598,97469349798822),(2158728192,97469386019972,97469764834462)]
theorem point_links_checked16439 : (cuts16439.take 2).map (fun c => (2158624769-1+2*2^9*c.k,97468755703456+c.lower,97469134517542+c.upper)) = pointBounds16439 := by
 decide +kernel
def cuts16440 : List PrefixCut := [⟨39,244083252,244083408⟩,
⟨105,654398862,654399281⟩,
⟨128,799512179,799512690⟩]
theorem checked16440 : checkPrefixCuts (2^48) 2158755841 9 Manual.Count131072.C016440.packed 128 cuts16440 = true := by
 decide +kernel
def pointBounds16440 : List (Nat × Nat × Nat) := [(2158795776,97469798825799,97470177640553),(2158863360,97470209141409,97470587956426)]
theorem point_links_checked16440 : (cuts16440.take 2).map (fun c => (2158755841-1+2*2^9*c.k,97469554742547+c.lower,97469933557145+c.upper)) = pointBounds16440 := by
 decide +kernel
def cuts16441 : List PrefixCut := [⟨43,265450190,265450359⟩,
⟨109,670003624,670004046⟩,
⟨128,780298598,780299092⟩]
theorem checked16441 : checkPrefixCuts (2^48) 2158886913 9 Manual.Count131072.C016441.packed 128 cuts16441 = true := by
 decide +kernel
def pointBounds16441 : List (Nat × Nat × Nat) := [(2158930944,97470619704916,97470998520194),(2158998528,97471024258350,97471403073881)]
theorem point_links_checked16441 : (cuts16441.take 2).map (fun c => (2158886913-1+2*2^9*c.k,97470354254726+c.lower,97470733069835+c.upper)) = pointBounds16441 := by
 decide +kernel
def cuts16442 : List PrefixCut := [⟨47,295549380,295549568⟩,
⟨113,695905684,695906130⟩,
⟨128,789898316,789898821⟩]
theorem checked16442 : checkPrefixCuts (2^48) 2159017985 9 Manual.Count131072.C016442.packed 128 cuts16442 = true := by
 decide +kernel
def pointBounds16442 : List (Nat × Nat × Nat) := [(2159066112,97471430102704,97471808918495),(2159133696,97471830459008,97472209275057)]
theorem point_links_checked16442 : (cuts16442.take 2).map (fun c => (2159017985-1+2*2^9*c.k,97471134553324+c.lower,97471513368927+c.upper)) = pointBounds16442 := by
 decide +kernel
def cuts16443 : List PrefixCut := [⟨51,316258803,316259002⟩,
⟨117,724933071,724933529⟩,
⟨128,789589758,789590258⟩]
theorem checked16443 : checkPrefixCuts (2^48) 2159149057 9 Manual.Count131072.C016443.packed 128 cuts16443 = true := by
 decide +kernel
def pointBounds16443 : List (Nat × Nat × Nat) := [(2159201280,97472240710443,97472619526750),(2159268864,97472649384711,97473028201277)]
theorem point_links_checked16443 : (cuts16443.take 2).map (fun c => (2159149057-1+2*2^9*c.k,97471924451640+c.lower,97472303267748+c.upper)) = pointBounds16443 := by
 decide +kernel
def cuts16444 : List PrefixCut := [⟨55,346872486,346872705⟩,
⟨121,762690488,762690965⟩,
⟨128,804923303,804923807⟩]
theorem checked16444 : checkPrefixCuts (2^48) 2159280129 9 Manual.Count131072.C016444.packed 128 cuts16444 = true := by
 decide +kernel
def pointBounds16444 : List (Nat × Nat × Nat) := [(2159336448,97473060913884,97473439730711),(2159404032,97473476731886,97473855548971)]
theorem point_links_checked16444 : (cuts16444.take 2).map (fun c => (2159280129-1+2*2^9*c.k,97472714041398+c.lower,97473092858006+c.upper)) = pointBounds16444 := by
 decide +kernel
def cuts16445 : List PrefixCut := [⟨59,367836805,367837040⟩,
⟨125,781412828,781413327⟩,
⟨128,798878410,798878921⟩]
theorem checked16445 : checkPrefixCuts (2^48) 2159411201 9 Manual.Count131072.C016445.packed 128 cuts16445 = true := by
 decide +kernel
def pointBounds16445 : List (Nat × Nat × Nat) := [(2159471616,97473886801506,97474265618853),(2159539200,97474300377529,97474679195140)]
theorem point_links_checked16445 : (cuts16445.take 2).map (fun c => (2159411201-1+2*2^9*c.k,97473518964701+c.lower,97473897781813+c.upper)) = pointBounds16445 := by
 decide +kernel
def cuts16446 : List PrefixCut := [⟨63,394794100,394794351⟩,
⟨128,799872620,799873131⟩]
theorem checked16446 : checkPrefixCuts (2^48) 2159542273 9 Manual.Count131072.C016446.packed 128 cuts16446 = true := by
 decide +kernel
def pointBounds16446 : List (Nat × Nat × Nat) := [(2159606784,97474712637211,97475091455085)]
theorem point_links_checked16446 : (cuts16446.take 1).map (fun c => (2159542273-1+2*2^9*c.k,97474317843111+c.lower,97474696660734+c.upper)) = pointBounds16446 := by
 decide +kernel
def cuts16447 : List PrefixCut := [⟨1,7689596,7689600⟩,
⟨67,419923479,419923745⟩,
⟨128,797869226,797869731⟩]
theorem checked16447 : checkPrefixCuts (2^48) 2159673345 9 Manual.Count131072.C016447.packed 128 cuts16447 = true := by
 decide +kernel
def pointBounds16447 : List (Nat × Nat × Nat) := [(2159674368,97475125405327,97475504223465),(2159741952,97475537639210,97475916457610)]
theorem point_links_checked16447 : (cuts16447.take 2).map (fun c => (2159673345-1+2*2^9*c.k,97475117715731+c.lower,97475496533865+c.upper)) = pointBounds16447 := by
 decide +kernel
def cuts16448 : List PrefixCut := [⟨5,28931947,28931966⟩,
⟨71,441400784,441401066⟩,
⟨128,795475052,795475561⟩]
theorem checked16448 : checkPrefixCuts (2^48) 2159804417 9 Manual.Count131072.C016448.packed 128 cuts16448 = true := by
 decide +kernel
def pointBounds16448 : List (Nat × Nat × Nat) := [(2159809536,97475944516904,97476323335562),(2159877120,97476356985741,97476735804662)]
theorem point_links_checked16448 : (cuts16448.take 2).map (fun c => (2159804417-1+2*2^9*c.k,97475915584957+c.lower,97476294403596+c.upper)) = pointBounds16448 := by
 decide +kernel
def cuts16449 : List PrefixCut := [⟨9,54993377,54993412⟩,
⟨75,477470495,477470800⟩,
⟨128,811324947,811325468⟩]
theorem checked16449 : checkPrefixCuts (2^48) 2159935489 9 Manual.Count131072.C016449.packed 128 cuts16449 = true := by
 decide +kernel
def pointBounds16449 : List (Nat × Nat × Nat) := [(2159944704,97476766053386,97477144872569),(2160012288,97477188530504,97477567349957)]
theorem point_links_checked16449 : (cuts16449.take 2).map (fun c => (2159935489-1+2*2^9*c.k,97476711060009+c.lower,97477089879157+c.upper)) = pointBounds16449 := by
 decide +kernel
def cuts16450 : List PrefixCut := [⟨13,77533272,77533321⟩,
⟨79,493338406,493338718⟩,
⟨128,802154227,802154733⟩]
theorem checked16450 : checkPrefixCuts (2^48) 2160066561 9 Manual.Count131072.C016450.packed 128 cuts16450 = true := by
 decide +kernel
def pointBounds16450 : List (Nat × Nat × Nat) := [(2160079872,97477599918228,97477978737946),(2160147456,97478015723362,97478394543343)]
theorem point_links_checked16450 : (cuts16450.take 2).map (fun c => (2160066561-1+2*2^9*c.k,97477522384956+c.lower,97477901204625+c.upper)) = pointBounds16450 := by
 decide +kernel
def cuts16451 : List PrefixCut := [⟨17,105803603,105803669⟩,
⟨83,515067855,515068181⟩,
⟨128,795460546,795461049⟩]
theorem checked16451 : checkPrefixCuts (2^48) 2160197633 9 Manual.Count131072.C016451.packed 128 cuts16451 = true := by
 decide +kernel
def pointBounds16451 : List (Nat × Nat × Nat) := [(2160215040,97478430342786,97478809163027),(2160282624,97478839607038,97479218427539)]
theorem point_links_checked16451 : (cuts16451.take 2).map (fun c => (2160197633-1+2*2^9*c.k,97478324539183+c.lower,97478703359358+c.upper)) = pointBounds16451 := by
 decide +kernel
def cuts16452 : List PrefixCut := [⟨21,131204007,131204088⟩,
⟨87,535882504,535882839⟩,
⟨128,792285351,792285847⟩]
theorem checked16452 : checkPrefixCuts (2^48) 2160328705 9 Manual.Count131072.C016452.packed 128 cuts16452 = true := by
 decide +kernel
def pointBounds16452 : List (Nat × Nat × Nat) := [(2160350208,97479251203736,97479630024495),(2160417792,97479655882233,97480034703246)]
theorem point_links_checked16452 : (cuts16452.take 2).map (fun c => (2160328705-1+2*2^9*c.k,97479119999729+c.lower,97479498820407+c.upper)) = pointBounds16452 := by
 decide +kernel
def cuts16453 : List PrefixCut := [⟨25,155559022,155559120⟩,
⟨91,569722796,569723158⟩,
⟨128,794712821,794713320⟩]
theorem checked16453 : checkPrefixCuts (2^48) 2160459777 9 Manual.Count131072.C016453.packed 128 cuts16453 = true := by
 decide +kernel
def pointBounds16453 : List (Nat × Nat × Nat) := [(2160485376,97480067844102,97480446665374),(2160552960,97480482007876,97480860829412)]
theorem point_links_checked16453 : (cuts16453.take 2).map (fun c => (2160459777-1+2*2^9*c.k,97479912285080+c.lower,97480291106254+c.upper)) = pointBounds16453 := by
 decide +kernel
def cuts16454 : List PrefixCut := [⟨29,173527511,173527620⟩,
⟨95,584408460,584408833⟩,
⟨128,788932237,788932739⟩]
theorem checked16454 : checkPrefixCuts (2^48) 2160590849 9 Manual.Count131072.C016454.packed 128 cuts16454 = true := by
 decide +kernel
def pointBounds16454 : List (Nat × Nat × Nat) := [(2160620544,97480880525412,97481259347194),(2160688128,97481291406361,97481670228407)]
theorem point_links_checked16454 : (cuts16454.take 2).map (fun c => (2160590849-1+2*2^9*c.k,97480706997901+c.lower,97481085819574+c.upper)) = pointBounds16454 := by
 decide +kernel
def cuts16455 : List PrefixCut := [⟨33,202306032,202306161⟩,
⟨99,619935080,619935474⟩,
⟨128,798003114,798003615⟩]
theorem checked16455 : checkPrefixCuts (2^48) 2160721921 9 Manual.Count131072.C016455.packed 128 cuts16455 = true := by
 decide +kernel
def pointBounds16455 : List (Nat × Nat × Nat) := [(2160755712,97481698236170,97482077058474),(2160823296,97482115865218,97482494687787)]
theorem point_links_checked16455 : (cuts16455.take 2).map (fun c => (2160721921-1+2*2^9*c.k,97481495930138+c.lower,97481874752313+c.upper)) = pointBounds16455 := by
 decide +kernel
def cuts16456 : List PrefixCut := [⟨37,232774371,232774518⟩,
⟨103,640477734,640478143⟩,
⟨128,796521880,796522386⟩]
theorem checked16456 : checkPrefixCuts (2^48) 2160852993 9 Manual.Count131072.C016456.packed 128 cuts16456 = true := by
 decide +kernel
def pointBounds16456 : List (Nat × Nat × Nat) := [(2160890880,97482526707623,97482905530446),(2160958464,97482934410986,97483313234071)]
theorem point_links_checked16456 : (cuts16456.take 2).map (fun c => (2160852993-1+2*2^9*c.k,97482293933252+c.lower,97482672755928+c.upper)) = pointBounds16456 := by
 decide +kernel
def cuts16457 : List PrefixCut := [⟨41,261154941,261155103⟩,
⟨107,663622958,663623377⟩,
⟨128,796083013,796083517⟩]
theorem checked16457 : checkPrefixCuts (2^48) 2160984065 9 Manual.Count131072.C016457.packed 128 cuts16457 = true := by
 decide +kernel
def pointBounds16457 : List (Nat × Nat × Nat) := [(2161026048,97483351610073,97483730433417),(2161093632,97483754078090,97484132901691)]
theorem point_links_checked16457 : (cuts16457.take 2).map (fun c => (2160984065-1+2*2^9*c.k,97483090455132+c.lower,97483469278314+c.upper)) = pointBounds16457 := by
 decide +kernel
def cuts16458 : List PrefixCut := [⟨45,281587126,281587304⟩,
⟨111,690542006,690542447⟩,
⟨128,795383453,795383962⟩]
theorem checked16458 : checkPrefixCuts (2^48) 2161115137 9 Manual.Count131072.C016458.packed 128 cuts16458 = true := by
 decide +kernel
def pointBounds16458 : List (Nat × Nat × Nat) := [(2161161216,97484168125271,97484546949135),(2161228800,97484577080151,97484955904278)]
theorem point_links_checked16458 : (cuts16458.take 2).map (fun c => (2161115137-1+2*2^9*c.k,97483886538145+c.lower,97484265361831+c.upper)) = pointBounds16458 := by
 decide +kernel
def cuts16459 : List PrefixCut := [⟨49,308528629,308528824⟩,
⟨115,724750875,724751330⟩,
⟨128,807316569,807317077⟩]
theorem checked16459 : checkPrefixCuts (2^48) 2161246209 9 Manual.Count131072.C016459.packed 128 cuts16459 = true := by
 decide +kernel
def pointBounds16459 : List (Nat × Nat × Nat) := [(2161296384,97484990450227,97485369274617),(2161363968,97485406672473,97485785497123)]
theorem point_links_checked16459 : (cuts16459.take 2).map (fun c => (2161246209-1+2*2^9*c.k,97484681921598+c.lower,97485060745793+c.upper)) = pointBounds16459 := by
 decide +kernel
def cuts16460 : List PrefixCut := [⟨53,323225330,323225534⟩,
⟨119,734342866,734343330⟩,
⟨128,785259586,785260084⟩]
theorem checked16460 : checkPrefixCuts (2^48) 2161377281 9 Manual.Count131072.C016460.packed 128 cuts16460 = true := by
 decide +kernel
def pointBounds16460 : List (Nat × Nat × Nat) := [(2161431552,97485812463497,97486191288404),(2161499136,97486223581033,97486602406200)]
theorem point_links_checked16460 : (cuts16460.take 2).map (fun c => (2161377281-1+2*2^9*c.k,97485489238167+c.lower,97485868062870+c.upper)) = pointBounds16460 := by
 decide +kernel
def cuts16461 : List PrefixCut := [⟨57,359276295,359276523⟩,
⟨123,765680350,765680836⟩,
⟨128,797582725,797583232⟩]
theorem checked16461 : checkPrefixCuts (2^48) 2161508353 9 Manual.Count131072.C016461.packed 128 cuts16461 = true := by
 decide +kernel
def pointBounds16461 : List (Nat × Nat × Nat) := [(2161566720,97486633774048,97487012599477),(2161634304,97487040178103,97487419003790)]
theorem point_links_checked16461 : (cuts16461.take 2).map (fun c => (2161508353-1+2*2^9*c.k,97486274497753+c.lower,97486653322954+c.upper)) = pointBounds16461 := by
 decide +kernel
def cuts16462 : List PrefixCut := [⟨61,370322169,370322403⟩,
⟨127,782560173,782560665⟩,
⟨128,789200666,789201163⟩]
theorem checked16462 : checkPrefixCuts (2^48) 2161639425 9 Manual.Count131072.C016462.packed 128 cuts16462 = true := by
 decide +kernel
def pointBounds16462 : List (Nat × Nat × Nat) := [(2161701888,97487442402647,97487821228589),(2161769472,97487854640651,97488233466851)]
theorem point_links_checked16462 : (cuts16462.take 2).map (fun c => (2161639425-1+2*2^9*c.k,97487072080478+c.lower,97487450906186+c.upper)) = pointBounds16462 := by
 decide +kernel
def cuts16463 : List PrefixCut := [⟨65,396860958,396861212⟩,
⟨128,786939481,786939977⟩]
theorem checked16463 : checkPrefixCuts (2^48) 2161770497 9 Manual.Count131072.C016463.packed 128 cuts16463 = true := by
 decide +kernel
def pointBounds16463 : List (Nat × Nat × Nat) := [(2161837056,97488258142102,97488636968561)]
theorem point_links_checked16463 : (cuts16463.take 1).map (fun c => (2161770497-1+2*2^9*c.k,97487861281144+c.lower,97488240107349+c.upper)) = pointBounds16463 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S2.B000201
