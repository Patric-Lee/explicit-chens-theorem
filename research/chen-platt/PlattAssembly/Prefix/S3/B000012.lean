import PlattAssemblyKernel
import PlattCertificates.Count131072.C020384
import PlattCertificates.Count131072.C020385
import PlattCertificates.Count131072.C020386
import PlattCertificates.Count131072.C020387
import PlattCertificates.Count131072.C020388
import PlattCertificates.Count131072.C020389
import PlattCertificates.Count131072.C020390
import PlattCertificates.Count131072.C020391
import PlattCertificates.Count131072.C020392
import PlattCertificates.Count131072.C020393
import PlattCertificates.Count131072.C020394
import PlattCertificates.Count131072.C020395
import PlattCertificates.Count131072.C020396
import PlattCertificates.Count131072.C020397
import PlattCertificates.Count131072.C020398
import PlattCertificates.Count131072.C020399
import PlattCertificates.Count131072.C020400
import PlattCertificates.Count131072.C020401
import PlattCertificates.Count131072.C020402
import PlattCertificates.Count131072.C020403
import PlattCertificates.Count131072.C020404
import PlattCertificates.Count131072.C020405
import PlattCertificates.Count131072.C020406
import PlattCertificates.Count131072.C020407
import PlattCertificates.Count131072.C020408
import PlattCertificates.Count131072.C020409
import PlattCertificates.Count131072.C020410
import PlattCertificates.Count131072.C020411
import PlattCertificates.Count131072.C020412
import PlattCertificates.Count131072.C020413
import PlattCertificates.Count131072.C020414
import PlattCertificates.Count131072.C020415
namespace ChenEffective.PlattWindow.Assembly.Prefix.S3.B000012
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts20384 : List PrefixCut := [⟨40,195664148,195664262⟩,
⟨122,611808980,611809332⟩,
⟨128,642419721,642420091⟩]
theorem checked20384 : checkPrefixCuts (2^48) 2675703809 9 Manual.Count131072.C020384.packed 128 cuts20384 = true := by
 decide +kernel
def pointBounds20384 : List (Nat × Nat × Nat) := [(2675744768,100267352357287,100267732871519),(2675828736,100267768502119,100268149016589)]
theorem point_links_checked20384 : (cuts20384.take 2).map (fun c => (2675703809-1+2*2^9*c.k,100267156693139+c.lower,100267537207257+c.upper)) = pointBounds20384 := by
 decide +kernel
def cuts20385 : List PrefixCut := [⟨76,377736952,377737174⟩,
⟨128,638180770,638181142⟩]
theorem checked20385 : checkPrefixCuts (2^48) 2675834881 9 Manual.Count131072.C020385.packed 128 cuts20385 = true := by
 decide +kernel
def pointBounds20385 : List (Nat × Nat × Nat) := [(2675912704,100268176849812,100268557364522)]
theorem point_links_checked20385 : (cuts20385.take 1).map (fun c => (2675834881-1+2*2^9*c.k,100267799112860+c.lower,100268179627348+c.upper)) = pointBounds20385 := by
 decide +kernel
def cuts20386 : List PrefixCut := [⟨30,143262876,143262961⟩,
⟨112,543170218,543170539⟩,
⟨128,623739207,623739574⟩]
theorem checked20386 : checkPrefixCuts (2^48) 2675965953 9 Manual.Count131072.C020386.packed 128 cuts20386 = true := by
 decide +kernel
def pointBounds20386 : List (Nat × Nat × Nat) := [(2675996672,100268580556506,100268961071451),(2676080640,100268980463848,100269360979029)]
theorem point_links_checked20386 : (cuts20386.take 2).map (fun c => (2675965953-1+2*2^9*c.k,100268437293630+c.lower,100268817808490+c.upper)) = pointBounds20386 := by
 decide +kernel
def cuts20387 : List PrefixCut := [⟨66,330054196,330054389⟩,
⟨128,633911179,633911548⟩]
theorem checked20387 : checkPrefixCuts (2^48) 2676097025 9 Manual.Count131072.C020387.packed 128 cuts20387 = true := by
 decide +kernel
def pointBounds20387 : List (Nat × Nat × Nat) := [(2676164608,100269391087033,100269771602453)]
theorem point_links_checked20387 : (cuts20387.take 1).map (fun c => (2676097025-1+2*2^9*c.k,100269061032837+c.lower,100269441548064+c.upper)) = pointBounds20387 := by
 decide +kernel
def cuts20388 : List PrefixCut := [⟨20,97602934,97602990⟩,
⟨102,507674486,507674780⟩,
⟨128,638612820,638613194⟩]
theorem checked20388 : checkPrefixCuts (2^48) 2676228097 9 Manual.Count131072.C020388.packed 128 cuts20388 = true := by
 decide +kernel
def pointBounds20388 : List (Nat × Nat × Nat) := [(2676248576,100269792546950,100270173062602),(2676332544,100270202618502,100270583134392)]
theorem point_links_checked20388 : (cuts20388.take 2).map (fun c => (2676228097-1+2*2^9*c.k,100269694944016+c.lower,100270075459612+c.upper)) = pointBounds20388 := by
 decide +kernel
def cuts20389 : List PrefixCut := [⟨56,281749585,281749750⟩,
⟨128,647941502,647941884⟩]
theorem checked20389 : checkPrefixCuts (2^48) 2676359169 9 Manual.Count131072.C020389.packed 128 cuts20389 = true := by
 decide +kernel
def pointBounds20389 : List (Nat × Nat × Nat) := [(2676416512,100270615306421,100270995822556)]
theorem point_links_checked20389 : (cuts20389.take 1).map (fun c => (2676359169-1+2*2^9*c.k,100270333556836+c.lower,100270714072806+c.upper)) = pointBounds20389 := by
 decide +kernel
def cuts20390 : List PrefixCut := [⟨10,50058766,50058794⟩,
⟨92,459355551,459355817⟩,
⟨128,635605779,635606147⟩]
theorem checked20390 : checkPrefixCuts (2^48) 2676490241 9 Manual.Count131072.C020390.packed 128 cuts20390 = true := by
 decide +kernel
def pointBounds20390 : List (Nat × Nat × Nat) := [(2676500480,100271031557104,100271412073484),(2676584448,100271440853889,100271821370507)]
theorem point_links_checked20390 : (cuts20390.take 2).map (fun c => (2676490241-1+2*2^9*c.k,100270981498338+c.lower,100271362014690+c.upper)) = pointBounds20390 := by
 decide +kernel
def cuts20391 : List PrefixCut := [⟨46,225882779,225882919⟩,
⟨128,633050760,633051136⟩]
theorem checked20391 : checkPrefixCuts (2^48) 2676621313 9 Manual.Count131072.C020391.packed 128 cuts20391 = true := by
 decide +kernel
def pointBounds20391 : List (Nat × Nat × Nat) := [(2676668416,100271842986896,100272223503756),(2676752384,100272250154877,100272630671973)]
theorem point_links_checked20391 : (cuts20391.take 2).map (fun c => (2676621313-1+2*2^9*c.k,100271617104117+c.lower,100271997620837+c.upper)) = pointBounds20391 := by
 decide +kernel
def cuts20392 : List PrefixCut := [⟨82,402318165,402318393⟩,
⟨128,635438277,635438639⟩]
theorem checked20392 : checkPrefixCuts (2^48) 2676752385 9 Manual.Count131072.C020392.packed 128 cuts20392 = true := by
 decide +kernel
def pointBounds20392 : List (Nat × Nat × Nat) := [(2676836352,100272652473042,100273032990366)]
theorem point_links_checked20392 : (cuts20392.take 1).map (fun c => (2676752385-1+2*2^9*c.k,100272250154877+c.lower,100272630671973+c.upper)) = pointBounds20392 := by
 decide +kernel
def cuts20393 : List PrefixCut := [⟨36,178859293,178859398⟩,
⟨118,582203728,582204071⟩,
⟨128,633199190,633199562⟩]
theorem checked20393 : checkPrefixCuts (2^48) 2676883457 9 Manual.Count131072.C020393.packed 128 cuts20393 = true := by
 decide +kernel
def pointBounds20393 : List (Nat × Nat × Nat) := [(2676920320,100273064452447,100273444970010),(2677004288,100273467796882,100273848314683)]
theorem point_links_checked20393 : (cuts20393.take 2).map (fun c => (2676883457-1+2*2^9*c.k,100272885593154+c.lower,100273266110612+c.upper)) = pointBounds20393 := by
 decide +kernel
def cuts20394 : List PrefixCut := [⟨72,355385469,355385677⟩,
⟨128,630539577,630539946⟩]
theorem checked20394 : checkPrefixCuts (2^48) 2677014529 9 Manual.Count131072.C020394.packed 128 cuts20394 = true := by
 decide +kernel
def pointBounds20394 : List (Nat × Nat × Nat) := [(2677088256,100273874177813,100274254695851)]
theorem point_links_checked20394 : (cuts20394.take 1).map (fun c => (2677014529-1+2*2^9*c.k,100273518792344+c.lower,100273899310174+c.upper)) = pointBounds20394 := by
 decide +kernel
def cuts20395 : List PrefixCut := [⟨26,126167290,126167365⟩,
⟨108,531997021,531997336⟩,
⟨128,626513544,626513914⟩]
theorem checked20395 : checkPrefixCuts (2^48) 2677145601 9 Manual.Count131072.C020395.packed 128 cuts20395 = true := by
 decide +kernel
def pointBounds20395 : List (Nat × Nat × Nat) := [(2677172224,100274275499211,100274656017485),(2677256192,100274681328942,100275061847456)]
theorem point_links_checked20395 : (cuts20395.take 2).map (fun c => (2677145601-1+2*2^9*c.k,100274149331921+c.lower,100274529850120+c.upper)) = pointBounds20395 := by
 decide +kernel
def cuts20396 : List PrefixCut := [⟨62,306464271,306464453⟩,
⟨128,631213770,631214146⟩]
theorem checked20396 : checkPrefixCuts (2^48) 2677276673 9 Manual.Count131072.C020396.packed 128 cuts20396 = true := by
 decide +kernel
def pointBounds20396 : List (Nat × Nat × Nat) := [(2677340160,100275082309736,100275462828487)]
theorem point_links_checked20396 : (cuts20396.take 1).map (fun c => (2677276673-1+2*2^9*c.k,100274775845465+c.lower,100275156364034+c.upper)) = pointBounds20396 := by
 decide +kernel
def cuts20397 : List PrefixCut := [⟨16,79162372,79162417⟩,
⟨98,483377006,483377288⟩,
⟨128,631288012,631288379⟩]
theorem checked20397 : checkPrefixCuts (2^48) 2677407745 9 Manual.Count131072.C020397.packed 128 cuts20397 = true := by
 decide +kernel
def pointBounds20397 : List (Nat × Nat × Nat) := [(2677424128,100275486221607,100275866740597),(2677508096,100275890436241,100276270955468)]
theorem point_links_checked20397 : (cuts20397.take 2).map (fun c => (2677407745-1+2*2^9*c.k,100275407059235+c.lower,100275787578180+c.upper)) = pointBounds20397 := by
 decide +kernel
def cuts20398 : List PrefixCut := [⟨52,263018820,263018976⟩,
⟨128,645448572,645448947⟩]
theorem checked20398 : checkPrefixCuts (2^48) 2677538817 9 Manual.Count131072.C020398.packed 128 cuts20398 = true := by
 decide +kernel
def pointBounds20398 : List (Nat × Nat × Nat) := [(2677592064,100276301366067,100276681885535)]
theorem point_links_checked20398 : (cuts20398.take 1).map (fun c => (2677538817-1+2*2^9*c.k,100276038347247+c.lower,100276418866559+c.upper)) = pointBounds20398 := by
 decide +kernel
def cuts20399 : List PrefixCut := [⟨6,30694813,30694832⟩,
⟨88,433189530,433189785⟩,
⟨128,630280167,630280540⟩]
theorem checked20399 : checkPrefixCuts (2^48) 2677669889 9 Manual.Count131072.C020399.packed 128 cuts20399 = true := by
 decide +kernel
def pointBounds20399 : List (Nat × Nat × Nat) := [(2677676032,100276714490632,100277095010338),(2677760000,100277116985349,100277497505291)]
theorem point_links_checked20399 : (cuts20399.take 2).map (fun c => (2677669889-1+2*2^9*c.k,100276683795819+c.lower,100277064315506+c.upper)) = pointBounds20399 := by
 decide +kernel
def cuts20400 : List PrefixCut := [⟨42,209806243,209806365⟩,
⟨124,616164825,616165185⟩,
⟨128,636661106,636661478⟩]
theorem checked20400 : checkPrefixCuts (2^48) 2677800961 9 Manual.Count131072.C020400.packed 128 cuts20400 = true := by
 decide +kernel
def pointBounds20400 : List (Nat × Nat × Nat) := [(2677843968,100277523882229,100277904402411),(2677927936,100277930240811,100278310761231)]
theorem point_links_checked20400 : (cuts20400.take 2).map (fun c => (2677800961-1+2*2^9*c.k,100277314075986+c.lower,100277694596046+c.upper)) = pointBounds20400 := by
 decide +kernel
def cuts20401 : List PrefixCut := [⟨78,385639386,385639606⟩,
⟨128,640518780,640519147⟩]
theorem checked20401 : checkPrefixCuts (2^48) 2677932033 9 Manual.Count131072.C020401.packed 128 cuts20401 = true := by
 decide +kernel
def pointBounds20401 : List (Nat × Nat × Nat) := [(2678011904,100278336376478,100278716897130)]
theorem point_links_checked20401 : (cuts20401.take 1).map (fun c => (2677932033-1+2*2^9*c.k,100277950737092+c.lower,100278331257524+c.upper)) = pointBounds20401 := by
 decide +kernel
def cuts20402 : List PrefixCut := [⟨32,156498768,156498861⟩,
⟨114,562819124,562819451⟩,
⟨128,633445684,633446051⟩]
theorem checked20402 : checkPrefixCuts (2^48) 2678063105 9 Manual.Count131072.C020402.packed 128 cuts20402 = true := by
 decide +kernel
def pointBounds20402 : List (Nat × Nat × Nat) := [(2678095872,100278747754640,100279128275532),(2678179840,100279154074996,100279534596122)]
theorem point_links_checked20402 : (cuts20402.take 2).map (fun c => (2678063105-1+2*2^9*c.k,100278591255872+c.lower,100278971776671+c.upper)) = pointBounds20402 := by
 decide +kernel
def cuts20403 : List PrefixCut := [⟨68,338518748,338518949⟩,
⟨128,635937088,635937459⟩]
theorem checked20403 : checkPrefixCuts (2^48) 2678194177 9 Manual.Count131072.C020403.packed 128 cuts20403 = true := by
 decide +kernel
def pointBounds20403 : List (Nat × Nat × Nat) := [(2678263808,100279563220304,100279943741671)]
theorem point_links_checked20403 : (cuts20403.take 1).map (fun c => (2678194177-1+2*2^9*c.k,100279224701556+c.lower,100279605222722+c.upper)) = pointBounds20403 := by
 decide +kernel
def cuts20404 : List PrefixCut := [⟨22,110242752,110242819⟩,
⟨104,514738411,514738709⟩,
⟨128,639058643,639059015⟩]
theorem checked20404 : checkPrefixCuts (2^48) 2678325249 9 Manual.Count131072.C020404.packed 128 cuts20404 = true := by
 decide +kernel
def pointBounds20404 : List (Nat × Nat × Nat) := [(2678347776,100279970881396,100280351403000),(2678431744,100280375377055,100280755898890)]
theorem point_links_checked20404 : (cuts20404.take 2).map (fun c => (2678325249-1+2*2^9*c.k,100279860638644+c.lower,100280241160181+c.upper)) = pointBounds20404 := by
 decide +kernel
def cuts20405 : List PrefixCut := [⟨58,286257822,286257988⟩,
⟨128,633983196,633983562⟩]
theorem checked20405 : checkPrefixCuts (2^48) 2678456321 9 Manual.Count131072.C020405.packed 128 cuts20405 = true := by
 decide +kernel
def pointBounds20405 : List (Nat × Nat × Nat) := [(2678515712,100280785955109,100281166477184)]
theorem point_links_checked20405 : (cuts20405.take 1).map (fun c => (2678456321-1+2*2^9*c.k,100280499697287+c.lower,100280880219196+c.upper)) = pointBounds20405 := by
 decide +kernel
def cuts20406 : List PrefixCut := [⟨12,57060119,57060154⟩,
⟨94,472341008,472341286⟩,
⟨128,638680874,638681252⟩]
theorem checked20406 : checkPrefixCuts (2^48) 2678587393 9 Manual.Count131072.C020406.packed 128 cuts20406 = true := by
 decide +kernel
def pointBounds20406 : List (Nat × Nat × Nat) := [(2678599680,100281190740602,100281571262912),(2678683648,100281606021491,100281986544044)]
theorem point_links_checked20406 : (cuts20406.take 2).map (fun c => (2678587393-1+2*2^9*c.k,100281133680483+c.lower,100281514202758+c.upper)) = pointBounds20406 := by
 decide +kernel
def cuts20407 : List PrefixCut := [⟨48,235688222,235688356⟩,
⟨128,636758178,636758540⟩]
theorem checked20407 : checkPrefixCuts (2^48) 2678718465 9 Manual.Count131072.C020407.packed 128 cuts20407 = true := by
 decide +kernel
def pointBounds20407 : List (Nat × Nat × Nat) := [(2678767616,100282008049579,100282388572366)]
theorem point_links_checked20407 : (cuts20407.take 1).map (fun c => (2678718465-1+2*2^9*c.k,100281772361357+c.lower,100282152884010+c.upper)) = pointBounds20407 := by
 decide +kernel
def cuts20408 : List PrefixCut := [⟨2,9666718,9666723⟩,
⟨84,420810801,420811043⟩,
⟨128,637042394,637042759⟩]
theorem checked20408 : checkPrefixCuts (2^48) 2678849537 9 Manual.Count131072.C020408.packed 128 cuts20408 = true := by
 decide +kernel
def pointBounds20408 : List (Nat × Nat × Nat) := [(2678851584,100282418786253,100282799309273),(2678935552,100282829930336,100283210453593)]
theorem point_links_checked20408 : (cuts20408.take 2).map (fun c => (2678849537-1+2*2^9*c.k,100282409119535+c.lower,100282789642550+c.upper)) = pointBounds20408 := by
 decide +kernel
def cuts20409 : List PrefixCut := [⟨38,184077627,184077733⟩,
⟨120,582903406,582903755⟩,
⟨128,625243767,625244140⟩]
theorem checked20409 : checkPrefixCuts (2^48) 2678980609 9 Manual.Count131072.C020409.packed 128 cuts20409 = true := by
 decide +kernel
def pointBounds20409 : List (Nat × Nat × Nat) := [(2679019520,100283230239556,100283610763042),(2679103488,100283629065335,100284009589064)]
theorem point_links_checked20409 : (cuts20409.take 2).map (fun c => (2678980609-1+2*2^9*c.k,100283046161929+c.lower,100283426685309+c.upper)) = pointBounds20409 := by
 decide +kernel
def cuts20410 : List PrefixCut := [⟨74,370551166,370551383⟩,
⟨128,639291397,639291772⟩]
theorem checked20410 : checkPrefixCuts (2^48) 2679111681 9 Manual.Count131072.C020410.packed 128 cuts20410 = true := by
 decide +kernel
def pointBounds20410 : List (Nat × Nat × Nat) := [(2679187456,100284041956862,100284422480832)]
theorem point_links_checked20410 : (cuts20410.take 1).map (fun c => (2679111681-1+2*2^9*c.k,100283671405696+c.lower,100284051929449+c.upper)) = pointBounds20410 := by
 decide +kernel
def cuts20411 : List PrefixCut := [⟨28,139725893,139725973⟩,
⟨110,546078081,546078393⟩,
⟨128,638734702,638735069⟩]
theorem checked20411 : checkPrefixCuts (2^48) 2679242753 9 Manual.Count131072.C020411.packed 128 cuts20411 = true := by
 decide +kernel
def pointBounds20411 : List (Nat × Nat × Nat) := [(2679271424,100284450422986,100284830947194),(2679355392,100284856775174,100285237299614)]
theorem point_links_checked20411 : (cuts20411.take 2).map (fun c => (2679242753-1+2*2^9*c.k,100284310697093+c.lower,100284691221221+c.upper)) = pointBounds20411 := by
 decide +kernel
def cuts20412 : List PrefixCut := [⟨64,316519310,316519494⟩,
⟨128,630404636,630405005⟩]
theorem checked20412 : checkPrefixCuts (2^48) 2679373825 9 Manual.Count131072.C020412.packed 128 cuts20412 = true := by
 decide +kernel
def pointBounds20412 : List (Nat × Nat × Nat) := [(2679439360,100285265951105,100285646475784)]
theorem point_links_checked20412 : (cuts20412.take 1).map (fun c => (2679373825-1+2*2^9*c.k,100284949431795+c.lower,100285329956290+c.upper)) = pointBounds20412 := by
 decide +kernel
def cuts20413 : List PrefixCut := [⟨18,88659666,88659718⟩,
⟨100,492137435,492137724⟩,
⟨128,631319120,631319488⟩]
theorem checked20413 : checkPrefixCuts (2^48) 2679504897 9 Manual.Count131072.C020413.packed 128 cuts20413 = true := by
 decide +kernel
def pointBounds20413 : List (Nat × Nat × Nat) := [(2679523328,100285668496097,100286049021013),(2679607296,100286071973866,100286452499019)]
theorem point_links_checked20413 : (cuts20413.take 2).map (fun c => (2679504897-1+2*2^9*c.k,100285579836431+c.lower,100285960361295+c.upper)) = pointBounds20413 := by
 decide +kernel
def cuts20414 : List PrefixCut := [⟨54,260291943,260292091⟩,
⟨128,626561401,626561764⟩]
theorem checked20414 : checkPrefixCuts (2^48) 2679635969 9 Manual.Count131072.C020414.packed 128 cuts20414 = true := by
 decide +kernel
def pointBounds20414 : List (Nat × Nat × Nat) := [(2679691264,100286471447494,100286851972874)]
theorem point_links_checked20414 : (cuts20414.take 1).map (fun c => (2679635969-1+2*2^9*c.k,100286211155551+c.lower,100286591680783+c.upper)) = pointBounds20414 := by
 decide +kernel
def cuts20415 : List PrefixCut := [⟨8,36657884,36657905⟩,
⟨90,449445802,449446062⟩,
⟨128,642285844,642286221⟩]
theorem checked20415 : checkPrefixCuts (2^48) 2679767041 9 Manual.Count131072.C020415.packed 128 cuts20415 = true := by
 decide +kernel
def pointBounds20415 : List (Nat × Nat × Nat) := [(2679775232,100286874374836,100287254900452),(2679859200,100287287162754,100287667688609)]
theorem point_links_checked20415 : (cuts20415.take 2).map (fun c => (2679767041-1+2*2^9*c.k,100286837716952+c.lower,100287218242547+c.upper)) = pointBounds20415 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S3.B000012
