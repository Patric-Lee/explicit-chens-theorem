import PlattAssemblyKernel
import PlattCertificates.Count131072.C011440
import PlattCertificates.Count131072.C011441
import PlattCertificates.Count131072.C011442
import PlattCertificates.Count131072.C011443
import PlattCertificates.Count131072.C011444
import PlattCertificates.Count131072.C011445
import PlattCertificates.Count131072.C011446
import PlattCertificates.Count131072.C011447
import PlattCertificates.Count131072.C011448
import PlattCertificates.Count131072.C011449
import PlattCertificates.Count131072.C011450
import PlattCertificates.Count131072.C011451
import PlattCertificates.Count131072.C011452
import PlattCertificates.Count131072.C011453
import PlattCertificates.Count131072.C011454
import PlattCertificates.Count131072.C011455
import PlattCertificates.Count131072.C011456
import PlattCertificates.Count131072.C011457
import PlattCertificates.Count131072.C011458
import PlattCertificates.Count131072.C011459
import PlattCertificates.Count131072.C011460
import PlattCertificates.Count131072.C011461
import PlattCertificates.Count131072.C011462
import PlattCertificates.Count131072.C011463
import PlattCertificates.Count131072.C011464
import PlattCertificates.Count131072.C011465
import PlattCertificates.Count131072.C011466
import PlattCertificates.Count131072.C011467
import PlattCertificates.Count131072.C011468
import PlattCertificates.Count131072.C011469
import PlattCertificates.Count131072.C011470
import PlattCertificates.Count131072.C011471
namespace ChenEffective.PlattWindow.Assembly.Prefix.S2.B000045
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts11440 : List PrefixCut := [⟨42,383059045,383059351⟩,
⟨88,796061486,796062117⟩,
⟨128,1154385856,1154386769⟩]
theorem checked11440 : checkPrefixCuts (2^48) 1503395841 9 Manual.Count131072.C011440.packed 128 cuts11440 = true := by
 decide +kernel
def pointBounds11440 : List (Nat × Nat × Nat) := [(1503438848,92691457112502,92691832555272),(1503485952,92691870114943,92692245558038)]
theorem point_links_checked11440 : (cuts11440.take 2).map (fun c => (1503395841-1+2*2^9*c.k,92691074053457+c.lower,92691449495921+c.upper)) = pointBounds11440 := by
 decide +kernel
def cuts11441 : List PrefixCut := [⟨6,51856993,51857034⟩,
⟨52,475129917,475130293⟩,
⟨98,892960719,892961425⟩,
⟨128,1161211614,1161212534⟩]
theorem checked11441 : checkPrefixCuts (2^48) 1503526913 9 Manual.Count131072.C011441.packed 128 cuts11441 = true := by
 decide +kernel
def pointBounds11441 : List (Nat × Nat × Nat) := [(1503533056,92692280296306,92692655739724),(1503580160,92692703569230,92693079012983),(1503627264,92693121400032,92693496844115)]
theorem point_links_checked11441 : (cuts11441.take 3).map (fun c => (1503526913-1+2*2^9*c.k,92692228439313+c.lower,92692603882690+c.upper)) = pointBounds11441 := by
 decide +kernel
def cuts11442 : List PrefixCut := [⟨16,147320395,147320512⟩,
⟨62,567558571,567559021⟩,
⟨108,987034647,987035427⟩,
⟨128,1164479724,1164480644⟩]
theorem checked11442 : checkPrefixCuts (2^48) 1503657985 9 Manual.Count131072.C011442.packed 128 cuts11442 = true := by
 decide +kernel
def pointBounds11442 : List (Nat × Nat × Nat) := [(1503674368,92693536971322,92693912415736),(1503721472,92693957209498,92694332654245),(1503768576,92694376685574,92694752130651)]
theorem point_links_checked11442 : (cuts11442.take 3).map (fun c => (1503657985-1+2*2^9*c.k,92693389650927+c.lower,92693765095224+c.upper)) = pointBounds11442 := by
 decide +kernel
def cuts11443 : List PrefixCut := [⟨26,237151301,237151486⟩,
⟨72,652296288,652296802⟩,
⟨118,1067053870,1067054712⟩,
⟨128,1155019731,1155020641⟩]
theorem checked11443 : checkPrefixCuts (2^48) 1503789057 9 Manual.Count131072.C011443.packed 128 cuts11443 = true := by
 decide +kernel
def pointBounds11443 : List (Nat × Nat × Nat) := [(1503815680,92694791281952,92695166727354),(1503862784,92695206426939,92695581872670),(1503909888,92695621184521,92695996630580)]
theorem point_links_checked11443 : (cuts11443.take 3).map (fun c => (1503789057-1+2*2^9*c.k,92694554130651+c.lower,92694929575868+c.upper)) = pointBounds11443 := by
 decide +kernel
def cuts11444 : List PrefixCut := [⟨36,322661224,322661481⟩,
⟨82,738328580,738329167⟩,
⟨128,1156603105,1156604022⟩]
theorem checked11444 : checkPrefixCuts (2^48) 1503920129 9 Manual.Count131072.C011444.packed 128 cuts11444 = true := by
 decide +kernel
def pointBounds11444 : List (Nat × Nat × Nat) := [(1503956992,92696031811606,92696407257990),(1504004096,92696447478962,92696822925676),(1504051200,92696865753487,92697241200531)]
theorem point_links_checked11444 : (cuts11444.take 3).map (fun c => (1503920129-1+2*2^9*c.k,92695709150382+c.lower,92696084596509+c.upper)) = pointBounds11444 := by
 decide +kernel
def cuts11445 : List PrefixCut := [⟨46,430238403,430238740⟩,
⟨92,854287843,854288517⟩,
⟨128,1183076031,1183076964⟩]
theorem checked11445 : checkPrefixCuts (2^48) 1504051201 9 Manual.Count131072.C011445.packed 128 cuts11445 = true := by
 decide +kernel
def pointBounds11445 : List (Nat × Nat × Nat) := [(1504098304,92697295991890,92697671439271),(1504145408,92697720041330,92698095489048)]
theorem point_links_checked11445 : (cuts11445.take 2).map (fun c => (1504051201-1+2*2^9*c.k,92696865753487+c.lower,92697241200531+c.upper)) = pointBounds11445 := by
 decide +kernel
def cuts11446 : List PrefixCut := [⟨10,94312284,94312356⟩,
⟨56,514031316,514031720⟩,
⟨102,934485659,934486393⟩,
⟨128,1166319354,1166320269⟩]
theorem checked11446 : checkPrefixCuts (2^48) 1504182273 9 Manual.Count131072.C011446.packed 128 cuts11446 = true := by
 decide +kernel
def pointBounds11446 : List (Nat × Nat × Nat) := [(1504192512,92698143141802,92698518589851),(1504239616,92698562860834,92698938309215),(1504286720,92698983315177,92699358763888)]
theorem point_links_checked11446 : (cuts11446.take 3).map (fun c => (1504182273-1+2*2^9*c.k,92698048829518+c.lower,92698424277495+c.upper)) = pointBounds11446 := by
 decide +kernel
def cuts11447 : List PrefixCut := [⟨20,188420337,188420488⟩,
⟨66,612029186,612029669⟩,
⟨112,1037495735,1037496562⟩,
⟨128,1184366562,1184367506⟩]
theorem checked11447 : checkPrefixCuts (2^48) 1504313345 9 Manual.Count131072.C011447.packed 128 cuts11447 = true := by
 decide +kernel
def pointBounds11447 : List (Nat × Nat × Nat) := [(1504333824,92699403569209,92699779018252),(1504380928,92699827178058,92700202627433),(1504428032,92700252644607,92700628094326)]
theorem point_links_checked11447 : (cuts11447.take 3).map (fun c => (1504313345-1+2*2^9*c.k,92699215148872+c.lower,92699590597764+c.upper)) = pointBounds11447 := by
 decide +kernel
def cuts11448 : List PrefixCut := [⟨30,274279277,274279492⟩,
⟨76,687371414,687371958⟩,
⟨122,1102134225,1102135094⟩,
⟨128,1156387318,1156388230⟩]
theorem checked11448 : checkPrefixCuts (2^48) 1504444417 9 Manual.Count131072.C011448.packed 128 cuts11448 = true := by
 decide +kernel
def pointBounds11448 : List (Nat × Nat × Nat) := [(1504475136,92700673794711,92701049244762),(1504522240,92701086886848,92701462337228),(1504569344,92701501649659,92701877100364)]
theorem point_links_checked11448 : (cuts11448.take 3).map (fun c => (1504444417-1+2*2^9*c.k,92700399515434+c.lower,92700774965270+c.upper)) = pointBounds11448 := by
 decide +kernel
def cuts11449 : List PrefixCut := [⟨40,360496825,360497105⟩,
⟨86,774298378,774298986⟩,
⟨128,1147494361,1147495265⟩]
theorem checked11449 : checkPrefixCuts (2^48) 1504575489 9 Manual.Count131072.C011449.packed 128 cuts11449 = true := by
 decide +kernel
def pointBounds11449 : List (Nat × Nat × Nat) := [(1504616448,92701916399577,92702291850605),(1504663552,92702330201130,92702705652486)]
theorem point_links_checked11449 : (cuts11449.take 2).map (fun c => (1504575489-1+2*2^9*c.k,92701555902752+c.lower,92701931353500+c.upper)) = pointBounds11449 := by
 decide +kernel
def cuts11450 : List PrefixCut := [⟨4,37038416,37038446⟩,
⟨50,460167062,460167428⟩,
⟨96,878419104,878419800⟩,
⟨128,1167970468,1167971392⟩]
theorem checked11450 : checkPrefixCuts (2^48) 1504706561 9 Manual.Count131072.C011450.packed 128 cuts11450 = true := by
 decide +kernel
def pointBounds11450 : List (Nat × Nat × Nat) := [(1504710656,92702740435529,92703115887211),(1504757760,92703163564175,92703539016193),(1504804864,92703581816217,92703957268565)]
theorem point_links_checked11450 : (cuts11450.take 3).map (fun c => (1504706561-1+2*2^9*c.k,92702703397113+c.lower,92703078848765+c.upper)) = pointBounds11450 := by
 decide +kernel
def cuts11451 : List PrefixCut := [⟨14,125320659,125320759⟩,
⟨60,543172403,543172836⟩,
⟨106,954651748,954652510⟩,
⟨128,1156272041,1156272965⟩]
theorem checked11451 : checkPrefixCuts (2^48) 1504837633 9 Manual.Count131072.C011451.packed 128 cuts11451 = true := by
 decide +kernel
def pointBounds11451 : List (Nat × Nat × Nat) := [(1504851968,92703996688240,92704372140916),(1504899072,92704414539984,92704789992993),(1504946176,92704826019329,92705201472667)]
theorem point_links_checked11451 : (cuts11451.take 3).map (fun c => (1504837633-1+2*2^9*c.k,92703871367581+c.lower,92704246820157+c.upper)) = pointBounds11451 := by
 decide +kernel
def cuts11452 : List PrefixCut := [⟨24,218636756,218636925⟩,
⟨70,632147657,632148156⟩,
⟨116,1055931739,1055932572⟩,
⟨128,1165335427,1165336346⟩]
theorem checked11452 : checkPrefixCuts (2^48) 1504968705 9 Manual.Count131072.C011452.packed 128 cuts11452 = true := by
 decide +kernel
def pointBounds11452 : List (Nat × Nat × Nat) := [(1504993280,92705246276378,92705621730047),(1505040384,92705659787279,92706035241278),(1505087488,92706083571361,92706459025694)]
theorem point_links_checked11452 : (cuts11452.take 3).map (fun c => (1504968705-1+2*2^9*c.k,92705027639622+c.lower,92705403093122+c.upper)) = pointBounds11452 := by
 decide +kernel
def cuts11453 : List PrefixCut := [⟨34,304268356,304268595⟩,
⟨80,724659718,724660290⟩,
⟨126,1145785955,1145786860⟩,
⟨128,1165420740,1165421660⟩]
theorem checked11453 : checkPrefixCuts (2^48) 1505099777 9 Manual.Count131072.C011453.packed 128 cuts11453 = true := by
 decide +kernel
def pointBounds11453 : List (Nat × Nat × Nat) := [(1505134592,92706497243405,92706872698063),(1505181696,92706917634767,92707293089758),(1505228800,92707338761004,92707714216328)]
theorem point_links_checked11453 : (cuts11453.take 3).map (fun c => (1505099777-1+2*2^9*c.k,92706192975049+c.lower,92706568429468+c.upper)) = pointBounds11453 := by
 decide +kernel
def cuts11454 : List PrefixCut := [⟨44,405966167,405966486⟩,
⟨90,822017408,822018053⟩,
⟨128,1166628767,1166629680⟩]
theorem checked11454 : checkPrefixCuts (2^48) 1505230849 9 Manual.Count131072.C011454.packed 128 cuts11454 = true := by
 decide +kernel
def pointBounds11454 : List (Nat × Nat × Nat) := [(1505275904,92707764361956,92708139817614),(1505323008,92708180413197,92708555869181)]
theorem point_links_checked11454 : (cuts11454.take 2).map (fun c => (1505230849-1+2*2^9*c.k,92707358395789+c.lower,92707733851128+c.upper)) = pointBounds11454 := by
 decide +kernel
def cuts11455 : List PrefixCut := [⟨8,72174678,72174735⟩,
⟨54,494931049,494931436⟩,
⟨100,910943182,910943897⟩,
⟨128,1168022828,1168023746⟩]
theorem checked11455 : checkPrefixCuts (2^48) 1505361921 9 Manual.Count131072.C011455.packed 128 cuts11455 = true := by
 decide +kernel
def pointBounds11455 : List (Nat × Nat × Nat) := [(1505370112,92708597199234,92708972655543),(1505417216,92709019955605,92709395412244),(1505464320,92709435967738,92709811424705)]
theorem point_links_checked11455 : (cuts11455.take 3).map (fun c => (1505361921-1+2*2^9*c.k,92708525024556+c.lower,92708900480808+c.upper)) = pointBounds11455 := by
 decide +kernel
def cuts11456 : List PrefixCut := [⟨18,166024132,166024264⟩,
⟨64,585375476,585375938⟩,
⟨110,998544258,998545041⟩,
⟨128,1165303733,1165304650⟩]
theorem checked11456 : checkPrefixCuts (2^48) 1505492993 9 Manual.Count131072.C011456.packed 128 cuts11456 = true := by
 decide +kernel
def pointBounds11456 : List (Nat × Nat × Nat) := [(1505511424,92709859071516,92710234528818),(1505558528,92710278422860,92710653880492),(1505605632,92710691591642,92711067049595)]
theorem point_links_checked11456 : (cuts11456.take 3).map (fun c => (1505492993-1+2*2^9*c.k,92709693047384+c.lower,92710068504554+c.upper)) = pointBounds11456 := by
 decide +kernel
def cuts11457 : List PrefixCut := [⟨28,250135352,250135548⟩,
⟨74,674494800,674495332⟩,
⟨120,1091176552,1091177409⟩,
⟨128,1162958905,1162959818⟩]
theorem checked11457 : checkPrefixCuts (2^48) 1505624065 9 Manual.Count131072.C011457.packed 128 cuts11457 = true := by
 decide +kernel
def pointBounds11457 : List (Nat × Nat × Nat) := [(1505652736,92711108486469,92711483944752),(1505699840,92711532845917,92711908304536),(1505746944,92711949527669,92712324986613)]
theorem point_links_checked11457 : (cuts11457.take 3).map (fun c => (1505624065-1+2*2^9*c.k,92710858351117+c.lower,92711233809204+c.upper)) = pointBounds11457 := by
 decide +kernel
def cuts11458 : List PrefixCut := [⟨38,340400014,340400284⟩,
⟨84,754438723,754439319⟩,
⟨128,1166408747,1166409667⟩]
theorem checked11458 : checkPrefixCuts (2^48) 1505755137 9 Manual.Count131072.C011458.packed 128 cuts11458 = true := by
 decide +kernel
def pointBounds11458 : List (Nat × Nat × Nat) := [(1505794048,92712361710036,92712737169306),(1505841152,92712775748745,92713151208341)]
theorem point_links_checked11458 : (cuts11458.take 2).map (fun c => (1505755137-1+2*2^9*c.k,92712021310022+c.lower,92712396769022+c.upper)) = pointBounds11458 := by
 decide +kernel
def cuts11459 : List PrefixCut := [⟨2,16448634,16448647⟩,
⟨48,433078316,433078657⟩,
⟨94,845956869,845957540⟩,
⟨128,1158270640,1158271556⟩]
theorem checked11459 : checkPrefixCuts (2^48) 1505886209 9 Manual.Count131072.C011459.packed 128 cuts11459 = true := by
 decide +kernel
def pointBounds11459 : List (Nat × Nat × Nat) := [(1505888256,92713204167403,92713579627336),(1505935360,92713620797085,92713996257346),(1505982464,92714033675638,92714409136229)]
theorem point_links_checked11459 : (cuts11459.take 3).map (fun c => (1505886209-1+2*2^9*c.k,92713187718769+c.lower,92713563178689+c.upper)) = pointBounds11459 := by
 decide +kernel
def cuts11460 : List PrefixCut := [⟨12,106532657,106532741⟩,
⟨58,526300531,526300946⟩,
⟨104,942878131,942878881⟩,
⟨128,1167140651,1167141577⟩]
theorem checked11460 : checkPrefixCuts (2^48) 1506017281 9 Manual.Count131072.C011460.packed 128 cuts11460 = true := by
 decide +kernel
def pointBounds11460 : List (Nat × Nat × Nat) := [(1506029568,92714452522066,92714827982986),(1506076672,92714872289940,92715247751191),(1506123776,92715288867540,92715664329126)]
theorem point_links_checked11460 : (cuts11460.take 3).map (fun c => (1506017281-1+2*2^9*c.k,92714345989409+c.lower,92714721450245+c.upper)) = pointBounds11460 := by
 decide +kernel
def cuts11461 : List PrefixCut := [⟨22,199590485,199590639⟩,
⟨68,609227511,609227992⟩,
⟨114,1033427734,1033428550⟩,
⟨128,1149473079,1149473987⟩]
theorem checked11461 : checkPrefixCuts (2^48) 1506148353 9 Manual.Count131072.C011461.packed 128 cuts11461 = true := by
 decide +kernel
def pointBounds11461 : List (Nat × Nat × Nat) := [(1506170880,92715712720545,92716088182461),(1506217984,92716122357571,92716497819814),(1506265088,92716546557794,92716922020372)]
theorem point_links_checked11461 : (cuts11461.take 3).map (fun c => (1506148353-1+2*2^9*c.k,92715513130060+c.lower,92715888591822+c.upper)) = pointBounds11461 := by
 decide +kernel
def cuts11462 : List PrefixCut := [⟨32,295808188,295808426⟩,
⟨78,705593571,705594131⟩,
⟨124,1122092917,1122093806⟩,
⟨128,1160023794,1160024712⟩]
theorem checked11462 : checkPrefixCuts (2^48) 1506279425 9 Manual.Count131072.C011462.packed 128 cuts11462 = true := by
 decide +kernel
def pointBounds11462 : List (Nat × Nat × Nat) := [(1506312192,92716958411327,92717333874235),(1506359296,92717368196710,92717743659940),(1506406400,92717784696056,92718160159615)]
theorem point_links_checked11462 : (cuts11462.take 3).map (fun c => (1506279425-1+2*2^9*c.k,92716662603139+c.lower,92717038065809+c.upper)) = pointBounds11462 := by
 decide +kernel
def cuts11463 : List PrefixCut := [⟨42,384534603,384534906⟩,
⟨88,793907734,793908358⟩,
⟨128,1157867431,1157868341⟩]
theorem checked11463 : checkPrefixCuts (2^48) 1506410497 9 Manual.Count131072.C011463.packed 128 cuts11463 = true := by
 decide +kernel
def pointBounds11463 : List (Nat × Nat × Nat) := [(1506453504,92718207161536,92718582625427),(1506500608,92718616534667,92718991998879)]
theorem point_links_checked11463 : (cuts11463.take 2).map (fun c => (1506410497-1+2*2^9*c.k,92717822626933+c.lower,92718198090521+c.upper)) = pointBounds11463 := by
 decide +kernel
def cuts11464 : List PrefixCut := [⟨6,54368908,54368952⟩,
⟨52,462221918,462222285⟩,
⟨98,884074069,884074770⟩,
⟨128,1149359594,1149360504⟩]
theorem checked11464 : checkPrefixCuts (2^48) 1506541569 9 Manual.Count131072.C011464.packed 128 cuts11464 = true := by
 decide +kernel
def pointBounds11464 : List (Nat × Nat × Nat) := [(1506547712,92719034863272,92719410327814),(1506594816,92719442716282,92719818181147),(1506641920,92719864568433,92720240033632)]
theorem point_links_checked11464 : (cuts11464.take 3).map (fun c => (1506541569-1+2*2^9*c.k,92718980494364+c.lower,92719355958862+c.upper)) = pointBounds11464 := by
 decide +kernel
def cuts11465 : List PrefixCut := [⟨16,149080627,149080746⟩,
⟨62,568291030,568291481⟩,
⟨108,982631263,982632043⟩,
⟨128,1158787312,1158788229⟩]
theorem checked11465 : checkPrefixCuts (2^48) 1506672641 9 Manual.Count131072.C011465.packed 128 cuts11465 = true := by
 decide +kernel
def pointBounds11465 : List (Nat × Nat × Nat) := [(1506689024,92720278934585,92720654400112),(1506736128,92720698144988,92721073610847),(1506783232,92721112485221,92721487951409)]
theorem point_links_checked11465 : (cuts11465.take 3).map (fun c => (1506672641-1+2*2^9*c.k,92720129853958+c.lower,92720505319366+c.upper)) = pointBounds11465 := by
 decide +kernel
def cuts11466 : List PrefixCut := [⟨26,238171230,238171414⟩,
⟨72,658276281,658276791⟩,
⟨118,1072390965,1072391802⟩,
⟨128,1159246928,1159247835⟩]
theorem checked11466 : checkPrefixCuts (2^48) 1506803713 9 Manual.Count131072.C011466.packed 128 cuts11466 = true := by
 decide +kernel
def pointBounds11466 : List (Nat × Nat × Nat) := [(1506830336,92721526812500,92721902279009),(1506877440,92721946917551,92722322384386),(1506924544,92722361032235,92722736499397)]
theorem point_links_checked11466 : (cuts11466.take 3).map (fun c => (1506803713-1+2*2^9*c.k,92721288641270+c.lower,92721664107595+c.upper)) = pointBounds11466 := by
 decide +kernel
def cuts11467 : List PrefixCut := [⟨36,319214045,319214302⟩,
⟨82,732555777,732556355⟩,
⟨128,1149433254,1149434159⟩]
theorem checked11467 : checkPrefixCuts (2^48) 1506934785 9 Manual.Count131072.C011467.packed 128 cuts11467 = true := by
 decide +kernel
def pointBounds11467 : List (Nat × Nat × Nat) := [(1506971648,92722767102243,92723142569732),(1507018752,92723180443975,92723555911785),(1507065856,92723597321452,92723972789589)]
theorem point_links_checked11467 : (cuts11467.take 3).map (fun c => (1506934785-1+2*2^9*c.k,92722447888198+c.lower,92722823355430+c.upper)) = pointBounds11467 := by
 decide +kernel
def cuts11468 : List PrefixCut := [⟨46,418358534,418358864⟩,
⟨92,825498321,825498974⟩,
⟨128,1155496456,1155497369⟩]
theorem checked11468 : checkPrefixCuts (2^48) 1507065857 9 Manual.Count131072.C011468.packed 128 cuts11468 = true := by
 decide +kernel
def pointBounds11468 : List (Nat × Nat × Nat) := [(1507112960,92724015679986,92724391148453),(1507160064,92724422819773,92724798288563)]
theorem point_links_checked11468 : (cuts11468.take 2).map (fun c => (1507065857-1+2*2^9*c.k,92723597321452+c.lower,92723972789589+c.upper)) = pointBounds11468 := by
 decide +kernel
def cuts11469 : List PrefixCut := [⟨10,91882601,91882673⟩,
⟨56,508334287,508334687⟩,
⟨102,925519984,925520712⟩,
⟨128,1152968437,1152969346⟩]
theorem checked11469 : checkPrefixCuts (2^48) 1507196929 9 Manual.Count131072.C011469.packed 128 cuts11469 = true := by
 decide +kernel
def pointBounds11469 : List (Nat × Nat × Nat) := [(1507207168,92724844700509,92725220169631),(1507254272,92725261152195,92725636621645),(1507301376,92725678337892,92726053807670)]
theorem point_links_checked11469 : (cuts11469.take 3).map (fun c => (1507196929-1+2*2^9*c.k,92724752817908+c.lower,92725128286958+c.upper)) = pointBounds11469 := by
 decide +kernel
def cuts11470 : List PrefixCut := [⟨20,184868988,184869131⟩,
⟨66,605576686,605577158⟩,
⟨113,1038408261,1038409075⟩,
⟨128,1171541295,1171542215⟩]
theorem checked11470 : checkPrefixCuts (2^48) 1507328001 9 Manual.Count131072.C011470.packed 128 cuts11470 = true := by
 decide +kernel
def pointBounds11470 : List (Nat × Nat × Nat) := [(1507348480,92726090655333,92726466125435),(1507395584,92726511363031,92726886833462),(1507443712,92726944194606,92727319665379)]
theorem point_links_checked11470 : (cuts11470.take 3).map (fun c => (1507328001-1+2*2^9*c.k,92725905786345+c.lower,92726281256304+c.upper)) = pointBounds11470 := by
 decide +kernel
def cuts11471 : List PrefixCut := [⟨32,280825908,280826130⟩,
⟨79,706908046,706908606⟩,
⟨126,1135590488,1135591386⟩,
⟨128,1155007839,1155008752⟩]
theorem checked11471 : checkPrefixCuts (2^48) 1507459073 9 Manual.Count131072.C011471.packed 128 cuts11471 = true := by
 decide +kernel
def pointBounds11471 : List (Nat × Nat × Nat) := [(1507491840,92727358153548,92727733624649),(1507539968,92727784235686,92728159707125),(1507588096,92728212918128,92728588389905)]
theorem point_links_checked11471 : (cuts11471.take 3).map (fun c => (1507459073-1+2*2^9*c.k,92727077327640+c.lower,92727452798519+c.upper)) = pointBounds11471 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S2.B000045
