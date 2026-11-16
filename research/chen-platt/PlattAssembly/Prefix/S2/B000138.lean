import PlattAssemblyKernel
import PlattCertificates.Count131072.C014416
import PlattCertificates.Count131072.C014417
import PlattCertificates.Count131072.C014418
import PlattCertificates.Count131072.C014419
import PlattCertificates.Count131072.C014420
import PlattCertificates.Count131072.C014421
import PlattCertificates.Count131072.C014422
import PlattCertificates.Count131072.C014423
import PlattCertificates.Count131072.C014424
import PlattCertificates.Count131072.C014425
import PlattCertificates.Count131072.C014426
import PlattCertificates.Count131072.C014427
import PlattCertificates.Count131072.C014428
import PlattCertificates.Count131072.C014429
import PlattCertificates.Count131072.C014430
import PlattCertificates.Count131072.C014431
import PlattCertificates.Count131072.C014432
import PlattCertificates.Count131072.C014433
import PlattCertificates.Count131072.C014434
import PlattCertificates.Count131072.C014435
import PlattCertificates.Count131072.C014436
import PlattCertificates.Count131072.C014437
import PlattCertificates.Count131072.C014438
import PlattCertificates.Count131072.C014439
import PlattCertificates.Count131072.C014440
import PlattCertificates.Count131072.C014441
import PlattCertificates.Count131072.C014442
import PlattCertificates.Count131072.C014443
import PlattCertificates.Count131072.C014444
import PlattCertificates.Count131072.C014445
import PlattCertificates.Count131072.C014446
import PlattCertificates.Count131072.C014447
namespace ChenEffective.PlattWindow.Assembly.Prefix.S2.B000138
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts14416 : List PrefixCut := [⟨12,86368794,86368852⟩,
⟨70,498433751,498434088⟩,
⟨128,914499359,914499980⟩]
theorem checked14416 : checkPrefixCuts (2^48) 1893466113 9 Manual.Count131072.C014416.packed 128 cuts14416 = true := by
 decide +kernel
def pointBounds14416 : List (Nat × Nat × Nat) := [(1893478400,95747169281099,95747546963897),(1893537792,95747581346056,95747959029133),(1893597184,95747997411664,95748375095025)]
theorem point_links_checked14416 : (cuts14416.take 3).map (fun c => (1893466113-1+2*2^9*c.k,95747082912305+c.lower,95747460595045+c.upper)) = pointBounds14416 := by
 decide +kernel
def cuts14417 : List PrefixCut := [⟨58,406390697,406390979⟩,
⟨116,820795150,820795717⟩,
⟨128,902396199,902396823⟩]
theorem checked14417 : checkPrefixCuts (2^48) 1893597185 9 Manual.Count131072.C014417.packed 128 cuts14417 = true := by
 decide +kernel
def pointBounds14417 : List (Nat × Nat × Nat) := [(1893656576,95748403802361,95748781486004),(1893715968,95748818206814,95749195890742)]
theorem point_links_checked14417 : (cuts14417.take 2).map (fun c => (1893597185-1+2*2^9*c.k,95747997411664+c.lower,95748375095025+c.upper)) = pointBounds14417 := by
 decide +kernel
def cuts14418 : List PrefixCut := [⟨46,321791472,321791689⟩,
⟨104,744195886,744196390⟩,
⟨128,916453395,916454015⟩]
theorem checked14418 : checkPrefixCuts (2^48) 1893728257 9 Manual.Count131072.C014418.packed 128 cuts14418 = true := by
 decide +kernel
def pointBounds14418 : List (Nat × Nat × Nat) := [(1893775360,95749221599335,95749599283537),(1893834752,95749644003749,95750021688238)]
theorem point_links_checked14418 : (cuts14418.take 2).map (fun c => (1893728257-1+2*2^9*c.k,95748899807863+c.lower,95749277491848+c.upper)) = pointBounds14418 := by
 decide +kernel
def cuts14419 : List PrefixCut := [⟨34,243891434,243891598⟩,
⟨92,650367015,650367459⟩,
⟨128,907621622,907622242⟩]
theorem checked14419 : checkPrefixCuts (2^48) 1893859329 9 Manual.Count131072.C014419.packed 128 cuts14419 = true := by
 decide +kernel
def pointBounds14419 : List (Nat × Nat × Nat) := [(1893894144,95750060152692,95750437837461),(1893953536,95750466628273,95750844313322)]
theorem point_links_checked14419 : (cuts14419.take 2).map (fun c => (1893859329-1+2*2^9*c.k,95749816261258+c.lower,95750193945863+c.upper)) = pointBounds14419 := by
 decide +kernel
def cuts14420 : List PrefixCut := [⟨22,155895941,155896045⟩,
⟨80,581516733,581517126⟩,
⟨128,917812959,917813582⟩]
theorem checked14420 : checkPrefixCuts (2^48) 1893990401 9 Manual.Count131072.C014420.packed 128 cuts14420 = true := by
 decide +kernel
def pointBounds14420 : List (Nat × Nat × Nat) := [(1894012928,95750879778821,95751257464150),(1894072320,95751305399613,95751683085231)]
theorem point_links_checked14420 : (cuts14420.take 2).map (fun c => (1893990401-1+2*2^9*c.k,95750723882880+c.lower,95751101568105+c.upper)) = pointBounds14420 := by
 decide +kernel
def cuts14421 : List PrefixCut := [⟨10,69546699,69546748⟩,
⟨68,487710833,487711165⟩,
⟨126,905267429,905268052⟩,
⟨128,919383882,919384515⟩]
theorem checked14421 : checkPrefixCuts (2^48) 1894121473 9 Manual.Count131072.C014421.packed 128 cuts14421 = true := by
 decide +kernel
def pointBounds14421 : List (Nat × Nat × Nat) := [(1894131712,95751711242538,95752088928435),(1894191104,95752129406672,95752507092852),(1894250496,95752546963268,95752924649739)]
theorem point_links_checked14421 : (cuts14421.take 3).map (fun c => (1894121473-1+2*2^9*c.k,95751641695839+c.lower,95752019381687+c.upper)) = pointBounds14421 := by
 decide +kernel
def cuts14422 : List PrefixCut := [⟨56,398374982,398375253⟩,
⟨114,812190684,812191236⟩,
⟨128,907284729,907285347⟩]
theorem checked14422 : checkPrefixCuts (2^48) 1894252545 9 Manual.Count131072.C014422.packed 128 cuts14422 = true := by
 decide +kernel
def pointBounds14422 : List (Nat × Nat × Nat) := [(1894309888,95752959454703,95753337141455),(1894369280,95753373270405,95753750957438)]
theorem point_links_checked14422 : (cuts14422.take 2).map (fun c => (1894252545-1+2*2^9*c.k,95752561079721+c.lower,95752938766202+c.upper)) = pointBounds14422 := by
 decide +kernel
def cuts14423 : List PrefixCut := [⟨44,309645139,309645347⟩,
⟨102,721503370,721503856⟩,
⟨128,903507325,903507932⟩]
theorem checked14423 : checkPrefixCuts (2^48) 1894383617 9 Manual.Count131072.C014423.packed 128 cuts14423 = true := by
 decide +kernel
def pointBounds14423 : List (Nat × Nat × Nat) := [(1894428672,95753778009589,95754155696896),(1894488064,95754189867820,95754567555405)]
theorem point_links_checked14423 : (cuts14423.take 2).map (fun c => (1894383617-1+2*2^9*c.k,95753468364450+c.lower,95753846051549+c.upper)) = pointBounds14423 := by
 decide +kernel
def cuts14424 : List PrefixCut := [⟨32,226127113,226127269⟩,
⟨90,628748313,628748743⟩,
⟨128,895125091,895125703⟩]
theorem checked14424 : checkPrefixCuts (2^48) 1894514689 9 Manual.Count131072.C014424.packed 128 cuts14424 = true := by
 decide +kernel
def pointBounds14424 : List (Nat × Nat × Nat) := [(1894547456,95754597998888,95754975686750),(1894606848,95755000620088,95755378308224)]
theorem point_links_checked14424 : (cuts14424.take 2).map (fun c => (1894514689-1+2*2^9*c.k,95754371871775+c.lower,95754749559481+c.upper)) = pointBounds14424 := by
 decide +kernel
def cuts14425 : List PrefixCut := [⟨20,140837267,140837362⟩,
⟨78,544324595,544324963⟩,
⟨128,905461991,905462605⟩]
theorem checked14425 : checkPrefixCuts (2^48) 1894645761 9 Manual.Count131072.C014425.packed 128 cuts14425 = true := by
 decide +kernel
def pointBounds14425 : List (Nat × Nat × Nat) := [(1894666240,95755407834133,95755785522546),(1894725632,95755811321461,95756189010147)]
theorem point_links_checked14425 : (cuts14425.take 2).map (fun c => (1894645761-1+2*2^9*c.k,95755266996866+c.lower,95755644685184+c.upper)) = pointBounds14425 := by
 decide +kernel
def cuts14426 : List PrefixCut := [⟨8,60460962,60461003⟩,
⟨66,475806920,475807242⟩,
⟨124,890991414,890992015⟩,
⟨128,917729143,917729762⟩]
theorem checked14426 : checkPrefixCuts (2^48) 1894776833 9 Manual.Count131072.C014426.packed 128 cuts14426 = true := by
 decide +kernel
def pointBounds14426 : List (Nat × Nat × Nat) := [(1894785024,95756232919819,95756610608792),(1894844416,95756648265777,95757025955031),(1894903808,95757063450271,95757441139804)]
theorem point_links_checked14426 : (cuts14426.take 3).map (fun c => (1894776833-1+2*2^9*c.k,95756172458857+c.lower,95756550147789+c.upper)) = pointBounds14426 := by
 decide +kernel
def cuts14427 : List PrefixCut := [⟨54,387096744,387097009⟩,
⟨112,809236482,809237037⟩,
⟨128,919299543,919300176⟩]
theorem checked14427 : checkPrefixCuts (2^48) 1894907905 9 Manual.Count131072.C014427.packed 128 cuts14427 = true := by
 decide +kernel
def pointBounds14427 : List (Nat × Nat × Nat) := [(1894963200,95757477284744,95757854974560),(1895022592,95757899424482,95758277114588)]
theorem point_links_checked14427 : (cuts14427.take 2).map (fun c => (1894907905-1+2*2^9*c.k,95757090188000+c.lower,95757467877551+c.upper)) = pointBounds14427 := by
 decide +kernel
def cuts14428 : List PrefixCut := [⟨42,297804318,297804517⟩,
⟨100,706550075,706550554⟩,
⟨128,910027083,910027701⟩]
theorem checked14428 : checkPrefixCuts (2^48) 1895038977 9 Manual.Count131072.C014428.packed 128 cuts14428 = true := by
 decide +kernel
def pointBounds14428 : List (Nat × Nat × Nat) := [(1895081984,95758307291861,95758684982244),(1895141376,95758716037618,95759093728281)]
theorem point_links_checked14428 : (cuts14428.take 2).map (fun c => (1895038977-1+2*2^9*c.k,95758009487543+c.lower,95758387177727+c.upper)) = pointBounds14428 := by
 decide +kernel
def cuts14429 : List PrefixCut := [⟨30,211790970,211791112⟩,
⟨88,631946961,631947388⟩,
⟨128,914419752,914420373⟩]
theorem checked14429 : checkPrefixCuts (2^48) 1895170049 9 Manual.Count131072.C014429.packed 128 cuts14429 = true := by
 decide +kernel
def pointBounds14429 : List (Nat × Nat × Nat) := [(1895200768,95759131305596,95759508996540),(1895260160,95759551461587,95759929152816)]
theorem point_links_checked14429 : (cuts14429.take 2).map (fun c => (1895170049-1+2*2^9*c.k,95758919514626+c.lower,95759297205428+c.upper)) = pointBounds14429 := by
 decide +kernel
def cuts14430 : List PrefixCut := [⟨18,124452418,124452505⟩,
⟨76,544136441,544136813⟩,
⟨128,907970807,907971426⟩]
theorem checked14430 : checkPrefixCuts (2^48) 1895301121 9 Manual.Count131072.C014430.packed 128 cuts14430 = true := by
 decide +kernel
def pointBounds14430 : List (Nat × Nat × Nat) := [(1895319552,95759958386796,95760336078306),(1895378944,95760378070819,95760755762614)]
theorem point_links_checked14430 : (cuts14430.take 2).map (fun c => (1895301121-1+2*2^9*c.k,95759833934378+c.lower,95760211625801+c.upper)) = pointBounds14430 := by
 decide +kernel
def cuts14431 : List PrefixCut := [⟨6,45292940,45292970⟩,
⟨64,448764470,448764774⟩,
⟨122,856826538,856827122⟩,
⟨128,900037611,900038226⟩]
theorem checked14431 : checkPrefixCuts (2^48) 1895432193 9 Manual.Count131072.C014431.packed 128 cuts14431 = true := by
 decide +kernel
def pointBounds14431 : List (Nat × Nat × Nat) := [(1895438336,95760787198125,95761164890197),(1895497728,95761190669655,95761568362001),(1895557120,95761598731723,95761976424349)]
theorem point_links_checked14431 : (cuts14431.take 3).map (fun c => (1895432193-1+2*2^9*c.k,95760741905185+c.lower,95761119597227+c.upper)) = pointBounds14431 := by
 decide +kernel
def cuts14432 : List PrefixCut := [⟨52,370035370,370035626⟩,
⟨110,780893175,780893709⟩,
⟨128,907399730,907400352⟩]
theorem checked14432 : checkPrefixCuts (2^48) 1895563265 9 Manual.Count131072.C014432.packed 128 cuts14432 = true := by
 decide +kernel
def pointBounds14432 : List (Nat × Nat × Nat) := [(1895616512,95762011978166,95762389671079),(1895675904,95762422835971,95762800529162)]
theorem point_links_checked14432 : (cuts14432.take 2).map (fun c => (1895563265-1+2*2^9*c.k,95761641942796+c.lower,95762019635453+c.upper)) = pointBounds14432 := by
 decide +kernel
def cuts14433 : List PrefixCut := [⟨40,280180891,280181084⟩,
⟨98,692943182,692943654⟩,
⟨128,911791050,911791670⟩]
theorem checked14433 : checkPrefixCuts (2^48) 1895694337 9 Manual.Count131072.C014433.packed 128 cuts14433 = true := by
 decide +kernel
def pointBounds14433 : List (Nat × Nat × Nat) := [(1895735296,95762829523417,95763207216889),(1895794688,95763242285708,95763619979459)]
theorem point_links_checked14433 : (cuts14433.take 2).map (fun c => (1895694337-1+2*2^9*c.k,95762549342526+c.lower,95762927035805+c.upper)) = pointBounds14433 := by
 decide +kernel
def cuts14434 : List PrefixCut := [⟨28,198207144,198207280⟩,
⟨86,614655261,614655674⟩,
⟨128,917666855,917667472⟩]
theorem checked14434 : checkPrefixCuts (2^48) 1895825409 9 Manual.Count131072.C014434.packed 128 cuts14434 = true := by
 decide +kernel
def pointBounds14434 : List (Nat × Nat × Nat) := [(1895854080,95763659340720,95764037034755),(1895913472,95764075788837,95764453483149)]
theorem point_links_checked14434 : (cuts14434.take 2).map (fun c => (1895825409-1+2*2^9*c.k,95763461133576+c.lower,95763838827475+c.upper)) = pointBounds14434 := by
 decide +kernel
def cuts14435 : List PrefixCut := [⟨16,113571885,113571963⟩,
⟨74,528806234,528806590⟩,
⟨128,908844660,908845269⟩]
theorem checked14435 : checkPrefixCuts (2^48) 1895956481 9 Manual.Count131072.C014435.packed 128 cuts14435 = true := by
 decide +kernel
def pointBounds14435 : List (Nat × Nat × Nat) := [(1895972864,95764492372316,95764870066910),(1896032256,95764907606665,95765285301537)]
theorem point_links_checked14435 : (cuts14435.take 2).map (fun c => (1895956481-1+2*2^9*c.k,95764378800431+c.lower,95764756494947+c.upper)) = pointBounds14435 := by
 decide +kernel
def cuts14436 : List PrefixCut := [⟨4,27908639,27908658⟩,
⟨62,443562256,443562558⟩,
⟨120,852968216,852968800⟩,
⟨128,909820893,909821517⟩]
theorem checked14436 : checkPrefixCuts (2^48) 1896087553 9 Manual.Count131072.C014436.packed 128 cuts14436 = true := by
 decide +kernel
def pointBounds14436 : List (Nat × Nat × Nat) := [(1896091648,95765315553730,95765693248874),(1896151040,95765731207347,95766108902774),(1896210432,95766140613307,95766518309016)]
theorem point_links_checked14436 : (cuts14436.take 3).map (fun c => (1896087553-1+2*2^9*c.k,95765287645091+c.lower,95765665340216+c.upper)) = pointBounds14436 := by
 decide +kernel
def cuts14437 : List PrefixCut := [⟨50,357884287,357884525⟩,
⟨108,767116237,767116757⟩,
⟨128,908422204,908422821⟩]
theorem checked14437 : checkPrefixCuts (2^48) 1896218625 9 Manual.Count131072.C014437.packed 128 cuts14437 = true := by
 decide +kernel
def pointBounds14437 : List (Nat × Nat × Nat) := [(1896269824,95766555350271,95766933046258),(1896329216,95766964582221,95767342278490)]
theorem point_links_checked14437 : (cuts14437.take 2).map (fun c => (1896218625-1+2*2^9*c.k,95766197465984+c.lower,95766575161733+c.upper)) = pointBounds14437 := by
 decide +kernel
def cuts14438 : List PrefixCut := [⟨38,270287946,270288133⟩,
⟨96,684837523,684837986⟩,
⟨128,912811966,912812582⟩]
theorem checked14438 : checkPrefixCuts (2^48) 1896349697 9 Manual.Count131072.C014438.packed 128 cuts14438 = true := by
 decide +kernel
def pointBounds14438 : List (Nat × Nat × Nat) := [(1896388608,95767376176134,95767753872687),(1896448000,95767790725711,95768168422540)]
theorem point_links_checked14438 : (cuts14438.take 2).map (fun c => (1896349697-1+2*2^9*c.k,95767105888188+c.lower,95767483584554+c.upper)) = pointBounds14438 := by
 decide +kernel
def cuts14439 : List PrefixCut := [⟨26,191014642,191014772⟩,
⟨84,607764385,607764798⟩,
⟨128,916607888,916608508⟩]
theorem checked14439 : checkPrefixCuts (2^48) 1896480769 9 Manual.Count131072.C014439.packed 128 cuts14439 = true := by
 decide +kernel
def pointBounds14439 : List (Nat × Nat × Nat) := [(1896507392,95768209714796,95768587411908),(1896566784,95768626464539,95769004161934)]
theorem point_links_checked14439 : (cuts14439.take 2).map (fun c => (1896480769-1+2*2^9*c.k,95768018700154+c.lower,95768396397136+c.upper)) = pointBounds14439 := by
 decide +kernel
def cuts14440 : List PrefixCut := [⟨14,98691824,98691890⟩,
⟨72,502207383,502207721⟩,
⟨128,901110089,901110701⟩]
theorem checked14440 : checkPrefixCuts (2^48) 1896611841 9 Manual.Count131072.C014440.packed 128 cuts14440 = true := by
 decide +kernel
def pointBounds14440 : List (Nat × Nat × Nat) := [(1896626176,95769033999866,95769411697534),(1896685568,95769437515425,95769815213365)]
theorem point_links_checked14440 : (cuts14440.take 2).map (fun c => (1896611841-1+2*2^9*c.k,95768935308042+c.lower,95769313005644+c.upper)) = pointBounds14440 := by
 decide +kernel
def cuts14441 : List PrefixCut := [⟨2,14691499,14691510⟩,
⟨60,422930485,422930776⟩,
⟨118,835311672,835312240⟩,
⟨128,902235210,902235823⟩]
theorem checked14441 : checkPrefixCuts (2^48) 1896742913 9 Manual.Count131072.C014441.packed 128 cuts14441 = true := by
 decide +kernel
def pointBounds14441 : List (Nat × Nat × Nat) := [(1896744960,95769851109630,95770228807855),(1896804352,95770259348616,95770637047121),(1896863744,95770671729803,95771049428585)]
theorem point_links_checked14441 : (cuts14441.take 3).map (fun c => (1896742913-1+2*2^9*c.k,95769836418131+c.lower,95770214116345+c.upper)) = pointBounds14441 := by
 decide +kernel
def cuts14442 : List PrefixCut := [⟨48,349154315,349154552⟩,
⟨106,760025851,760026369⟩,
⟨128,917901576,917902204⟩]
theorem checked14442 : checkPrefixCuts (2^48) 1896873985 9 Manual.Count131072.C014442.packed 128 cuts14442 = true := by
 decide +kernel
def pointBounds14442 : List (Nat × Nat × Nat) := [(1896923136,95771087807656,95771465506720),(1896982528,95771498679192,95771876378537)]
theorem point_links_checked14442 : (cuts14442.take 2).map (fun c => (1896873985-1+2*2^9*c.k,95770738653341+c.lower,95771116352168+c.upper)) = pointBounds14442 := by
 decide +kernel
def cuts14443 : List PrefixCut := [⟨36,252834596,252834771⟩,
⟨94,662493400,662493849⟩,
⟨128,902703888,902704499⟩]
theorem checked14443 : checkPrefixCuts (2^48) 1897005057 9 Manual.Count131072.C014443.packed 128 cuts14443 = true := by
 decide +kernel
def pointBounds14443 : List (Nat × Nat × Nat) := [(1897041920,95771909389513,95772287089143),(1897101312,95772319048317,95772696748221)]
theorem point_links_checked14443 : (cuts14443.take 2).map (fun c => (1897005057-1+2*2^9*c.k,95771656554917+c.lower,95772034254372+c.upper)) = pointBounds14443 := by
 decide +kernel
def cuts14444 : List PrefixCut := [⟨24,171067581,171067697⟩,
⟨82,591382940,591383335⟩,
⟨128,925192716,925193339⟩]
theorem checked14444 : checkPrefixCuts (2^48) 1897136129 9 Manual.Count131072.C014444.packed 128 cuts14444 = true := by
 decide +kernel
def pointBounds14444 : List (Nat × Nat × Nat) := [(1897160704,95772730326386,95773108026568),(1897220096,95773150641745,95773528342206)]
theorem point_links_checked14444 : (cuts14444.take 2).map (fun c => (1897136129-1+2*2^9*c.k,95772559258805+c.lower,95772936958871+c.upper)) = pointBounds14444 := by
 decide +kernel
def cuts14445 : List PrefixCut := [⟨12,87085904,87085961⟩,
⟨70,500402374,500402708⟩,
⟨128,923941940,923942565⟩]
theorem checked14445 : checkPrefixCuts (2^48) 1897267201 9 Manual.Count131072.C014445.packed 128 cuts14445 = true := by
 decide +kernel
def pointBounds14445 : List (Nat × Nat × Nat) := [(1897279488,95773571537425,95773949238171),(1897338880,95773984853895,95774362554918),(1897398272,95774408393461,95774786094775)]
theorem point_links_checked14445 : (cuts14445.take 3).map (fun c => (1897267201-1+2*2^9*c.k,95773484451521+c.lower,95773862152210+c.upper)) = pointBounds14445 := by
 decide +kernel
def cuts14446 : List PrefixCut := [⟨58,411362059,411362341⟩,
⟨116,825084654,825085225⟩,
⟨128,910824047,910824677⟩]
theorem checked14446 : checkPrefixCuts (2^48) 1897398273 9 Manual.Count131072.C014446.packed 128 cuts14446 = true := by
 decide +kernel
def pointBounds14446 : List (Nat × Nat × Nat) := [(1897457664,95774819755520,95775197457116),(1897517056,95775233478115,95775611180000)]
theorem point_links_checked14446 : (cuts14446.take 2).map (fun c => (1897398273-1+2*2^9*c.k,95774408393461+c.lower,95774786094775+c.upper)) = pointBounds14446 := by
 decide +kernel
def cuts14447 : List PrefixCut := [⟨46,327970260,327970481⟩,
⟨104,733063811,733064305⟩,
⟨128,907497871,907498486⟩]
theorem checked14447 : checkPrefixCuts (2^48) 1897529345 9 Manual.Count131072.C014447.packed 128 cuts14447 = true := by
 decide +kernel
def pointBounds14447 : List (Nat × Nat × Nat) := [(1897576448,95775647187768,95776024889933),(1897635840,95776052281319,95776429983757)]
theorem point_links_checked14447 : (cuts14447.take 2).map (fun c => (1897529345-1+2*2^9*c.k,95775319217508+c.lower,95775696919452+c.upper)) = pointBounds14447 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S2.B000138
