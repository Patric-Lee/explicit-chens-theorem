import PlattAssemblyKernel
import PlattCertificates.Count131072.C013232
import PlattCertificates.Count131072.C013233
import PlattCertificates.Count131072.C013234
import PlattCertificates.Count131072.C013235
import PlattCertificates.Count131072.C013236
import PlattCertificates.Count131072.C013237
import PlattCertificates.Count131072.C013238
import PlattCertificates.Count131072.C013239
import PlattCertificates.Count131072.C013240
import PlattCertificates.Count131072.C013241
import PlattCertificates.Count131072.C013242
import PlattCertificates.Count131072.C013243
import PlattCertificates.Count131072.C013244
import PlattCertificates.Count131072.C013245
import PlattCertificates.Count131072.C013246
import PlattCertificates.Count131072.C013247
import PlattCertificates.Count131072.C013248
import PlattCertificates.Count131072.C013249
import PlattCertificates.Count131072.C013250
import PlattCertificates.Count131072.C013251
import PlattCertificates.Count131072.C013252
import PlattCertificates.Count131072.C013253
import PlattCertificates.Count131072.C013254
import PlattCertificates.Count131072.C013255
import PlattCertificates.Count131072.C013256
import PlattCertificates.Count131072.C013257
import PlattCertificates.Count131072.C013258
import PlattCertificates.Count131072.C013259
import PlattCertificates.Count131072.C013260
import PlattCertificates.Count131072.C013261
import PlattCertificates.Count131072.C013262
import PlattCertificates.Count131072.C013263
namespace ChenEffective.PlattWindow.Assembly.Prefix.S2.B000101
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts13232 : List PrefixCut := [⟨34,257462205,257462388⟩,
⟨88,685745161,685745651⟩,
⟨128,994197465,994198175⟩]
theorem checked13232 : checkPrefixCuts (2^48) 1738276865 9 Manual.Count131072.C013232.packed 128 cuts13232 = true := by
 decide +kernel
def pointBounds13232 : List (Nat × Nat × Nat) := [(1738311680,94618344366170,94618721259902),(1738366976,94618772649126,94619149543165)]
theorem point_links_checked13232 : (cuts13232.take 2).map (fun c => (1738276865-1+2*2^9*c.k,94618086903965+c.lower,94618463797514+c.upper)) = pointBounds13232 := by
 decide +kernel
def cuts13233 : List PrefixCut := [⟨14,108320906,108320986⟩,
⟨68,524595190,524595567⟩,
⟨122,957046832,957047519⟩,
⟨128,1004484529,1004485248⟩]
theorem checked13233 : checkPrefixCuts (2^48) 1738407937 9 Manual.Count131072.C013233.packed 128 cuts13233 = true := by
 decide +kernel
def pointBounds13233 : List (Nat × Nat × Nat) := [(1738422272,94619189422336,94619566316675),(1738477568,94619605696620,94619982591256),(1738532864,94620038148262,94620415043208)]
theorem point_links_checked13233 : (cuts13233.take 3).map (fun c => (1738407937-1+2*2^9*c.k,94619081101430+c.lower,94619457995689+c.upper)) = pointBounds13233 := by
 decide +kernel
def cuts13234 : List PrefixCut := [⟨48,376743164,376743432⟩,
⟨102,789254025,789254594⟩,
⟨128,990324074,990324784⟩]
theorem checked13234 : checkPrefixCuts (2^48) 1738539009 9 Manual.Count131072.C013234.packed 128 cuts13234 = true := by
 decide +kernel
def pointBounds13234 : List (Nat × Nat × Nat) := [(1738588160,94620462329123,94620839224369),(1738643456,94620874839984,94621251735531)]
theorem point_links_checked13234 : (cuts13234.take 2).map (fun c => (1738539009-1+2*2^9*c.k,94620085585959+c.lower,94620462480937+c.upper)) = pointBounds13234 := by
 decide +kernel
def cuts13235 : List PrefixCut := [⟨28,221141137,221141292⟩,
⟨82,638806148,638806606⟩,
⟨128,995267852,995268563⟩]
theorem checked13235 : checkPrefixCuts (2^48) 1738670081 9 Manual.Count131072.C013235.packed 128 cuts13235 = true := by
 decide +kernel
def pointBounds13235 : List (Nat × Nat × Nat) := [(1738698752,94621297051170,94621673947013),(1738754048,94621714716181,94622091612327)]
theorem point_links_checked13235 : (cuts13235.take 2).map (fun c => (1738670081-1+2*2^9*c.k,94621075910033+c.lower,94621452805721+c.upper)) = pointBounds13235 := by
 decide +kernel
def cuts13236 : List PrefixCut := [⟨8,63618177,63618226⟩,
⟨62,480770964,480771315⟩,
⟨116,901795345,901795997⟩,
⟨128,1001019870,1001020595⟩]
theorem checked13236 : checkPrefixCuts (2^48) 1738801153 9 Manual.Count131072.C013236.packed 128 cuts13236 = true := by
 decide +kernel
def pointBounds13236 : List (Nat × Nat × Nat) := [(1738809344,94622134796062,94622511692510),(1738864640,94622551948849,94622928845599),(1738919936,94622972973230,94623349870281)]
theorem point_links_checked13236 : (cuts13236.take 3).map (fun c => (1738801153-1+2*2^9*c.k,94622071177885+c.lower,94622448074284+c.upper)) = pointBounds13236 := by
 decide +kernel
def cuts13237 : List PrefixCut := [⟨42,324052641,324052879⟩,
⟨96,746507068,746507613⟩,
⟨128,997545425,997546149⟩]
theorem checked13237 : checkPrefixCuts (2^48) 1738932225 9 Manual.Count131072.C013237.packed 128 cuts13237 = true := by
 decide +kernel
def pointBounds13237 : List (Nat × Nat × Nat) := [(1738975232,94623396250396,94623773147758),(1739030528,94623818704823,94624195602492)]
theorem point_links_checked13237 : (cuts13237.take 2).map (fun c => (1738932225-1+2*2^9*c.k,94623072197755+c.lower,94623449094879+c.upper)) = pointBounds13237 := by
 decide +kernel
def cuts13238 : List PrefixCut := [⟨22,167194424,167194543⟩,
⟨76,581691252,581691666⟩,
⟨128,998117419,998118127⟩]
theorem checked13238 : checkPrefixCuts (2^48) 1739063297 9 Manual.Count131072.C013238.packed 128 cuts13238 = true := by
 decide +kernel
def pointBounds13238 : List (Nat × Nat × Nat) := [(1739085824,94624236937604,94624613835571),(1739141120,94624651434432,94625028332694)]
theorem point_links_checked13238 : (cuts13238.take 2).map (fun c => (1739063297-1+2*2^9*c.k,94624069743180+c.lower,94624446641028+c.upper)) = pointBounds13238 := by
 decide +kernel
def cuts13239 : List PrefixCut := [⟨2,16184201,16184213⟩,
⟨56,429845484,429845793⟩,
⟨110,849481560,849482171⟩,
⟨128,995452920,995453636⟩]
theorem checked13239 : checkPrefixCuts (2^48) 1739194369 9 Manual.Count131072.C013239.packed 128 cuts13239 = true := by
 decide +kernel
def pointBounds13239 : List (Nat × Nat × Nat) := [(1739196416,94625084044800,94625460943368),(1739251712,94625497706083,94625874604948),(1739307008,94625917342159,94626294241326)]
theorem point_links_checked13239 : (cuts13239.take 3).map (fun c => (1739194369-1+2*2^9*c.k,94625067860599+c.lower,94625444759155+c.upper)) = pointBounds13239 := by
 decide +kernel
def cuts13240 : List PrefixCut := [⟨36,277859043,277859245⟩,
⟨90,691804591,691805091⟩,
⟨128,990037982,990038695⟩]
theorem checked13240 : checkPrefixCuts (2^48) 1739325441 9 Manual.Count131072.C013240.packed 128 cuts13240 = true := by
 decide +kernel
def pointBounds13240 : List (Nat × Nat × Nat) := [(1739362304,94626341172562,94626718072036),(1739417600,94626755118110,94627132017882)]
theorem point_links_checked13240 : (cuts13240.take 2).map (fun c => (1739325441-1+2*2^9*c.k,94626063313519+c.lower,94626440212791+c.upper)) = pointBounds13240 := by
 decide +kernel
def cuts13241 : List PrefixCut := [⟨16,126540846,126540937⟩,
⟨70,549521682,549522071⟩,
⟨124,972974450,972975138⟩,
⟨128,1003717537,1003718248⟩]
theorem checked13241 : checkPrefixCuts (2^48) 1739456513 9 Manual.Count131072.C013241.packed 128 cuts13241 = true := by
 decide +kernel
def pointBounds13241 : List (Nat × Nat × Nat) := [(1739472896,94627179892347,94627556792423),(1739528192,94627602873183,94627979773557),(1739583488,94628026325951,94628403226624)]
theorem point_links_checked13241 : (cuts13241.take 3).map (fun c => (1739456513-1+2*2^9*c.k,94627053351501+c.lower,94627430251486+c.upper)) = pointBounds13241 := by
 decide +kernel
def cuts13242 : List PrefixCut := [⟨50,379590194,379590472⟩,
⟨104,802854290,802854872⟩,
⟨128,999434590,999435311⟩]
theorem checked13242 : checkPrefixCuts (2^48) 1739587585 9 Manual.Count131072.C013242.packed 128 cuts13242 = true := by
 decide +kernel
def pointBounds13242 : List (Nat × Nat × Nat) := [(1739638784,94628436659232,94628813560206),(1739694080,94628859923328,94629236824606)]
theorem point_links_checked13242 : (cuts13242.take 2).map (fun c => (1739587585-1+2*2^9*c.k,94628057069038+c.lower,94628433969734+c.upper)) = pointBounds13242 := by
 decide +kernel
def cuts13243 : List PrefixCut := [⟨30,233627500,233627671⟩,
⟨84,650554872,650555347⟩,
⟨128,994344242,994344963⟩]
theorem checked13243 : checkPrefixCuts (2^48) 1739718657 9 Manual.Count131072.C013243.packed 128 cuts13243 = true := by
 decide +kernel
def pointBounds13243 : List (Nat × Nat × Nat) := [(1739749376,94629290131128,94629667032716),(1739804672,94629707058500,94630083960392)]
theorem point_links_checked13243 : (cuts13243.take 2).map (fun c => (1739718657-1+2*2^9*c.k,94629056503628+c.lower,94629433405045+c.upper)) = pointBounds13243 := by
 decide +kernel
def cuts13244 : List PrefixCut := [⟨10,77492936,77492992⟩,
⟨64,501350274,501350633⟩,
⟨118,926650105,926650766⟩,
⟨128,1004622963,1004623678⟩]
theorem checked13244 : checkPrefixCuts (2^48) 1739849729 9 Manual.Count131072.C013244.packed 128 cuts13244 = true := by
 decide +kernel
def pointBounds13244 : List (Nat × Nat × Nat) := [(1739859968,94630128340806,94630505243000),(1739915264,94630552198144,94630929100641),(1739970560,94630977497975,94631354400774)]
theorem point_links_checked13244 : (cuts13244.take 3).map (fun c => (1739849729-1+2*2^9*c.k,94630050847870+c.lower,94630427750008+c.upper)) = pointBounds13244 := by
 decide +kernel
def cuts13245 : List PrefixCut := [⟨44,336475050,336475293⟩,
⟨98,759321401,759321949⟩,
⟨128,995650164,995650880⟩]
theorem checked13245 : checkPrefixCuts (2^48) 1739980801 9 Manual.Count131072.C013245.packed 128 cuts13245 = true := by
 decide +kernel
def pointBounds13245 : List (Nat × Nat × Nat) := [(1740025856,94631391945883,94631768848979),(1740081152,94631814792234,94632191695635)]
theorem point_links_checked13245 : (cuts13245.take 2).map (fun c => (1739980801-1+2*2^9*c.k,94631055470833+c.lower,94631432373686+c.upper)) = pointBounds13245 := by
 decide +kernel
def cuts13246 : List PrefixCut := [⟨24,189739324,189739463⟩,
⟨78,606250508,606250946⟩,
⟨128,986032343,986033052⟩]
theorem checked13246 : checkPrefixCuts (2^48) 1740111873 9 Manual.Count131072.C013246.packed 128 cuts13246 = true := by
 decide +kernel
def pointBounds13246 : List (Nat × Nat × Nat) := [(1740136448,94632240860321,94632617764029),(1740191744,94632657371505,94633034275512)]
theorem point_links_checked13246 : (cuts13246.take 2).map (fun c => (1740111873-1+2*2^9*c.k,94632051120997+c.lower,94632428024566+c.upper)) = pointBounds13246 := by
 decide +kernel
def cuts13247 : List PrefixCut := [⟨4,31054925,31054946⟩,
⟨58,458052759,458053085⟩,
⟨112,882611030,882611655⟩,
⟨128,1003587429,1003588142⟩]
theorem checked13247 : checkPrefixCuts (2^48) 1740242945 9 Manual.Count131072.C013247.packed 128 cuts13247 = true := by
 decide +kernel
def pointBounds13247 : List (Nat × Nat × Nat) := [(1740247040,94633068208265,94633445112564),(1740302336,94633495206099,94633872110703),(1740357632,94633919764370,94634296669273)]
theorem point_links_checked13247 : (cuts13247.take 3).map (fun c => (1740242945-1+2*2^9*c.k,94633037153340+c.lower,94633414057618+c.upper)) = pointBounds13247 := by
 decide +kernel
def cuts13248 : List PrefixCut := [⟨38,302274505,302274724⟩,
⟨92,720175037,720175552⟩,
⟨128,995910966,995911680⟩]
theorem checked13248 : checkPrefixCuts (2^48) 1740374017 9 Manual.Count131072.C013248.packed 128 cuts13248 = true := by
 decide +kernel
def pointBounds13248 : List (Nat × Nat × Nat) := [(1740412928,94634343015274,94634719920484),(1740468224,94634760915806,94635137821312)]
theorem point_links_checked13248 : (cuts13248.take 2).map (fun c => (1740374017-1+2*2^9*c.k,94634040740769+c.lower,94634417645760+c.upper)) = pointBounds13248 := by
 decide +kernel
def cuts13249 : List PrefixCut := [⟨18,137138043,137138141⟩,
⟨72,559863476,559863877⟩,
⟨126,981281795,981282500⟩,
⟨128,995026987,995027701⟩]
theorem checked13249 : checkPrefixCuts (2^48) 1740505089 9 Manual.Count131072.C013249.packed 128 cuts13249 = true := by
 decide +kernel
def pointBounds13249 : List (Nat × Nat × Nat) := [(1740523520,94635173789778,94635550695581),(1740578816,94635596515211,94635973421317),(1740634112,94636017933530,94636394839940)]
theorem point_links_checked13249 : (cuts13249.take 3).map (fun c => (1740505089-1+2*2^9*c.k,94635036651735+c.lower,94635413557440+c.upper)) = pointBounds13249 := by
 decide +kernel
def cuts13250 : List PrefixCut := [⟨52,407983174,407983468⟩,
⟨106,828727945,828728542⟩,
⟨128,999318198,999318920⟩]
theorem checked13250 : checkPrefixCuts (2^48) 1740636161 9 Manual.Count131072.C013250.packed 128 cuts13250 = true := by
 decide +kernel
def pointBounds13250 : List (Nat × Nat × Nat) := [(1740689408,94636439661896,94636816568609),(1740744704,94636860406667,94637237313683)]
theorem point_links_checked13250 : (cuts13250.take 2).map (fun c => (1740636161-1+2*2^9*c.k,94636031678722+c.lower,94636408585141+c.upper)) = pointBounds13250 := by
 decide +kernel
def cuts13251 : List PrefixCut := [⟨32,237205606,237205780⟩,
⟨86,655336582,655337060⟩,
⟨128,994229791,994230509⟩]
theorem checked13251 : checkPrefixCuts (2^48) 1740767233 9 Manual.Count131072.C013251.packed 128 cuts13251 = true := by
 decide +kernel
def pointBounds13251 : List (Nat × Nat × Nat) := [(1740800000,94637268202526,94637645109841),(1740855296,94637686333502,94638063241121)]
theorem point_links_checked13251 : (cuts13251.take 2).map (fun c => (1740767233-1+2*2^9*c.k,94637030996920+c.lower,94637407904061+c.upper)) = pointBounds13251 := by
 decide +kernel
def cuts13252 : List PrefixCut := [⟨12,93291174,93291241⟩,
⟨66,517862885,517863251⟩,
⟨120,945331214,945331878⟩,
⟨128,1002563066,1002563772⟩]
theorem checked13252 : checkPrefixCuts (2^48) 1740898305 9 Manual.Count131072.C013252.packed 128 cuts13252 = true := by
 decide +kernel
def pointBounds13252 : List (Nat × Nat × Nat) := [(1740910592,94638118517885,94638495425811),(1740965888,94638543089596,94638919997821),(1741021184,94638970557925,94639347466448)]
theorem point_links_checked13252 : (cuts13252.take 3).map (fun c => (1740898305-1+2*2^9*c.k,94638025226711+c.lower,94638402134570+c.upper)) = pointBounds13252 := by
 decide +kernel
def cuts13253 : List PrefixCut := [⟨46,357612661,357612919⟩,
⟨100,785700462,785701029⟩,
⟨128,1001679162,1001679885⟩]
theorem checked13253 : checkPrefixCuts (2^48) 1741029377 9 Manual.Count131072.C013253.packed 128 cuts13253 = true := by
 decide +kernel
def pointBounds13253 : List (Nat × Nat × Nat) := [(1741076480,94639385402438,94639762311261),(1741131776,94639813490239,94640190399371)]
theorem point_links_checked13253 : (cuts13253.take 2).map (fun c => (1741029377-1+2*2^9*c.k,94639027789777+c.lower,94639404698342+c.upper)) = pointBounds13253 := by
 decide +kernel
def cuts13254 : List PrefixCut := [⟨26,205629113,205629259⟩,
⟨80,623020504,623020954⟩,
⟨128,997239077,997239790⟩]
theorem checked13254 : checkPrefixCuts (2^48) 1741160449 9 Manual.Count131072.C013254.packed 128 cuts13254 = true := by
 decide +kernel
def pointBounds13254 : List (Nat × Nat × Nat) := [(1741187072,94640235098052,94640612007486),(1741242368,94640652489443,94641029399181)]
theorem point_links_checked13254 : (cuts13254.take 2).map (fun c => (1741160449-1+2*2^9*c.k,94640029468939+c.lower,94640406378227+c.upper)) = pointBounds13254 := by
 decide +kernel
def cuts13255 : List PrefixCut := [⟨6,44452898,44452929⟩,
⟨60,454220631,454220956⟩,
⟨114,868016185,868016807⟩,
⟨128,977766811,977767512⟩]
theorem checked13255 : checkPrefixCuts (2^48) 1741291521 9 Manual.Count131072.C013255.packed 128 cuts13255 = true := by
 decide +kernel
def pointBounds13255 : List (Nat × Nat × Nat) := [(1741297664,94641071160914,94641448070946),(1741352960,94641480928647,94641857838973),(1741408256,94641894724201,94642271634824)]
theorem point_links_checked13255 : (cuts13255.take 3).map (fun c => (1741291521-1+2*2^9*c.k,94641026708016+c.lower,94641403618017+c.upper)) = pointBounds13255 := by
 decide +kernel
def cuts13256 : List PrefixCut := [⟨40,304355156,304355370⟩,
⟨94,722650093,722650608⟩,
⟨128,990138621,990139321⟩]
theorem checked13256 : checkPrefixCuts (2^48) 1741422593 9 Manual.Count131072.C013256.packed 128 cuts13256 = true := by
 decide +kernel
def pointBounds13256 : List (Nat × Nat × Nat) := [(1741463552,94642308829983,94642685740899),(1741518848,94642727124920,94643104036137)]
theorem point_links_checked13256 : (cuts13256.take 2).map (fun c => (1741422593-1+2*2^9*c.k,94642004474827+c.lower,94642381385529+c.upper)) = pointBounds13256 := by
 decide +kernel
def cuts13257 : List PrefixCut := [⟨20,153864073,153864179⟩,
⟨74,577304190,577304594⟩,
⟨128,988609926,988610622⟩]
theorem checked13257 : checkPrefixCuts (2^48) 1741553665 9 Manual.Count131072.C013257.packed 128 cuts13257 = true := by
 decide +kernel
def pointBounds13257 : List (Nat × Nat × Nat) := [(1741574144,94643148477521,94643525389029),(1741629440,94643571917638,94643948829444),(1741684736,94643983223374,94644360135472)]
theorem point_links_checked13257 : (cuts13257.take 3).map (fun c => (1741553665-1+2*2^9*c.k,94642994613448+c.lower,94643371524850+c.upper)) = pointBounds13257 := by
 decide +kernel
def cuts13258 : List PrefixCut := [⟨54,419049889,419050191⟩,
⟨108,840833715,840834320⟩,
⟨128,999201221,999201940⟩]
theorem checked13258 : checkPrefixCuts (2^48) 1741684737 9 Manual.Count131072.C013258.packed 128 cuts13258 = true := by
 decide +kernel
def pointBounds13258 : List (Nat × Nat × Nat) := [(1741740032,94644402273263,94644779185663),(1741795328,94644824057089,94645200969792)]
theorem point_links_checked13258 : (cuts13258.take 2).map (fun c => (1741684737-1+2*2^9*c.k,94643983223374+c.lower,94644360135472+c.upper)) = pointBounds13258 := by
 decide +kernel
def cuts13259 : List PrefixCut := [⟨34,266150094,266150287⟩,
⟨88,691946917,691947414⟩,
⟨128,1005105010,1005105730⟩]
theorem checked13259 : checkPrefixCuts (2^48) 1741815809 9 Manual.Count131072.C013259.packed 128 cuts13259 = true := by
 decide +kernel
def pointBounds13259 : List (Nat × Nat × Nat) := [(1741850624,94645248574689,94645625487699),(1741905920,94645674371512,94646051284826)]
theorem point_links_checked13259 : (cuts13259.take 2).map (fun c => (1741815809-1+2*2^9*c.k,94644982424595+c.lower,94645359337412+c.upper)) = pointBounds13259 := by
 decide +kernel
def cuts13260 : List PrefixCut := [⟨14,105838636,105838714⟩,
⟨68,530154213,530154596⟩,
⟨122,953163694,953164384⟩,
⟨128,999050853,999051576⟩]
theorem checked13260 : checkPrefixCuts (2^48) 1741946881 9 Manual.Count131072.C013260.packed 128 cuts13260 = true := by
 decide +kernel
def pointBounds13260 : List (Nat × Nat × Nat) := [(1741961216,94646093368241,94646470281856),(1742016512,94646517683818,94646894597738),(1742071808,94646940693299,94647317607526)]
theorem point_links_checked13260 : (cuts13260.take 3).map (fun c => (1741946881-1+2*2^9*c.k,94645987529605+c.lower,94646364443142+c.upper)) = pointBounds13260 := by
 decide +kernel
def cuts13261 : List PrefixCut := [⟨48,370322856,370323123⟩,
⟨102,795729016,795729589⟩,
⟨128,992513082,992513797⟩]
theorem checked13261 : checkPrefixCuts (2^48) 1742077953 9 Manual.Count131072.C013261.packed 128 cuts13261 = true := by
 decide +kernel
def pointBounds13261 : List (Nat × Nat × Nat) := [(1742127104,94647356903314,94647733817841),(1742182400,94647782309474,94648159224307)]
theorem point_links_checked13261 : (cuts13261.take 2).map (fun c => (1742077953-1+2*2^9*c.k,94646986580458+c.lower,94647363494718+c.upper)) = pointBounds13261 := by
 decide +kernel
def cuts13262 : List PrefixCut := [⟨28,219884170,219884326⟩,
⟨82,649140738,649141201⟩,
⟨128,1011340541,1011341263⟩]
theorem checked13262 : checkPrefixCuts (2^48) 1742209025 9 Manual.Count131072.C013262.packed 128 cuts13262 = true := by
 decide +kernel
def pointBounds13262 : List (Nat × Nat × Nat) := [(1742237696,94648198977710,94648575892841),(1742292992,94648628234278,94649005149716)]
theorem point_links_checked13262 : (cuts13262.take 2).map (fun c => (1742209025-1+2*2^9*c.k,94647979093540+c.lower,94648356008515+c.upper)) = pointBounds13262 := by
 decide +kernel
def cuts13263 : List PrefixCut := [⟨8,60581069,60581113⟩,
⟨62,471070854,471071195⟩,
⟨116,888817007,888817648⟩,
⟨128,981863092,981863800⟩]
theorem checked13263 : checkPrefixCuts (2^48) 1742340097 9 Manual.Count131072.C013263.packed 128 cuts13263 = true := by
 decide +kernel
def pointBounds13263 : List (Nat × Nat × Nat) := [(1742348288,94649051015150,94649427930891),(1742403584,94649461504935,94649838420973),(1742458880,94649879251088,94650256167426)]
theorem point_links_checked13263 : (cuts13263.take 3).map (fun c => (1742340097-1+2*2^9*c.k,94648990434081+c.lower,94649367349778+c.upper)) = pointBounds13263 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S2.B000101
