import PlattAssemblyKernel
import PlattCertificates.Count131072.C011504
import PlattCertificates.Count131072.C011505
import PlattCertificates.Count131072.C011506
import PlattCertificates.Count131072.C011507
import PlattCertificates.Count131072.C011508
import PlattCertificates.Count131072.C011509
import PlattCertificates.Count131072.C011510
import PlattCertificates.Count131072.C011511
import PlattCertificates.Count131072.C011512
import PlattCertificates.Count131072.C011513
import PlattCertificates.Count131072.C011514
import PlattCertificates.Count131072.C011515
import PlattCertificates.Count131072.C011516
import PlattCertificates.Count131072.C011517
import PlattCertificates.Count131072.C011518
import PlattCertificates.Count131072.C011519
import PlattCertificates.Count131072.C011520
import PlattCertificates.Count131072.C011521
import PlattCertificates.Count131072.C011522
import PlattCertificates.Count131072.C011523
import PlattCertificates.Count131072.C011524
import PlattCertificates.Count131072.C011525
import PlattCertificates.Count131072.C011526
import PlattCertificates.Count131072.C011527
import PlattCertificates.Count131072.C011528
import PlattCertificates.Count131072.C011529
import PlattCertificates.Count131072.C011530
import PlattCertificates.Count131072.C011531
import PlattCertificates.Count131072.C011532
import PlattCertificates.Count131072.C011533
import PlattCertificates.Count131072.C011534
import PlattCertificates.Count131072.C011535
namespace ChenEffective.PlattWindow.Assembly.Prefix.S2.B000047
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts11504 : List PrefixCut := [⟨38,334201668,334201935⟩,
⟨85,763159149,763159752⟩,
⟨128,1150400523,1150401431⟩]
theorem checked11504 : checkPrefixCuts (2^48) 1511784449 9 Manual.Count131072.C011504.packed 128 cuts11504 = true := by
 decide +kernel
def pointBounds11504 : List (Nat × Nat × Nat) := [(1511823360,92765498928316,92765874429566),(1511871488,92765927885797,92766303387383)]
theorem point_links_checked11504 : (cuts11504.take 2).map (fun c => (1511784449-1+2*2^9*c.k,92765164726648+c.lower,92765540227631+c.upper)) = pointBounds11504 := by
 decide +kernel
def cuts11505 : List PrefixCut := [⟨4,38909693,38909723⟩,
⟨51,469701500,469701870⟩,
⟨98,893405393,893406098⟩,
⟨128,1164635823,1164636740⟩]
theorem checked11505 : checkPrefixCuts (2^48) 1511915521 9 Manual.Count131072.C011505.packed 128 cuts11505 = true := by
 decide +kernel
def pointBounds11505 : List (Nat × Nat × Nat) := [(1511919616,92766354036864,92766729538785),(1511967744,92766784828671,92767160330932),(1512015872,92767208532564,92767584035160)]
theorem point_links_checked11505 : (cuts11505.take 3).map (fun c => (1511915521-1+2*2^9*c.k,92766315127171+c.lower,92766690629062+c.upper)) = pointBounds11505 := by
 decide +kernel
def cuts11506 : List PrefixCut := [⟨17,147433814,147433930⟩,
⟨64,578929027,578929483⟩,
⟨111,1000358725,1000359512⟩,
⟨128,1158577589,1158578498⟩]
theorem checked11506 : checkPrefixCuts (2^48) 1512046593 9 Manual.Count131072.C011506.packed 128 cuts11506 = true := by
 decide +kernel
def pointBounds11506 : List (Nat × Nat × Nat) := [(1512064000,92767627196808,92768002699732),(1512112128,92768058692021,92768434195285),(1512160256,92768480121719,92768855625314)]
theorem point_links_checked11506 : (cuts11506.take 3).map (fun c => (1512046593-1+2*2^9*c.k,92767479762994+c.lower,92767855265802+c.upper)) = pointBounds11506 := by
 decide +kernel
def cuts11507 : List PrefixCut := [⟨30,260219273,260219475⟩,
⟨77,676968887,676969417⟩,
⟨124,1098730601,1098731466⟩,
⟨128,1135582929,1135583823⟩]
theorem checked11507 : checkPrefixCuts (2^48) 1512177665 9 Manual.Count131072.C011507.packed 128 cuts11507 = true := by
 decide +kernel
def pointBounds11507 : List (Nat × Nat × Nat) := [(1512208384,92768898559856,92769274063775),(1512256512,92769315309470,92769690813717),(1512304640,92769737071184,92770112575766)]
theorem point_links_checked11507 : (cuts11507.take 3).map (fun c => (1512177665-1+2*2^9*c.k,92768638340583+c.lower,92769013844300+c.upper)) = pointBounds11507 := by
 decide +kernel
def cuts11508 : List PrefixCut := [⟨43,386943278,386943581⟩,
⟨90,822822900,822823545⟩,
⟨128,1164332670,1164333585⟩]
theorem checked11508 : checkPrefixCuts (2^48) 1512308737 9 Manual.Count131072.C011508.packed 128 cuts11508 = true := by
 decide +kernel
def pointBounds11508 : List (Nat × Nat × Nat) := [(1512352768,92770160866790,92770536371704),(1512400896,92770596746412,92770972251668)]
theorem point_links_checked11508 : (cuts11508.take 2).map (fun c => (1512308737-1+2*2^9*c.k,92769773923512+c.lower,92770149428123+c.upper)) = pointBounds11508 := by
 decide +kernel
def cuts11509 : List PrefixCut := [⟨9,79095021,79095083⟩,
⟨56,492800649,492801037⟩,
⟨103,913378707,913379425⟩,
⟨128,1140224738,1140225633⟩]
theorem checked11509 : checkPrefixCuts (2^48) 1512439809 9 Manual.Count131072.C011509.packed 128 cuts11509 = true := by
 decide +kernel
def pointBounds11509 : List (Nat × Nat × Nat) := [(1512449024,92771017351203,92771392856791),(1512497152,92771431056831,92771806562745),(1512545280,92771851634889,92772227141133)]
theorem point_links_checked11509 : (cuts11509.take 3).map (fun c => (1512439809-1+2*2^9*c.k,92770938256182+c.lower,92771313761708+c.upper)) = pointBounds11509 := by
 decide +kernel
def cuts11510 : List PrefixCut := [⟨22,201162183,201162341⟩,
⟨69,627482124,627482615⟩,
⟨116,1045228767,1045229588⟩,
⟨128,1157804150,1157805058⟩]
theorem checked11510 : checkPrefixCuts (2^48) 1512570881 9 Manual.Count131072.C011510.packed 128 cuts11510 = true := by
 decide +kernel
def pointBounds11510 : List (Nat × Nat × Nat) := [(1512593408,92772279643103,92772655149682),(1512641536,92772705963044,92773081469956),(1512689664,92773123709687,92773499216929)]
theorem point_links_checked11510 : (cuts11510.take 3).map (fun c => (1512570881-1+2*2^9*c.k,92772078480920+c.lower,92772453987341+c.upper)) = pointBounds11510 := by
 decide +kernel
def cuts11511 : List PrefixCut := [⟨35,316136393,316136640⟩,
⟨82,749300020,749300607⟩,
⟨128,1171472383,1171473297⟩]
theorem checked11511 : checkPrefixCuts (2^48) 1512701953 9 Manual.Count131072.C011511.packed 128 cuts11511 = true := by
 decide +kernel
def pointBounds11511 : List (Nat × Nat × Nat) := [(1512737792,92773552421463,92773927929039),(1512785920,92773985585090,92774361093006)]
theorem point_links_checked11511 : (cuts11511.take 2).map (fun c => (1512701953-1+2*2^9*c.k,92773236285070+c.lower,92773611792399+c.upper)) = pointBounds11511 := by
 decide +kernel
def cuts11512 : List PrefixCut := [⟨1,8744729,8744736⟩,
⟨48,423461388,423461723⟩,
⟨95,852676680,852677353⟩,
⟨128,1149044884,1149045787⟩]
theorem checked11512 : checkPrefixCuts (2^48) 1512833025 9 Manual.Count131072.C011512.packed 128 cuts11512 = true := by
 decide +kernel
def pointBounds11512 : List (Nat × Nat × Nat) := [(1512834048,92774416502182,92774792010432),(1512882176,92774831218841,92775206727419),(1512930304,92775260434133,92775635943049)]
theorem point_links_checked11512 : (cuts11512.take 3).map (fun c => (1512833025-1+2*2^9*c.k,92774407757453+c.lower,92774783265696+c.upper)) = pointBounds11512 := by
 decide +kernel
def cuts11513 : List PrefixCut := [⟨14,130786911,130787013⟩,
⟨61,554951844,554952281⟩,
⟨108,978359208,978359978⟩,
⟨128,1151922531,1151923441⟩]
theorem checked11513 : checkPrefixCuts (2^48) 1512964097 9 Manual.Count131072.C011513.packed 128 cuts11513 = true := by
 decide +kernel
def pointBounds11513 : List (Nat × Nat × Nat) := [(1512978432,92775687589248,92776063098496),(1513026560,92776111754181,92776487263764),(1513074688,92776535161545,92776910671461)]
theorem point_links_checked11513 : (cuts11513.take 3).map (fun c => (1512964097-1+2*2^9*c.k,92775556802337+c.lower,92775932311483+c.upper)) = pointBounds11513 := by
 decide +kernel
def cuts11514 : List PrefixCut := [⟨27,250574575,250574769⟩,
⟨74,664654059,664654583⟩,
⟨121,1082254669,1082255524⟩,
⟨128,1148660310,1148661217⟩]
theorem checked11514 : checkPrefixCuts (2^48) 1513095169 9 Manual.Count131072.C011514.packed 128 cuts11514 = true := by
 decide +kernel
def pointBounds11514 : List (Nat × Nat × Nat) := [(1513122816,92776959299443,92777334809693),(1513170944,92777373378927,92777748889507),(1513219072,92777790979537,92778166490448)]
theorem point_links_checked11514 : (cuts11514.take 3).map (fun c => (1513095169-1+2*2^9*c.k,92776708724868+c.lower,92777084234924+c.upper)) = pointBounds11514 := by
 decide +kernel
def cuts11515 : List PrefixCut := [⟨40,358249948,358250234⟩,
⟨87,799074186,799074819⟩,
⟨128,1164370761,1164371683⟩]
theorem checked11515 : checkPrefixCuts (2^48) 1513226241 9 Manual.Count131072.C011515.packed 128 cuts11515 = true := by
 decide +kernel
def pointBounds11515 : List (Nat × Nat × Nat) := [(1513267200,92778215635126,92778591146375),(1513315328,92778656459364,92779031970960)]
theorem point_links_checked11515 : (cuts11515.take 2).map (fun c => (1513226241-1+2*2^9*c.k,92777857385178+c.lower,92778232896141+c.upper)) = pointBounds11515 := by
 decide +kernel
def cuts11516 : List PrefixCut := [⟨6,53380074,53380118⟩,
⟨53,468509534,468509904⟩,
⟨100,890693214,890693917⟩,
⟨128,1141579315,1141580218⟩]
theorem checked11516 : checkPrefixCuts (2^48) 1513357313 9 Manual.Count131072.C011516.packed 128 cuts11516 = true := by
 decide +kernel
def pointBounds11516 : List (Nat × Nat × Nat) := [(1513363456,92779075136013,92779450647942),(1513411584,92779490265473,92779865777728),(1513459712,92779912449153,92780287961741)]
theorem point_links_checked11516 : (cuts11516.take 3).map (fun c => (1513357313-1+2*2^9*c.k,92779021755939+c.lower,92779397267824+c.upper)) = pointBounds11516 := by
 decide +kernel
def cuts11517 : List PrefixCut := [⟨19,165518974,165519104⟩,
⟨66,583584503,583584960⟩,
⟨113,1012050861,1012051654⟩,
⟨128,1146687604,1146688502⟩]
theorem checked11517 : checkPrefixCuts (2^48) 1513488385 9 Manual.Count131072.C011517.packed 128 cuts11517 = true := by
 decide +kernel
def pointBounds11517 : List (Nat × Nat × Nat) := [(1513507840,92780328854228,92780704367146),(1513555968,92780746919757,92781122433002),(1513604096,92781175386115,92781550899696)]
theorem point_links_checked11517 : (cuts11517.take 3).map (fun c => (1513488385-1+2*2^9*c.k,92780163335254+c.lower,92780538848042+c.upper)) = pointBounds11517 := by
 decide +kernel
def cuts11518 : List PrefixCut := [⟨32,288423015,288423242⟩,
⟨79,704961018,704961572⟩,
⟨126,1119998077,1119998960⟩,
⟨128,1137291005,1137291902⟩]
theorem checked11518 : checkPrefixCuts (2^48) 1513619457 9 Manual.Count131072.C011518.packed 128 cuts11518 = true := by
 decide +kernel
def pointBounds11518 : List (Nat × Nat × Nat) := [(1513652224,92781598445873,92781973959786),(1513700352,92782014983876,92782390498116),(1513748480,92782430020935,92782805535504)]
theorem point_links_checked11518 : (cuts11518.take 3).map (fun c => (1513619457-1+2*2^9*c.k,92781310022858+c.lower,92781685536544+c.upper)) = pointBounds11518 := by
 decide +kernel
def cuts11519 : List PrefixCut := [⟨45,407957870,407958188⟩,
⟨92,839145187,839145847⟩,
⟨128,1161178527,1161179444⟩]
theorem checked11519 : checkPrefixCuts (2^48) 1513750529 9 Manual.Count131072.C011519.packed 128 cuts11519 = true := by
 decide +kernel
def pointBounds11519 : List (Nat × Nat × Nat) := [(1513796608,92782855271733,92783230786634),(1513844736,92783286459050,92783661974293)]
theorem point_links_checked11519 : (cuts11519.take 2).map (fun c => (1513750529-1+2*2^9*c.k,92782447313863+c.lower,92782822828446+c.upper)) = pointBounds11519 := by
 decide +kernel
def cuts11520 : List PrefixCut := [⟨11,96682859,96682937⟩,
⟨58,523752345,523752759⟩,
⟨105,949135090,949135835⟩,
⟨128,1156615786,1156616695⟩]
theorem checked11520 : checkPrefixCuts (2^48) 1513881601 9 Manual.Count131072.C011520.packed 128 cuts11520 = true := by
 decide +kernel
def pointBounds11520 : List (Nat × Nat × Nat) := [(1513892864,92783705175249,92784080690827),(1513940992,92784132244735,92784507760649),(1513989120,92784557627480,92784933143725)]
theorem point_links_checked11520 : (cuts11520.take 3).map (fun c => (1513881601-1+2*2^9*c.k,92783608492390+c.lower,92783984007890+c.upper)) = pointBounds11520 := by
 decide +kernel
def cuts11521 : List PrefixCut := [⟨24,209522433,209522599⟩,
⟨71,630602179,630602680⟩,
⟨118,1062078921,1062079763⟩,
⟨128,1148707235,1148708146⟩]
theorem checked11521 : checkPrefixCuts (2^48) 1514012673 9 Manual.Count131072.C011521.packed 128 cuts11521 = true := by
 decide +kernel
def pointBounds11521 : List (Nat × Nat × Nat) := [(1514037248,92784974630609,92785350147184),(1514085376,92785395710355,92785771227265),(1514133504,92785827187097,92786202704348)]
theorem point_links_checked11521 : (cuts11521.take 3).map (fun c => (1514012673-1+2*2^9*c.k,92784765108176+c.lower,92785140624585+c.upper)) = pointBounds11521 := by
 decide +kernel
def cuts11522 : List PrefixCut := [⟨37,334982288,334982553⟩,
⟨84,750631073,750631666⟩,
⟨128,1152325859,1152326772⟩]
theorem checked11522 : checkPrefixCuts (2^48) 1514143745 9 Manual.Count131072.C011522.packed 128 cuts11522 = true := by
 decide +kernel
def pointBounds11522 : List (Nat × Nat × Nat) := [(1514181632,92786248797699,92786624315284),(1514229760,92786664446484,92787039964397)]
theorem point_links_checked11522 : (cuts11522.take 2).map (fun c => (1514143745-1+2*2^9*c.k,92785913815411+c.lower,92786289332731+c.upper)) = pointBounds11522 := by
 decide +kernel
def cuts11523 : List PrefixCut := [⟨3,26766832,26766854⟩,
⟨50,452612441,452612797⟩,
⟨97,871753113,871753798⟩,
⟨128,1150181583,1150182487⟩]
theorem checked11523 : checkPrefixCuts (2^48) 1514274817 9 Manual.Count131072.C011523.packed 128 cuts11523 = true := by
 decide +kernel
def pointBounds11523 : List (Nat × Nat × Nat) := [(1514277888,92787092908102,92787468426357),(1514326016,92787518753711,92787894272300),(1514374144,92787937894383,92788313413301)]
theorem point_links_checked11523 : (cuts11523.take 3).map (fun c => (1514274817-1+2*2^9*c.k,92787066141270+c.lower,92787441659503+c.upper)) = pointBounds11523 := by
 decide +kernel
def cuts11524 : List PrefixCut := [⟨16,150178016,150178134⟩,
⟨63,577284094,577284550⟩,
⟨110,999544350,999545141⟩,
⟨128,1160490380,1160491297⟩]
theorem checked11524 : checkPrefixCuts (2^48) 1514405889 9 Manual.Count131072.C011524.packed 128 cuts11524 = true := by
 decide +kernel
def pointBounds11524 : List (Nat × Nat × Nat) := [(1514422272,92788366500869,92788742020124),(1514470400,92788793606947,92789169126540),(1514518528,92789215867203,92789591387131)]
theorem point_links_checked11524 : (cuts11524.take 3).map (fun c => (1514405889-1+2*2^9*c.k,92788216322853+c.lower,92788591841990+c.upper)) = pointBounds11524 := by
 decide +kernel
def cuts11525 : List PrefixCut := [⟨29,265203639,265203850⟩,
⟨76,691339830,691340374⟩,
⟨123,1120807433,1120808316⟩,
⟨128,1165779023,1165779941⟩]
theorem checked11525 : checkPrefixCuts (2^48) 1514536961 9 Manual.Count131072.C011525.packed 128 cuts11525 = true := by
 decide +kernel
def pointBounds11525 : List (Nat × Nat × Nat) := [(1514566656,92789642016872,92790017537137),(1514614784,92790068153063,92790443673661),(1514662912,92790497620666,92790873141603)]
theorem point_links_checked11525 : (cuts11525.take 3).map (fun c => (1514536961-1+2*2^9*c.k,92789376813233+c.lower,92789752333287+c.upper)) = pointBounds11525 := by
 decide +kernel
def cuts11526 : List PrefixCut := [⟨42,373146794,373147094⟩,
⟨89,812435819,812436462⟩,
⟨128,1157501858,1157502771⟩]
theorem checked11526 : checkPrefixCuts (2^48) 1514668033 9 Manual.Count131072.C011526.packed 128 cuts11526 = true := by
 decide +kernel
def pointBounds11526 : List (Nat × Nat × Nat) := [(1514711040,92790915739050,92791291260322),(1514759168,92791355028075,92791730549690)]
theorem point_links_checked11526 : (cuts11526.take 2).map (fun c => (1514668033-1+2*2^9*c.k,92790542592256+c.lower,92790918113228+c.upper)) = pointBounds11526 := by
 decide +kernel
def cuts11527 : List PrefixCut := [⟨8,71725035,71725093⟩,
⟨55,501881443,501881842⟩,
⟨102,915858992,915859716⟩,
⟨128,1155915410,1155916319⟩]
theorem checked11527 : checkPrefixCuts (2^48) 1514799105 9 Manual.Count131072.C011527.packed 128 cuts11527 = true := by
 decide +kernel
def pointBounds11527 : List (Nat × Nat × Nat) := [(1514807296,92791771819149,92792147341092),(1514855424,92792201975557,92792577497841),(1514903552,92792615953106,92792991475715)]
theorem point_links_checked11527 : (cuts11527.take 3).map (fun c => (1514799105-1+2*2^9*c.k,92791700094114+c.lower,92792075615999+c.upper)) = pointBounds11527 := by
 decide +kernel
def cuts11528 : List PrefixCut := [⟨21,196203975,196204130⟩,
⟨68,611827386,611827870⟩,
⟨115,1028366419,1028367229⟩,
⟨128,1140952302,1140953203⟩]
theorem checked11528 : checkPrefixCuts (2^48) 1514930177 9 Manual.Count131072.C011528.packed 128 cuts11528 = true := by
 decide +kernel
def pointBounds11528 : List (Nat × Nat × Nat) := [(1514951680,92793052213499,92793427736448),(1514999808,92793467836910,92793843360188),(1515047936,92793884375943,92794259899547)]
theorem point_links_checked11528 : (cuts11528.take 3).map (fun c => (1514930177-1+2*2^9*c.k,92792856009524+c.lower,92793231532318+c.upper)) = pointBounds11528 := by
 decide +kernel
def cuts11529 : List PrefixCut := [⟨34,308770288,308770526⟩,
⟨81,732528236,732528806⟩,
⟨128,1155158159,1155159059⟩]
theorem checked11529 : checkPrefixCuts (2^48) 1515061249 9 Manual.Count131072.C011529.packed 128 cuts11529 = true := by
 decide +kernel
def pointBounds11529 : List (Nat × Nat × Nat) := [(1515096064,92794305732114,92794681256047),(1515144192,92794729490062,92795105014327),(1515192320,92795152119985,92795527644580)]
theorem point_links_checked11529 : (cuts11529.take 3).map (fun c => (1515061249-1+2*2^9*c.k,92793996961826+c.lower,92794372485521+c.upper)) = pointBounds11529 := by
 decide +kernel
def cuts11530 : List PrefixCut := [⟨47,419272666,419272998⟩,
⟨94,845590828,845591492⟩,
⟨128,1153200180,1153201085⟩]
theorem checked11530 : checkPrefixCuts (2^48) 1515192321 9 Manual.Count131072.C011530.packed 128 cuts11530 = true := by
 decide +kernel
def pointBounds11530 : List (Nat × Nat × Nat) := [(1515240448,92795571392651,92795946917578),(1515288576,92795997710813,92796373236072)]
theorem point_links_checked11530 : (cuts11530.take 2).map (fun c => (1515192321-1+2*2^9*c.k,92795152119985+c.lower,92795527644580+c.upper)) = pointBounds11530 := by
 decide +kernel
def cuts11531 : List PrefixCut := [⟨13,117952234,117952326⟩,
⟨60,546100855,546101287⟩,
⟨107,965320249,965321012⟩,
⟨128,1146600168,1146601071⟩]
theorem checked11531 : checkPrefixCuts (2^48) 1515323393 9 Manual.Count131072.C011531.packed 128 cuts11531 = true := by
 decide +kernel
def pointBounds11531 : List (Nat × Nat × Nat) := [(1515336704,92796423272399,92796798797991),(1515384832,92796851421020,92797226946952),(1515432960,92797270640414,92797646166677)]
theorem point_links_checked11531 : (cuts11531.take 3).map (fun c => (1515323393-1+2*2^9*c.k,92796305320165+c.lower,92796680845665+c.upper)) = pointBounds11531 := by
 decide +kernel
def cuts11532 : List PrefixCut := [⟨26,231982577,231982758⟩,
⟨73,664547917,664548441⟩,
⟨120,1089856271,1089857130⟩,
⟨128,1159501542,1159502455⟩]
theorem checked11532 : checkPrefixCuts (2^48) 1515454465 9 Manual.Count131072.C011532.packed 128 cuts11532 = true := by
 decide +kernel
def pointBounds11532 : List (Nat × Nat × Nat) := [(1515481088,92797683902910,92798059429494),(1515529216,92798116468250,92798491995177),(1515577344,92798541776604,92798917303866)]
theorem point_links_checked11532 : (cuts11532.take 3).map (fun c => (1515454465-1+2*2^9*c.k,92797451920333+c.lower,92797827446736+c.upper)) = pointBounds11532 := by
 decide +kernel
def cuts11533 : List PrefixCut := [⟨39,358806696,358806977⟩,
⟨86,776102367,776102975⟩,
⟨128,1154758451,1154759359⟩]
theorem checked11533 : checkPrefixCuts (2^48) 1515585537 9 Manual.Count131072.C011533.packed 128 cuts11533 = true := by
 decide +kernel
def pointBounds11533 : List (Nat × Nat × Nat) := [(1515625472,92798970228571,92799345756168),(1515673600,92799387524242,92799763052166)]
theorem point_links_checked11533 : (cuts11533.take 2).map (fun c => (1515585537-1+2*2^9*c.k,92798611421875+c.lower,92798986949191+c.upper)) = pointBounds11533 := by
 decide +kernel
def cuts11534 : List PrefixCut := [⟨5,43826106,43826141⟩,
⟨52,468709047,468709420⟩,
⟨99,887450580,887451284⟩,
⟨128,1147230762,1147231671⟩]
theorem checked11534 : checkPrefixCuts (2^48) 1515716609 9 Manual.Count131072.C011534.packed 128 cuts11534 = true := by
 decide +kernel
def pointBounds11534 : List (Nat × Nat × Nat) := [(1515721728,92799810006432,92800185534691),(1515769856,92800234889373,92800610417970),(1515817984,92800653630906,92801029159834)]
theorem point_links_checked11534 : (cuts11534.take 3).map (fun c => (1515716609-1+2*2^9*c.k,92799766180326+c.lower,92800141708550+c.upper)) = pointBounds11534 := by
 decide +kernel
def cuts11535 : List PrefixCut := [⟨18,164518652,164518782⟩,
⟨65,585833110,585833570⟩,
⟨112,1001192618,1001193404⟩,
⟨128,1142861144,1142862041⟩]
theorem checked11535 : checkPrefixCuts (2^48) 1515847681 9 Manual.Count131072.C011535.packed 128 cuts11535 = true := by
 decide +kernel
def pointBounds11535 : List (Nat × Nat × Nat) := [(1515866112,92801077929740,92801453459003),(1515914240,92801499244198,92801874773791),(1515962368,92801914603706,92802290133625)]
theorem point_links_checked11535 : (cuts11535.take 3).map (fun c => (1515847681-1+2*2^9*c.k,92800913411088+c.lower,92801288940221+c.upper)) = pointBounds11535 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S2.B000047
