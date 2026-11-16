import PlattAssemblyKernel
import PlattCertificates.Count131072.C013296
import PlattCertificates.Count131072.C013297
import PlattCertificates.Count131072.C013298
import PlattCertificates.Count131072.C013299
import PlattCertificates.Count131072.C013300
import PlattCertificates.Count131072.C013301
import PlattCertificates.Count131072.C013302
import PlattCertificates.Count131072.C013303
import PlattCertificates.Count131072.C013304
import PlattCertificates.Count131072.C013305
import PlattCertificates.Count131072.C013306
import PlattCertificates.Count131072.C013307
import PlattCertificates.Count131072.C013308
import PlattCertificates.Count131072.C013309
import PlattCertificates.Count131072.C013310
import PlattCertificates.Count131072.C013311
import PlattCertificates.Count131072.C013312
import PlattCertificates.Count131072.C013313
import PlattCertificates.Count131072.C013314
import PlattCertificates.Count131072.C013315
import PlattCertificates.Count131072.C013316
import PlattCertificates.Count131072.C013317
import PlattCertificates.Count131072.C013318
import PlattCertificates.Count131072.C013319
import PlattCertificates.Count131072.C013320
import PlattCertificates.Count131072.C013321
import PlattCertificates.Count131072.C013322
import PlattCertificates.Count131072.C013323
import PlattCertificates.Count131072.C013324
import PlattCertificates.Count131072.C013325
import PlattCertificates.Count131072.C013326
import PlattCertificates.Count131072.C013327
namespace ChenEffective.PlattWindow.Assembly.Prefix.S2.B000103
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts13296 : List PrefixCut := [⟨50,390299264,390299541⟩,
⟨104,810236915,810237488⟩,
⟨128,996674608,996675316⟩]
theorem checked13296 : checkPrefixCuts (2^48) 1746665473 9 Manual.Count131072.C013296.packed 128 cuts13296 = true := by
 decide +kernel
def pointBounds13296 : List (Nat × Nat × Nat) := [(1746716672,94682183429927,94682560369401),(1746771968,94682603367578,94682980307348)]
theorem point_links_checked13296 : (cuts13296.take 2).map (fun c => (1746665473-1+2*2^9*c.k,94681793130663+c.lower,94682170069860+c.upper)) = pointBounds13296 := by
 decide +kernel
def cuts13297 : List PrefixCut := [⟨30,231552943,231553110⟩,
⟨84,646791162,646791633⟩,
⟨128,994665994,994666713⟩]
theorem checked13297 : checkPrefixCuts (2^48) 1746796545 9 Manual.Count131072.C013297.packed 128 cuts13297 = true := by
 decide +kernel
def pointBounds13297 : List (Nat × Nat × Nat) := [(1746827264,94683021358214,94683398298286),(1746882560,94683436596433,94683813536809)]
theorem point_links_checked13297 : (cuts13297.take 2).map (fun c => (1746796545-1+2*2^9*c.k,94682789805271+c.lower,94683166745176+c.upper)) = pointBounds13297 := by
 decide +kernel
def cuts13298 : List PrefixCut := [⟨10,73795336,73795388⟩,
⟨64,490618382,490618737⟩,
⟨118,903722605,903723257⟩,
⟨128,984118522,984119231⟩]
theorem checked13298 : checkPrefixCuts (2^48) 1746927617 9 Manual.Count131072.C013298.packed 128 cuts13298 = true := by
 decide +kernel
def pointBounds13298 : List (Nat × Nat × Nat) := [(1746937856,94683858266601,94684235207277),(1746993152,94684275089647,94684652030626),(1747048448,94684688193870,94685065135146)]
theorem point_links_checked13298 : (cuts13298.take 3).map (fun c => (1746927617-1+2*2^9*c.k,94683784471265+c.lower,94684161411889+c.upper)) = pointBounds13298 := by
 decide +kernel
def cuts13299 : List PrefixCut := [⟨44,332211956,332212196⟩,
⟨98,753828579,753829118⟩,
⟨128,987266723,987267426⟩]
theorem checked13299 : checkPrefixCuts (2^48) 1747058689 9 Manual.Count131072.C013299.packed 128 cuts13299 = true := by
 decide +kernel
def pointBounds13299 : List (Nat × Nat × Nat) := [(1747103744,94685100801743,94685477743316),(1747159040,94685522418366,94685899360238)]
theorem point_links_checked13299 : (cuts13299.take 2).map (fun c => (1747058689-1+2*2^9*c.k,94684768589787+c.lower,94685145531120+c.upper)) = pointBounds13299 := by
 decide +kernel
def cuts13300 : List PrefixCut := [⟨24,186554228,186554359⟩,
⟨78,605244573,605245003⟩,
⟨128,994603406,994604114⟩]
theorem checked13300 : checkPrefixCuts (2^48) 1747189761 9 Manual.Count131072.C013300.packed 128 cuts13300 = true := by
 decide +kernel
def pointBounds13300 : List (Nat × Nat × Nat) := [(1747214336,94685942410738,94686319352905),(1747269632,94686361101083,94686738043549)]
theorem point_links_checked13300 : (cuts13300.take 2).map (fun c => (1747189761-1+2*2^9*c.k,94685755856510+c.lower,94686132798546+c.upper)) = pointBounds13300 := by
 decide +kernel
def cuts13301 : List PrefixCut := [⟨4,26740808,26740830⟩,
⟨58,441216339,441216654⟩,
⟨112,853584680,853585289⟩,
⟨128,976809405,976810103⟩]
theorem checked13301 : checkPrefixCuts (2^48) 1747320833 9 Manual.Count131072.C013301.packed 128 cuts13301 = true := by
 decide +kernel
def pointBounds13301 : List (Nat × Nat × Nat) := [(1747324928,94686777200724,94687154143490),(1747380224,94687191676255,94687568619314),(1747435520,94687604044596,94687980987949)]
theorem point_links_checked13301 : (cuts13301.take 3).map (fun c => (1747320833-1+2*2^9*c.k,94686750459916+c.lower,94687127402660+c.upper)) = pointBounds13301 := by
 decide +kernel
def cuts13302 : List PrefixCut := [⟨38,295734649,295734862⟩,
⟨92,712425839,712426352⟩,
⟨128,985756461,985757168⟩]
theorem checked13302 : checkPrefixCuts (2^48) 1747451905 9 Manual.Count131072.C013302.packed 128 cuts13302 = true := by
 decide +kernel
def pointBounds13302 : List (Nat × Nat × Nat) := [(1747490816,94688023003970,94688399947625),(1747546112,94688439695160,94688816639115)]
theorem point_links_checked13302 : (cuts13302.take 2).map (fun c => (1747451905-1+2*2^9*c.k,94687727269321+c.lower,94688104212763+c.upper)) = pointBounds13302 := by
 decide +kernel
def cuts13303 : List PrefixCut := [⟨18,138032198,138032298⟩,
⟨72,557596082,557596484⟩,
⟨126,973925663,973926359⟩,
⟨128,990030989,990031696⟩]
theorem checked13303 : checkPrefixCuts (2^48) 1747582977 9 Manual.Count131072.C013303.packed 128 cuts13303 = true := by
 decide +kernel
def pointBounds13303 : List (Nat × Nat × Nat) := [(1747601408,94688851057980,94689228002229),(1747656704,94689270621864,94689647566415),(1747712000,94689686951445,94690063896290)]
theorem point_links_checked13303 : (cuts13303.take 3).map (fun c => (1747582977-1+2*2^9*c.k,94688713025782+c.lower,94689089969931+c.upper)) = pointBounds13303 := by
 decide +kernel
def cuts13304 : List PrefixCut := [⟨52,403593114,403593399⟩,
⟨106,826660223,826660810⟩,
⟨128,997203829,997204542⟩]
theorem checked13304 : checkPrefixCuts (2^48) 1747714049 9 Manual.Count131072.C013304.packed 128 cuts13304 = true := by
 decide +kernel
def pointBounds13304 : List (Nat × Nat × Nat) := [(1747767296,94690106649885,94690483595026),(1747822592,94690529716994,94690906662437)]
theorem point_links_checked13304 : (cuts13304.take 2).map (fun c => (1747714049-1+2*2^9*c.k,94689703056771+c.lower,94690080001627+c.upper)) = pointBounds13304 := by
 decide +kernel
def cuts13305 : List PrefixCut := [⟨32,245424308,245424480⟩,
⟨86,665404953,665405422⟩,
⟨128,994713345,994714048⟩]
theorem checked13305 : checkPrefixCuts (2^48) 1747845121 9 Manual.Count131072.C013305.packed 128 cuts13305 = true := by
 decide +kernel
def pointBounds13305 : List (Nat × Nat × Nat) := [(1747877888,94690945684908,94691322630649),(1747933184,94691365665553,94691742611591)]
theorem point_links_checked13305 : (cuts13305.take 2).map (fun c => (1747845121-1+2*2^9*c.k,94690700260600+c.lower,94691077206169+c.upper)) = pointBounds13305 := by
 decide +kernel
def cuts13306 : List PrefixCut := [⟨12,92591350,92591416⟩,
⟨66,498858166,498858524⟩,
⟨120,911392082,911392737⟩,
⟨128,971934590,971935288⟩]
theorem checked13306 : checkPrefixCuts (2^48) 1747976193 9 Manual.Count131072.C013306.packed 128 cuts13306 = true := by
 decide +kernel
def pointBounds13306 : List (Nat × Nat × Nat) := [(1747988480,94691787565295,94692164511633),(1748043776,94692193832111,94692570778741),(1748099072,94692606366027,94692983312954)]
theorem point_links_checked13306 : (cuts13306.take 3).map (fun c => (1747976193-1+2*2^9*c.k,94691694973945+c.lower,94692071920217+c.upper)) = pointBounds13306 := by
 decide +kernel
def cuts13307 : List PrefixCut := [⟨46,355359648,355359897⟩,
⟨100,765130261,765130804⟩,
⟨128,977175379,977176074⟩]
theorem checked13307 : checkPrefixCuts (2^48) 1748107265 9 Manual.Count131072.C013307.packed 128 cuts13307 = true := by
 decide +kernel
def pointBounds13307 : List (Nat × Nat × Nat) := [(1748154368,94693022268183,94693399215402),(1748209664,94693432038796,94693808986309)]
theorem point_links_checked13307 : (cuts13307.take 2).map (fun c => (1748107265-1+2*2^9*c.k,94692666908535+c.lower,94693043855505+c.upper)) = pointBounds13307 := by
 decide +kernel
def cuts13308 : List PrefixCut := [⟨26,204796604,204796752⟩,
⟨80,625167110,625167562⟩,
⟨128,997387771,997388490⟩]
theorem checked13308 : checkPrefixCuts (2^48) 1748238337 9 Manual.Count131072.C013308.packed 128 cuts13308 = true := by
 decide +kernel
def pointBounds13308 : List (Nat × Nat × Nat) := [(1748264960,94693848880518,94694225828331),(1748320256,94694269251024,94694646199141)]
theorem point_links_checked13308 : (cuts13308.take 2).map (fun c => (1748238337-1+2*2^9*c.k,94693644083914+c.lower,94694021031579+c.upper)) = pointBounds13308 := by
 decide +kernel
def cuts13309 : List PrefixCut := [⟨6,47009809,47009843⟩,
⟨60,464778028,464778356⟩,
⟨114,887845521,887846150⟩,
⟨128,996507957,996508662⟩]
theorem checked13309 : checkPrefixCuts (2^48) 1748369409 9 Manual.Count131072.C013309.packed 128 cuts13309 = true := by
 decide +kernel
def pointBounds13309 : List (Nat × Nat × Nat) := [(1748375552,94694688481494,94695065429912),(1748430848,94695106249713,94695483198425),(1748486144,94695529317206,94695906266219)]
theorem point_links_checked13309 : (cuts13309.take 3).map (fun c => (1748369409-1+2*2^9*c.k,94694641471685+c.lower,94695018420069+c.upper)) = pointBounds13309 := by
 decide +kernel
def cuts13310 : List PrefixCut := [⟨40,310206194,310206417⟩,
⟨94,731798191,731798709⟩,
⟨128,988223809,988224510⟩]
theorem checked13310 : checkPrefixCuts (2^48) 1748500481 9 Manual.Count131072.C013310.packed 128 cuts13310 = true := by
 decide +kernel
def pointBounds13310 : List (Nat × Nat × Nat) := [(1748541440,94695948185836,94696325135148),(1748596736,94696369777833,94696746727440)]
theorem point_links_checked13310 : (cuts13310.take 2).map (fun c => (1748500481-1+2*2^9*c.k,94695637979642+c.lower,94696014928731+c.upper)) = pointBounds13310 := by
 decide +kernel
def cuts13311 : List PrefixCut := [⟨20,158714169,158714283⟩,
⟨74,577382176,577382590⟩,
⟨128,993783534,993784247⟩]
theorem checked13311 : checkPrefixCuts (2^48) 1748631553 9 Manual.Count131072.C013311.packed 128 cuts13311 = true := by
 decide +kernel
def pointBounds13311 : List (Nat × Nat × Nat) := [(1748652032,94696784917620,94697161867524),(1748707328,94697203585627,94697580535831),(1748762624,94697619986985,94697996937488)]
theorem point_links_checked13311 : (cuts13311.take 3).map (fun c => (1748631553-1+2*2^9*c.k,94696626203451+c.lower,94697003153241+c.upper)) = pointBounds13311 := by
 decide +kernel
def cuts13312 : List PrefixCut := [⟨54,415422407,415422701⟩,
⟨108,837108634,837109228⟩,
⟨128,985500370,985501070⟩]
theorem checked13312 : checkPrefixCuts (2^48) 1748762625 9 Manual.Count131072.C013312.packed 128 cuts13312 = true := by
 decide +kernel
def pointBounds13312 : List (Nat × Nat × Nat) := [(1748817920,94698035409392,94698412360189),(1748873216,94698457095619,94698834046716)]
theorem point_links_checked13312 : (cuts13312.take 2).map (fun c => (1748762625-1+2*2^9*c.k,94697619986985+c.lower,94697996937488+c.upper)) = pointBounds13312 := by
 decide +kernel
def cuts13313 : List PrefixCut := [⟨34,267969989,267970178⟩,
⟨88,687376425,687376912⟩,
⟨128,992507936,992508643⟩]
theorem checked13313 : checkPrefixCuts (2^48) 1748893697 9 Manual.Count131072.C013313.packed 128 cuts13313 = true := by
 decide +kernel
def pointBounds13313 : List (Nat × Nat × Nat) := [(1748928512,94698873457344,94699250408736),(1748983808,94699292863780,94699669815470)]
theorem point_links_checked13313 : (cuts13313.take 2).map (fun c => (1748893697-1+2*2^9*c.k,94698605487355+c.lower,94698982438558+c.upper)) = pointBounds13313 := by
 decide +kernel
def cuts13314 : List PrefixCut := [⟨14,112652280,112652360⟩,
⟨68,541527011,541527390⟩,
⟨122,962020177,962020858⟩,
⟨128,1007238895,1007239608⟩]
theorem checked13314 : checkPrefixCuts (2^48) 1749024769 9 Manual.Count131072.C013314.packed 128 cuts13314 = true := by
 decide +kernel
def pointBounds13314 : List (Nat × Nat × Nat) := [(1749039104,94699710647571,94700087599561),(1749094400,94700139522302,94700516474591),(1749149696,94700560015468,94700936968059)]
theorem point_links_checked13314 : (cuts13314.take 3).map (fun c => (1749024769-1+2*2^9*c.k,94699597995291+c.lower,94699974947201+c.upper)) = pointBounds13314 := by
 decide +kernel
def cuts13315 : List PrefixCut := [⟨48,376226601,376226871⟩,
⟨102,794440371,794440942⟩,
⟨128,997830053,997830767⟩]
theorem checked13315 : checkPrefixCuts (2^48) 1749155841 9 Manual.Count131072.C013315.packed 128 cuts13315 = true := by
 decide +kernel
def pointBounds13315 : List (Nat × Nat × Nat) := [(1749204992,94700981460787,94701358413680),(1749260288,94701399674557,94701776627751)]
theorem point_links_checked13315 : (cuts13315.take 2).map (fun c => (1749155841-1+2*2^9*c.k,94700605234186+c.lower,94700982186809+c.upper)) = pointBounds13315 := by
 decide +kernel
def cuts13316 : List PrefixCut := [⟨28,217385427,217385578⟩,
⟨82,626562153,626562597⟩,
⟨128,981825929,981826624⟩]
theorem checked13316 : checkPrefixCuts (2^48) 1749286913 9 Manual.Count131072.C013316.packed 128 cuts13316 = true := by
 decide +kernel
def pointBounds13316 : List (Nat × Nat × Nat) := [(1749315584,94701820449666,94702197403154),(1749370880,94702229626392,94702606580173)]
theorem point_links_checked13316 : (cuts13316.take 2).map (fun c => (1749286913-1+2*2^9*c.k,94701603064239+c.lower,94701980017576+c.upper)) = pointBounds13316 := by
 decide +kernel
def cuts13317 : List PrefixCut := [⟨8,60979551,60979595⟩,
⟨62,483162846,483163189⟩,
⟨116,902436817,902437456⟩,
⟨128,995106457,995107162⟩]
theorem checked13317 : checkPrefixCuts (2^48) 1749417985 9 Manual.Count131072.C013317.packed 128 cuts13317 = true := by
 decide +kernel
def pointBounds13317 : List (Nat × Nat × Nat) := [(1749426176,94702645869719,94703022823795),(1749481472,94703068053014,94703445007389),(1749536768,94703487326985,94703864281656)]
theorem point_links_checked13317 : (cuts13317.take 3).map (fun c => (1749417985-1+2*2^9*c.k,94702584890168+c.lower,94702961844200+c.upper)) = pointBounds13317 := by
 decide +kernel
def cuts13318 : List PrefixCut := [⟨42,326430179,326430413⟩,
⟨96,738438194,738438725⟩,
⟨128,991975117,991975830⟩]
theorem checked13318 : checkPrefixCuts (2^48) 1749549057 9 Manual.Count131072.C013318.packed 128 cuts13318 = true := by
 decide +kernel
def pointBounds13318 : List (Nat × Nat × Nat) := [(1749592064,94703906426804,94704283381775),(1749647360,94704318434819,94704695390087)]
theorem point_links_checked13318 : (cuts13318.take 2).map (fun c => (1749549057-1+2*2^9*c.k,94703579996625+c.lower,94703956951362+c.upper)) = pointBounds13318 := by
 decide +kernel
def cuts13319 : List PrefixCut := [⟨22,176958266,176958393⟩,
⟨76,590870597,590871023⟩,
⟨128,987557772,987558487⟩]
theorem checked13319 : checkPrefixCuts (2^48) 1749680129 9 Manual.Count131072.C013319.packed 128 cuts13319 = true := by
 decide +kernel
def pointBounds13319 : List (Nat × Nat × Nat) := [(1749702656,94704748930008,94705125885585),(1749757952,94705162842339,94705539798215)]
theorem point_links_checked13319 : (cuts13319.take 2).map (fun c => (1749680129-1+2*2^9*c.k,94704571971742+c.lower,94704948927192+c.upper)) = pointBounds13319 := by
 decide +kernel
def cuts13320 : List PrefixCut := [⟨2,13029664,13029673⟩,
⟨56,442036313,442036630⟩,
⟨110,861056613,861057231⟩,
⟨128,997617356,997618073⟩]
theorem checked13320 : checkPrefixCuts (2^48) 1749811201 9 Manual.Count131072.C013320.packed 128 cuts13320 = true := by
 decide +kernel
def pointBounds13320 : List (Nat × Nat × Nat) := [(1749813248,94705572559178,94705949515352),(1749868544,94706001565827,94706378522309),(1749923840,94706420586127,94706797542910)]
theorem point_links_checked13320 : (cuts13320.take 3).map (fun c => (1749811201-1+2*2^9*c.k,94705559529514+c.lower,94705936485679+c.upper)) = pointBounds13320 := by
 decide +kernel
def cuts13321 : List PrefixCut := [⟨36,282767944,282768143⟩,
⟨90,694684796,694685290⟩,
⟨128,989822263,989822968⟩]
theorem checked13321 : checkPrefixCuts (2^48) 1749942273 9 Manual.Count131072.C013321.packed 128 cuts13321 = true := by
 decide +kernel
def pointBounds13321 : List (Nat × Nat × Nat) := [(1749979136,94706839914814,94707216871895),(1750034432,94707251831666,94707628789042)]
theorem point_links_checked13321 : (cuts13321.take 2).map (fun c => (1749942273-1+2*2^9*c.k,94706557146870+c.lower,94706934103752+c.upper)) = pointBounds13321 := by
 decide +kernel
def cuts13322 : List PrefixCut := [⟨16,120948127,120948213⟩,
⟨70,535412267,535412648⟩,
⟨124,963372721,963373401⟩,
⟨128,994090142,994090843⟩]
theorem checked13322 : checkPrefixCuts (2^48) 1750073345 9 Manual.Count131072.C013322.packed 128 cuts13322 = true := by
 decide +kernel
def pointBounds13322 : List (Nat × Nat × Nat) := [(1750089728,94707667917260,94708044874933),(1750145024,94708082381400,94708459339368),(1750200320,94708510341854,94708887300121)]
theorem point_links_checked13322 : (cuts13322.take 3).map (fun c => (1750073345-1+2*2^9*c.k,94707546969133+c.lower,94707923926720+c.upper)) = pointBounds13322 := by
 decide +kernel
def cuts13323 : List PrefixCut := [⟨50,386293533,386293807⟩,
⟨104,807955018,807955592⟩,
⟨128,990960318,990961022⟩]
theorem checked13323 : checkPrefixCuts (2^48) 1750204417 9 Manual.Count131072.C013323.packed 128 cuts13323 = true := by
 decide +kernel
def pointBounds13323 : List (Nat × Nat × Nat) := [(1750255616,94708927352808,94709304311370),(1750310912,94709349014293,94709725973155)]
theorem point_links_checked13323 : (cuts13323.take 2).map (fun c => (1750204417-1+2*2^9*c.k,94708541059275+c.lower,94708918017563+c.upper)) = pointBounds13323 := by
 decide +kernel
def cuts13324 : List PrefixCut := [⟨30,229959052,229959217⟩,
⟨84,649825114,649825580⟩,
⟨128,987670139,987670846⟩]
theorem checked13324 : checkPrefixCuts (2^48) 1750335489 9 Manual.Count131072.C013324.packed 128 cuts13324 = true := by
 decide +kernel
def pointBounds13324 : List (Nat × Nat × Nat) := [(1750366208,94709761978645,94710138937802),(1750421504,94710181844707,94710558804165)]
theorem point_links_checked13324 : (cuts13324.take 2).map (fun c => (1750335489-1+2*2^9*c.k,94709532019593+c.lower,94709908978585+c.upper)) = pointBounds13324 := by
 decide +kernel
def cuts13325 : List PrefixCut := [⟨10,78791731,78791787⟩,
⟨64,496380088,496380438⟩,
⟨118,913794445,913795093⟩,
⟨128,992580732,992581438⟩]
theorem checked13325 : checkPrefixCuts (2^48) 1750466561 9 Manual.Count131072.C013325.packed 128 cuts13325 = true := by
 decide +kernel
def pointBounds13325 : List (Nat × Nat × Nat) := [(1750476800,94710598481463,94710975441218),(1750532096,94711016069820,94711393029869),(1750587392,94711433484177,94711810444524)]
theorem point_links_checked13325 : (cuts13325.take 3).map (fun c => (1750466561-1+2*2^9*c.k,94710519689732+c.lower,94710896649431+c.upper)) = pointBounds13325 := by
 decide +kernel
def cuts13326 : List PrefixCut := [⟨44,342473693,342473937⟩,
⟨98,750053960,750054494⟩,
⟨128,982216296,982216997⟩]
theorem checked13326 : checkPrefixCuts (2^48) 1750597633 9 Manual.Count131072.C013326.packed 128 cuts13326 = true := by
 decide +kernel
def pointBounds13326 : List (Nat × Nat × Nat) := [(1750642688,94711854744157,94712231704806),(1750697984,94712262324424,94712639285363)]
theorem point_links_checked13326 : (cuts13326.take 2).map (fun c => (1750597633-1+2*2^9*c.k,94711512270464+c.lower,94711889230869+c.upper)) = pointBounds13326 := by
 decide +kernel
def cuts13327 : List PrefixCut := [⟨24,184569355,184569488⟩,
⟨78,605146408,605146841⟩,
⟨128,996611900,996612614⟩]
theorem checked13327 : checkPrefixCuts (2^48) 1750728705 9 Manual.Count131072.C013327.packed 128 cuts13327 = true := by
 decide +kernel
def pointBounds13327 : List (Nat × Nat × Nat) := [(1750753280,94712679056115,94713056017354),(1750808576,94713099633168,94713476594707)]
theorem point_links_checked13327 : (cuts13327.take 2).map (fun c => (1750728705-1+2*2^9*c.k,94712494486760+c.lower,94712871447866+c.upper)) = pointBounds13327 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S2.B000103
