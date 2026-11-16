import PlattAssemblyKernel
import PlattCertificates.Count131072.C023296
import PlattCertificates.Count131072.C023297
import PlattCertificates.Count131072.C023298
import PlattCertificates.Count131072.C023299
import PlattCertificates.Count131072.C023300
import PlattCertificates.Count131072.C023301
import PlattCertificates.Count131072.C023302
import PlattCertificates.Count131072.C023303
import PlattCertificates.Count131072.C023304
import PlattCertificates.Count131072.C023305
import PlattCertificates.Count131072.C023306
import PlattCertificates.Count131072.C023307
import PlattCertificates.Count131072.C023308
import PlattCertificates.Count131072.C023309
import PlattCertificates.Count131072.C023310
import PlattCertificates.Count131072.C023311
import PlattCertificates.Count131072.C023312
import PlattCertificates.Count131072.C023313
import PlattCertificates.Count131072.C023314
import PlattCertificates.Count131072.C023315
import PlattCertificates.Count131072.C023316
import PlattCertificates.Count131072.C023317
import PlattCertificates.Count131072.C023318
import PlattCertificates.Count131072.C023319
import PlattCertificates.Count131072.C023320
import PlattCertificates.Count131072.C023321
import PlattCertificates.Count131072.C023322
import PlattCertificates.Count131072.C023323
import PlattCertificates.Count131072.C023324
import PlattCertificates.Count131072.C023325
import PlattCertificates.Count131072.C023326
import PlattCertificates.Count131072.C023327
namespace ChenEffective.PlattWindow.Assembly.Prefix.S3.B000103
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts23296 : List PrefixCut := [⟨42,182837663,182837768⟩,
⟨128,549886053,549886368⟩]
theorem checked23296 : checkPrefixCuts (2^48) 3057385473 9 Manual.Count131072.C023296.packed 128 cuts23296 = true := by
 decide +kernel
def pointBounds23296 : List (Nat × Nat × Nat) := [(3057428480,101991054860709,101991436365597)]
theorem point_links_checked23296 : (cuts23296.take 1).map (fun c => (3057385473-1+2*2^9*c.k,101990872023046+c.lower,101991253527829+c.upper)) = pointBounds23296 := by
 decide +kernel
def cuts23297 : List PrefixCut := [⟨8,36179520,36179542⟩,
⟨102,437001296,437001544⟩,
⟨128,547653125,547653434⟩]
theorem checked23297 : checkPrefixCuts (2^48) 3057516545 9 Manual.Count131072.C023297.packed 128 cuts23297 = true := by
 decide +kernel
def pointBounds23297 : List (Nat × Nat × Nat) := [(3057524736,101991458088619,101991839593739),(3057620992,101991858910395,101992240415741)]
theorem point_links_checked23297 : (cuts23297.take 2).map (fun c => (3057516545-1+2*2^9*c.k,101991421909099+c.lower,101991803414197+c.upper)) = pointBounds23297 := by
 decide +kernel
def cuts23298 : List PrefixCut := [⟨68,294207734,294207899⟩,
⟨128,553244916,553245225⟩]
theorem checked23298 : checkPrefixCuts (2^48) 3057647617 9 Manual.Count131072.C023298.packed 128 cuts23298 = true := by
 decide +kernel
def pointBounds23298 : List (Nat × Nat × Nat) := [(3057717248,101992263769958,101992645275530)]
theorem point_links_checked23298 : (cuts23298.take 1).map (fun c => (3057647617-1+2*2^9*c.k,101991969562224+c.lower,101992351067631+c.upper)) = pointBounds23298 := by
 decide +kernel
def cuts23299 : List PrefixCut := [⟨34,148479151,148479238⟩,
⟨128,551748326,551748640⟩]
theorem checked23299 : checkPrefixCuts (2^48) 3057778689 9 Manual.Count131072.C023299.packed 128 cuts23299 = true := by
 decide +kernel
def pointBounds23299 : List (Nat × Nat × Nat) := [(3057813504,101992671286291,101993052792094),(3057909760,101993074555466,101993456061496)]
theorem point_links_checked23299 : (cuts23299.take 2).map (fun c => (3057778689-1+2*2^9*c.k,101992522807140+c.lower,101992904312856+c.upper)) = pointBounds23299 := by
 decide +kernel
def cuts23300 : List PrefixCut := [⟨94,400771332,400771558⟩,
⟨128,549331496,549331805⟩]
theorem checked23300 : checkPrefixCuts (2^48) 3057909761 9 Manual.Count131072.C023300.packed 128 cuts23300 = true := by
 decide +kernel
def pointBounds23300 : List (Nat × Nat × Nat) := [(3058006016,101993475326798,101993856833054)]
theorem point_links_checked23300 : (cuts23300.take 1).map (fun c => (3057909761-1+2*2^9*c.k,101993074555466+c.lower,101993456061496+c.upper)) = pointBounds23300 := by
 decide +kernel
def cuts23301 : List PrefixCut := [⟨60,264348268,264348417⟩,
⟨128,554278334,554278653⟩]
theorem checked23301 : checkPrefixCuts (2^48) 3058040833 9 Manual.Count131072.C023301.packed 128 cuts23301 = true := by
 decide +kernel
def pointBounds23301 : List (Nat × Nat × Nat) := [(3058102272,101993888235230,101994269741718)]
theorem point_links_checked23301 : (cuts23301.take 1).map (fun c => (3058040833-1+2*2^9*c.k,101993623886962+c.lower,101994005393301+c.upper)) = pointBounds23301 := by
 decide +kernel
def cuts23302 : List PrefixCut := [⟨26,114129417,114129486⟩,
⟨120,515783251,515783545⟩,
⟨128,549468581,549468898⟩]
theorem checked23302 : checkPrefixCuts (2^48) 3058171905 9 Manual.Count131072.C023302.packed 128 cuts23302 = true := by
 decide +kernel
def pointBounds23302 : List (Nat × Nat × Nat) := [(3058198528,101994292294713,101994673801440),(3058294784,101994693948547,101995075455499)]
theorem point_links_checked23302 : (cuts23302.take 2).map (fun c => (3058171905-1+2*2^9*c.k,101994178165296+c.lower,101994559671954+c.upper)) = pointBounds23302 := by
 decide +kernel
def cuts23303 : List PrefixCut := [⟨86,372557576,372557785⟩,
⟨128,551929904,551930215⟩]
theorem checked23303 : checkPrefixCuts (2^48) 3058302977 9 Manual.Count131072.C023303.packed 128 cuts23303 = true := by
 decide +kernel
def pointBounds23303 : List (Nat × Nat × Nat) := [(3058391040,101995100191453,101995481698637)]
theorem point_links_checked23303 : (cuts23303.take 1).map (fun c => (3058302977-1+2*2^9*c.k,101994727633877+c.lower,101995109140852+c.upper)) = pointBounds23303 := by
 decide +kernel
def cuts23304 : List PrefixCut := [⟨52,224004817,224004948⟩,
⟨128,550617800,550618116⟩]
theorem checked23304 : checkPrefixCuts (2^48) 3058434049 9 Manual.Count131072.C023304.packed 128 cuts23304 = true := by
 decide +kernel
def pointBounds23304 : List (Nat × Nat × Nat) := [(3058487296,101995503568598,101995885076015)]
theorem point_links_checked23304 : (cuts23304.take 1).map (fun c => (3058434049-1+2*2^9*c.k,101995279563781+c.lower,101995661071067+c.upper)) = pointBounds23304 := by
 decide +kernel
def cuts23305 : List PrefixCut := [⟨18,78131888,78131932⟩,
⟨112,475501954,475502221⟩,
⟨128,545348717,545349022⟩]
theorem checked23305 : checkPrefixCuts (2^48) 3058565121 9 Manual.Count131072.C023305.packed 128 cuts23305 = true := by
 decide +kernel
def pointBounds23305 : List (Nat × Nat × Nat) := [(3058583552,101995908313469,101996289821115),(3058679808,101996305683535,101996687191404)]
theorem point_links_checked23305 : (cuts23305.take 2).map (fun c => (3058565121-1+2*2^9*c.k,101995830181581+c.lower,101996211689183+c.upper)) = pointBounds23305 := by
 decide +kernel
def cuts23306 : List PrefixCut := [⟨78,339013756,339013947⟩,
⟨128,554619647,554619960⟩]
theorem checked23306 : checkPrefixCuts (2^48) 3058696193 9 Manual.Count131072.C023306.packed 128 cuts23306 = true := by
 decide +kernel
def pointBounds23306 : List (Nat × Nat × Nat) := [(3058776064,101996714544054,101997096052152)]
theorem point_links_checked23306 : (cuts23306.take 1).map (fun c => (3058696193-1+2*2^9*c.k,101996375530298+c.lower,101996757038205+c.upper)) = pointBounds23306 := by
 decide +kernel
def cuts23307 : List PrefixCut := [⟨44,189652927,189653034⟩,
⟨128,553859710,553860022⟩]
theorem checked23307 : checkPrefixCuts (2^48) 3058827265 9 Manual.Count131072.C023307.packed 128 cuts23307 = true := by
 decide +kernel
def pointBounds23307 : List (Nat × Nat × Nat) := [(3058872320,101997119802872,101997501311199)]
theorem point_links_checked23307 : (cuts23307.take 1).map (fun c => (3058827265-1+2*2^9*c.k,101996930149945+c.lower,101997311658165+c.upper)) = pointBounds23307 := by
 decide +kernel
def cuts23308 : List PrefixCut := [⟨10,44627969,44627995⟩,
⟨104,452989748,452990008⟩,
⟨128,558804709,558805031⟩]
theorem checked23308 : checkPrefixCuts (2^48) 3058958337 9 Manual.Count131072.C023308.packed 128 cuts23308 = true := by
 decide +kernel
def pointBounds23308 : List (Nat × Nat × Nat) := [(3058968576,101997528637624,101997910146182),(3059064832,101997936999403,101998318508195)]
theorem point_links_checked23308 : (cuts23308.take 2).map (fun c => (3058958337-1+2*2^9*c.k,101997484009655+c.lower,101997865518187+c.upper)) = pointBounds23308 := by
 decide +kernel
def cuts23309 : List PrefixCut := [⟨70,298393551,298393723⟩,
⟨128,545255313,545255625⟩]
theorem checked23309 : checkPrefixCuts (2^48) 3059089409 9 Manual.Count131072.C023309.packed 128 cuts23309 = true := by
 decide +kernel
def pointBounds23309 : List (Nat × Nat × Nat) := [(3059161088,101998341207915,101998722716941)]
theorem point_links_checked23309 : (cuts23309.take 1).map (fun c => (3059089409-1+2*2^9*c.k,101998042814364+c.lower,101998424323218+c.upper)) = pointBounds23309 := by
 decide +kernel
def cuts23310 : List PrefixCut := [⟨36,155217742,155217827⟩,
⟨128,555352592,555352902⟩]
theorem checked23310 : checkPrefixCuts (2^48) 3059220481 9 Manual.Count131072.C023310.packed 128 cuts23310 = true := by
 decide +kernel
def pointBounds23310 : List (Nat × Nat × Nat) := [(3059257344,101998743287419,101999124796670)]
theorem point_links_checked23310 : (cuts23310.take 1).map (fun c => (3059220481-1+2*2^9*c.k,101998588069677+c.lower,101998969578843+c.upper)) = pointBounds23310 := by
 decide +kernel
def cuts23311 : List PrefixCut := [⟨2,9108468,9108474⟩,
⟨96,415762870,415763107⟩,
⟨128,551924800,551925113⟩]
theorem checked23311 : checkPrefixCuts (2^48) 3059351553 9 Manual.Count131072.C023311.packed 128 cuts23311 = true := by
 decide +kernel
def pointBounds23311 : List (Nat × Nat × Nat) := [(3059353600,101999152530737,101999534040219),(3059449856,101999559185139,101999940694852)]
theorem point_links_checked23311 : (cuts23311.take 2).map (fun c => (3059351553-1+2*2^9*c.k,101999143422269+c.lower,101999524931745+c.upper)) = pointBounds23311 := by
 decide +kernel
def cuts23312 : List PrefixCut := [⟨62,276459577,276459740⟩,
⟨128,558709115,558709443⟩]
theorem checked23312 : checkPrefixCuts (2^48) 3059482625 9 Manual.Count131072.C023312.packed 128 cuts23312 = true := by
 decide +kernel
def pointBounds23312 : List (Nat × Nat × Nat) := [(3059546112,101999971806646,102000353316598)]
theorem point_links_checked23312 : (cuts23312.take 1).map (fun c => (3059482625-1+2*2^9*c.k,101999695347069+c.lower,102000076856858+c.upper)) = pointBounds23312 := by
 decide +kernel
def cuts23313 : List PrefixCut := [⟨28,119319392,119319464⟩,
⟨122,526579359,526579667⟩,
⟨128,552429399,552429722⟩]
theorem checked23313 : checkPrefixCuts (2^48) 3059613697 9 Manual.Count131072.C023313.packed 128 cuts23313 = true := by
 decide +kernel
def pointBounds23313 : List (Nat × Nat × Nat) := [(3059642368,102000373375576,102000754885765),(3059738624,102000780635543,102001162145968)]
theorem point_links_checked23313 : (cuts23313.take 2).map (fun c => (3059613697-1+2*2^9*c.k,102000254056184+c.lower,102000635566301+c.upper)) = pointBounds23313 := by
 decide +kernel
def cuts23314 : List PrefixCut := [⟨88,378637263,378637478⟩,
⟨128,550197879,550198193⟩]
theorem checked23314 : checkPrefixCuts (2^48) 3059744769 9 Manual.Count131072.C023314.packed 128 cuts23314 = true := by
 decide +kernel
def pointBounds23314 : List (Nat × Nat × Nat) := [(3059834880,102001185122846,102001566633501)]
theorem point_links_checked23314 : (cuts23314.take 1).map (fun c => (3059744769-1+2*2^9*c.k,102000806485583+c.lower,102001187996023+c.upper)) = pointBounds23314 := by
 decide +kernel
def cuts23315 : List PrefixCut := [⟨54,233097989,233098119⟩,
⟨128,551278206,551278520⟩]
theorem checked23315 : checkPrefixCuts (2^48) 3059875841 9 Manual.Count131072.C023315.packed 128 cuts23315 = true := by
 decide +kernel
def pointBounds23315 : List (Nat × Nat × Nat) := [(3059931136,102001589781451,102001971292335)]
theorem point_links_checked23315 : (cuts23315.take 1).map (fun c => (3059875841-1+2*2^9*c.k,102001356683462+c.lower,102001738194216+c.upper)) = pointBounds23315 := by
 decide +kernel
def cuts23316 : List PrefixCut := [⟨20,84258020,84258064⟩,
⟨114,492570572,492570853⟩,
⟨128,555393818,555394135⟩]
theorem checked23316 : checkPrefixCuts (2^48) 3060006913 9 Manual.Count131072.C023316.packed 128 cuts23316 = true := by
 decide +kernel
def pointBounds23316 : List (Nat × Nat × Nat) := [(3060027392,102001992219688,102002373730800),(3060123648,102002400532240,102002782043589)]
theorem point_links_checked23316 : (cuts23316.take 2).map (fun c => (3060006913-1+2*2^9*c.k,102001907961668+c.lower,102002289472736+c.upper)) = pointBounds23316 := by
 decide +kernel
def cuts23317 : List PrefixCut := [⟨80,343636851,343637041⟩,
⟨128,543320915,543321224⟩]
theorem checked23317 : checkPrefixCuts (2^48) 3060137985 9 Manual.Count131072.C023317.packed 128 cuts23317 = true := by
 decide +kernel
def pointBounds23317 : List (Nat × Nat × Nat) := [(3060219904,102002806992337,102003188503912)]
theorem point_links_checked23317 : (cuts23317.take 1).map (fun c => (3060137985-1+2*2^9*c.k,102002463355486+c.lower,102002844866871+c.upper)) = pointBounds23317 := by
 decide +kernel
def cuts23318 : List PrefixCut := [⟨46,198945085,198945196⟩,
⟨128,549551857,549552168⟩]
theorem checked23318 : checkPrefixCuts (2^48) 3060269057 9 Manual.Count131072.C023318.packed 128 cuts23318 = true := by
 decide +kernel
def pointBounds23318 : List (Nat × Nat × Nat) := [(3060316160,102003205621486,102003587133291)]
theorem point_links_checked23318 : (cuts23318.take 1).map (fun c => (3060269057-1+2*2^9*c.k,102003006676401+c.lower,102003388188095+c.upper)) = pointBounds23318 := by
 decide +kernel
def cuts23319 : List PrefixCut := [⟨12,50217287,50217314⟩,
⟨106,454523655,454523908⟩,
⟨128,548884494,548884800⟩]
theorem checked23319 : checkPrefixCuts (2^48) 3060400129 9 Manual.Count131072.C023319.packed 128 cuts23319 = true := by
 decide +kernel
def pointBounds23319 : List (Nat × Nat × Nat) := [(3060412416,102003606445545,102003987957577),(3060508672,102004010751913,102004392264171)]
theorem point_links_checked23319 : (cuts23319.take 2).map (fun c => (3060400129-1+2*2^9*c.k,102003556228258+c.lower,102003937740263+c.upper)) = pointBounds23319 := by
 decide +kernel
def cuts23320 : List PrefixCut := [⟨72,311680179,311680351⟩,
⟨128,552355777,552356084⟩]
theorem checked23320 : checkPrefixCuts (2^48) 3060531201 9 Manual.Count131072.C023320.packed 128 cuts23320 = true := by
 decide +kernel
def pointBounds23320 : List (Nat × Nat × Nat) := [(3060604928,102004416792931,102004798305414)]
theorem point_links_checked23320 : (cuts23320.take 1).map (fun c => (3060531201-1+2*2^9*c.k,102004105112752+c.lower,102004486625063+c.upper)) = pointBounds23320 := by
 decide +kernel
def cuts23321 : List PrefixCut := [⟨38,167559808,167559901⟩,
⟨128,559229368,559229682⟩]
theorem checked23321 : checkPrefixCuts (2^48) 3060662273 9 Manual.Count131072.C023321.packed 128 cuts23321 = true := by
 decide +kernel
def pointBounds23321 : List (Nat × Nat × Nat) := [(3060701184,102004825028337,102005206541048)]
theorem point_links_checked23321 : (cuts23321.take 1).map (fun c => (3060662273-1+2*2^9*c.k,102004657468529+c.lower,102005038981147+c.upper)) = pointBounds23321 := by
 decide +kernel
def cuts23322 : List PrefixCut := [⟨4,19127962,19127974⟩,
⟨98,420716553,420716793⟩,
⟨128,549457674,549457990⟩]
theorem checked23322 : checkPrefixCuts (2^48) 3060793345 9 Manual.Count131072.C023322.packed 128 cuts23322 = true := by
 decide +kernel
def pointBounds23322 : List (Nat × Nat × Nat) := [(3060797440,102005235825859,102005617338803),(3060893696,102005637414450,102006018927622)]
theorem point_links_checked23322 : (cuts23322.take 2).map (fun c => (3060793345-1+2*2^9*c.k,102005216697897+c.lower,102005598210829+c.upper)) = pointBounds23322 := by
 decide +kernel
def cuts23323 : List PrefixCut := [⟨64,273662522,273662682⟩,
⟨128,548790537,548790850⟩]
theorem checked23323 : checkPrefixCuts (2^48) 3060924417 9 Manual.Count131072.C023323.packed 128 cuts23323 = true := by
 decide +kernel
def pointBounds23323 : List (Nat × Nat × Nat) := [(3060989952,102006039818093,102006421331501)]
theorem point_links_checked23323 : (cuts23323.take 1).map (fun c => (3060924417-1+2*2^9*c.k,102005766155571+c.lower,102006147668819+c.upper)) = pointBounds23323 := by
 decide +kernel
def cuts23324 : List PrefixCut := [⟨30,124780344,124780414⟩,
⟨124,523664512,523664806⟩,
⟨128,541594696,541595001⟩]
theorem checked23324 : checkPrefixCuts (2^48) 3061055489 9 Manual.Count131072.C023324.packed 128 cuts23324 = true := by
 decide +kernel
def pointBounds23324 : List (Nat × Nat × Nat) := [(3061086208,102006439726452,102006821240083),(3061182464,102006838610620,102007220124475)]
theorem point_links_checked23324 : (cuts23324.take 2).map (fun c => (3061055489-1+2*2^9*c.k,102006314946108+c.lower,102006696459669+c.upper)) = pointBounds23324 := by
 decide +kernel
def cuts23325 : List PrefixCut := [⟨90,388113476,388113698⟩,
⟨128,555915381,555915693⟩]
theorem checked23325 : checkPrefixCuts (2^48) 3061186561 9 Manual.Count131072.C023325.packed 128 cuts23325 = true := by
 decide +kernel
def pointBounds23325 : List (Nat × Nat × Nat) := [(3061278720,102007244654280,102007626168368)]
theorem point_links_checked23325 : (cuts23325.take 1).map (fun c => (3061186561-1+2*2^9*c.k,102006856540804+c.lower,102007238054670+c.upper)) = pointBounds23325 := by
 decide +kernel
def cuts23326 : List PrefixCut := [⟨56,240619548,240619686⟩,
⟨128,555064063,555064386⟩]
theorem checked23326 : checkPrefixCuts (2^48) 3061317633 9 Manual.Count131072.C023326.packed 128 cuts23326 = true := by
 decide +kernel
def pointBounds23326 : List (Nat × Nat × Nat) := [(3061374976,102007653075733,102008034590049)]
theorem point_links_checked23326 : (cuts23326.take 1).map (fun c => (3061317633-1+2*2^9*c.k,102007412456185+c.lower,102007793970363+c.upper)) = pointBounds23326 := by
 decide +kernel
def cuts23327 : List PrefixCut := [⟨22,95710991,95711043⟩,
⟨116,494453117,494453389⟩,
⟨128,543088308,543088606⟩]
theorem checked23327 : checkPrefixCuts (2^48) 3061448705 9 Manual.Count131072.C023327.packed 128 cuts23327 = true := by
 decide +kernel
def pointBounds23327 : List (Nat × Nat × Nat) := [(3061471232,102008063231239,102008444745792),(3061567488,102008461973365,102008843488138)]
theorem point_links_checked23327 : (cuts23327.take 2).map (fun c => (3061448705-1+2*2^9*c.k,102007967520248+c.lower,102008349034749+c.upper)) = pointBounds23327 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S3.B000103
