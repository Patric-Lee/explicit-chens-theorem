import PlattAssemblyKernel
import PlattCertificates.Count131072.C025440
import PlattCertificates.Count131072.C025441
import PlattCertificates.Count131072.C025442
import PlattCertificates.Count131072.C025443
import PlattCertificates.Count131072.C025444
import PlattCertificates.Count131072.C025445
import PlattCertificates.Count131072.C025446
import PlattCertificates.Count131072.C025447
import PlattCertificates.Count131072.C025448
import PlattCertificates.Count131072.C025449
import PlattCertificates.Count131072.C025450
import PlattCertificates.Count131072.C025451
import PlattCertificates.Count131072.C025452
import PlattCertificates.Count131072.C025453
import PlattCertificates.Count131072.C025454
import PlattCertificates.Count131072.C025455
import PlattCertificates.Count131072.C025456
import PlattCertificates.Count131072.C025457
import PlattCertificates.Count131072.C025458
import PlattCertificates.Count131072.C025459
import PlattCertificates.Count131072.C025460
import PlattCertificates.Count131072.C025461
import PlattCertificates.Count131072.C025462
import PlattCertificates.Count131072.C025463
import PlattCertificates.Count131072.C025464
import PlattCertificates.Count131072.C025465
import PlattCertificates.Count131072.C025466
import PlattCertificates.Count131072.C025467
import PlattCertificates.Count131072.C025468
import PlattCertificates.Count131072.C025469
import PlattCertificates.Count131072.C025470
import PlattCertificates.Count131072.C025471
namespace ChenEffective.PlattWindow.Assembly.Prefix.S3.B000170
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts25440 : List PrefixCut := [⟨72,280341694,280341852⟩,
⟨128,505622371,505622650⟩]
theorem checked25440 : checkPrefixCuts (2^48) 3338403841 9 Manual.Count131072.C025440.packed 128 cuts25440 = true := by
 decide +kernel
def pointBounds25440 : List (Nat × Nat × Nat) := [(3338477568,103122099902605,103122482044778)]
theorem point_links_checked25440 : (cuts25440.take 1).map (fun c => (3338403841-1+2*2^9*c.k,103121819560911+c.lower,103122201702926+c.upper)) = pointBounds25440 := by
 decide +kernel
def cuts25441 : List PrefixCut := [⟨46,176292862,176292962⟩,
⟨128,498689112,498689394⟩]
theorem checked25441 : checkPrefixCuts (2^48) 3338534913 9 Manual.Count131072.C025441.packed 128 cuts25441 = true := by
 decide +kernel
def pointBounds25441 : List (Nat × Nat × Nat) := [(3338582016,103122501476144,103122883618538)]
theorem point_links_checked25441 : (cuts25441.take 1).map (fun c => (3338534913-1+2*2^9*c.k,103122325183282+c.lower,103122707325576+c.upper)) = pointBounds25441 := by
 decide +kernel
def cuts25442 : List PrefixCut := [⟨20,74864910,74864951⟩,
⟨122,474052630,474052892⟩,
⟨128,498416591,498416866⟩]
theorem checked25442 : checkPrefixCuts (2^48) 3338665985 9 Manual.Count131072.C025442.packed 128 cuts25442 = true := by
 decide +kernel
def pointBounds25442 : List (Nat × Nat × Nat) := [(3338686464,103122898737304,103123280879921),(3338790912,103123297925024,103123680067862)]
theorem point_links_checked25442 : (cuts25442.take 2).map (fun c => (3338665985-1+2*2^9*c.k,103122823872394+c.lower,103123206014970+c.upper)) = pointBounds25442 := by
 decide +kernel
def cuts25443 : List PrefixCut := [⟨96,371186356,371186571⟩,
⟨128,498228539,498228824⟩]
theorem checked25443 : checkPrefixCuts (2^48) 3338797057 9 Manual.Count131072.C025443.packed 128 cuts25443 = true := by
 decide +kernel
def pointBounds25443 : List (Nat × Nat × Nat) := [(3338895360,103123693475341,103124075618407)]
theorem point_links_checked25443 : (cuts25443.take 1).map (fun c => (3338797057-1+2*2^9*c.k,103123322288985+c.lower,103123704431836+c.upper)) = pointBounds25443 := by
 decide +kernel
def cuts25444 : List PrefixCut := [⟨70,276167071,276167223⟩,
⟨128,505795955,505796236⟩]
theorem checked25444 : checkPrefixCuts (2^48) 3338928129 9 Manual.Count131072.C025444.packed 128 cuts25444 = true := by
 decide +kernel
def pointBounds25444 : List (Nat × Nat × Nat) := [(3338999808,103124096684595,103124478827883)]
theorem point_links_checked25444 : (cuts25444.take 1).map (fun c => (3338928129-1+2*2^9*c.k,103123820517524+c.lower,103124202660660+c.upper)) = pointBounds25444 := by
 decide +kernel
def cuts25445 : List PrefixCut := [⟨44,174073509,174073608⟩,
⟨128,503753015,503753300⟩]
theorem checked25445 : checkPrefixCuts (2^48) 3339059201 9 Manual.Count131072.C025445.packed 128 cuts25445 = true := by
 decide +kernel
def pointBounds25445 : List (Nat × Nat × Nat) := [(3339104256,103124500386988,103124882530504)]
theorem point_links_checked25445 : (cuts25445.take 1).map (fun c => (3339059201-1+2*2^9*c.k,103124326313479+c.lower,103124708456896+c.upper)) = pointBounds25445 := by
 decide +kernel
def cuts25446 : List PrefixCut := [⟨18,71565713,71565751⟩,
⟨120,471955433,471955698⟩,
⟨128,503311740,503312023⟩]
theorem checked25446 : checkPrefixCuts (2^48) 3339190273 9 Manual.Count131072.C025446.packed 128 cuts25446 = true := by
 decide +kernel
def pointBounds25446 : List (Nat × Nat × Nat) := [(3339208704,103124901632207,103125283775947),(3339313152,103125302021927,103125684165894)]
theorem point_links_checked25446 : (cuts25446.take 2).map (fun c => (3339190273-1+2*2^9*c.k,103124830066494+c.lower,103125212210196+c.upper)) = pointBounds25446 := by
 decide +kernel
def cuts25447 : List PrefixCut := [⟨94,366239299,366239504⟩,
⟨128,496211667,496211945⟩]
theorem checked25447 : checkPrefixCuts (2^48) 3339321345 9 Manual.Count131072.C025447.packed 128 cuts25447 = true := by
 decide +kernel
def pointBounds25447 : List (Nat × Nat × Nat) := [(3339417600,103125699617533,103126081761723)]
theorem point_links_checked25447 : (cuts25447.take 1).map (fun c => (3339321345-1+2*2^9*c.k,103125333378234+c.lower,103125715522219+c.upper)) = pointBounds25447 := by
 decide +kernel
def cuts25448 : List PrefixCut := [⟨68,265587884,265588037⟩,
⟨128,499563614,499563900⟩]
theorem checked25448 : checkPrefixCuts (2^48) 3339452417 9 Manual.Count131072.C025448.packed 128 cuts25448 = true := by
 decide +kernel
def pointBounds25448 : List (Nat × Nat × Nat) := [(3339522048,103126095177785,103126477322201)]
theorem point_links_checked25448 : (cuts25448.take 1).map (fun c => (3339452417-1+2*2^9*c.k,103125829589901+c.lower,103126211734164+c.upper)) = pointBounds25448 := by
 decide +kernel
def cuts25449 : List PrefixCut := [⟨42,168820649,168820740⟩,
⟨128,503842540,503842821⟩]
theorem checked25449 : checkPrefixCuts (2^48) 3339583489 9 Manual.Count131072.C025449.packed 128 cuts25449 = true := by
 decide +kernel
def pointBounds25449 : List (Nat × Nat × Nat) := [(3339626496,103126497974164,103126880118804)]
theorem point_links_checked25449 : (cuts25449.take 1).map (fun c => (3339583489-1+2*2^9*c.k,103126329153515+c.lower,103126711298064+c.upper)) = pointBounds25449 := by
 decide +kernel
def cuts25450 : List PrefixCut := [⟨16,62452159,62452193⟩,
⟨118,458396722,458396979⟩,
⟨128,497670245,497670524⟩]
theorem checked25450 : checkPrefixCuts (2^48) 3339714561 9 Manual.Count131072.C025450.packed 128 cuts25450 = true := by
 decide +kernel
def pointBounds25450 : List (Nat × Nat × Nat) := [(3339730944,103126895448214,103127277593078),(3339835392,103127291392777,103127673537864)]
theorem point_links_checked25450 : (cuts25450.take 2).map (fun c => (3339714561-1+2*2^9*c.k,103126832996055+c.lower,103127215140885+c.upper)) = pointBounds25450 := by
 decide +kernel
def cuts25451 : List PrefixCut := [⟨92,363990784,363990982⟩,
⟨128,507595330,507595605⟩]
theorem checked25451 : checkPrefixCuts (2^48) 3339845633 9 Manual.Count131072.C025451.packed 128 cuts25451 = true := by
 decide +kernel
def pointBounds25451 : List (Nat × Nat × Nat) := [(3339939840,103127694657084,103128076802391)]
theorem point_links_checked25451 : (cuts25451.take 1).map (fun c => (3339845633-1+2*2^9*c.k,103127330666300+c.lower,103127712811409+c.upper)) = pointBounds25451 := by
 decide +kernel
def cuts25452 : List PrefixCut := [⟨66,256276232,256276379⟩,
⟨128,501507767,501508058⟩]
theorem checked25452 : checkPrefixCuts (2^48) 3339976705 9 Manual.Count131072.C025452.packed 128 cuts25452 = true := by
 decide +kernel
def pointBounds25452 : List (Nat × Nat × Nat) := [(3340044288,103128094537862,103128476683393)]
theorem point_links_checked25452 : (cuts25452.take 1).map (fun c => (3339976705-1+2*2^9*c.k,103127838261630+c.lower,103128220407014+c.upper)) = pointBounds25452 := by
 decide +kernel
def cuts25453 : List PrefixCut := [⟨40,157754703,157754796⟩,
⟨128,505195932,505196215⟩]
theorem checked25453 : checkPrefixCuts (2^48) 3340107777 9 Manual.Count131072.C025453.packed 128 cuts25453 = true := by
 decide +kernel
def pointBounds25453 : List (Nat × Nat × Nat) := [(3340148736,103128497524100,103128879669868)]
theorem point_links_checked25453 : (cuts25453.take 1).map (fun c => (3340107777-1+2*2^9*c.k,103128339769397+c.lower,103128721915072+c.upper)) = pointBounds25453 := by
 decide +kernel
def cuts25454 : List PrefixCut := [⟨14,56543633,56543665⟩,
⟨116,456218300,456218555⟩,
⟨128,501384203,501384484⟩]
theorem checked25454 : checkPrefixCuts (2^48) 3340238849 9 Manual.Count131072.C025454.packed 128 cuts25454 = true := by
 decide +kernel
def pointBounds25454 : List (Nat × Nat × Nat) := [(3340253184,103128901508962,103129283654952),(3340357632,103129301183629,103129683329842)]
theorem point_links_checked25454 : (cuts25454.take 2).map (fun c => (3340238849-1+2*2^9*c.k,103128844965329+c.lower,103129227111287+c.upper)) = pointBounds25454 := by
 decide +kernel
def cuts25455 : List PrefixCut := [⟨90,354327688,354327892⟩,
⟨128,504819232,504819518⟩]
theorem checked25455 : checkPrefixCuts (2^48) 3340369921 9 Manual.Count131072.C025455.packed 128 cuts25455 = true := by
 decide +kernel
def pointBounds25455 : List (Nat × Nat × Nat) := [(3340462080,103129700677220,103130082823663)]
theorem point_links_checked25455 : (cuts25455.take 1).map (fun c => (3340369921-1+2*2^9*c.k,103129346349532+c.lower,103129728495771+c.upper)) = pointBounds25455 := by
 decide +kernel
def cuts25456 : List PrefixCut := [⟨64,255561941,255562079⟩,
⟨128,507327216,507327494⟩]
theorem checked25456 : checkPrefixCuts (2^48) 3340500993 9 Manual.Count131072.C025456.packed 128 cuts25456 = true := by
 decide +kernel
def pointBounds25456 : List (Nat × Nat × Nat) := [(3340566528,103130106730705,103130488877368)]
theorem point_links_checked25456 : (cuts25456.take 1).map (fun c => (3340500993-1+2*2^9*c.k,103129851168764+c.lower,103130233315289+c.upper)) = pointBounds25456 := by
 decide +kernel
def cuts25457 : List PrefixCut := [⟨38,150989423,150989508⟩,
⟨128,507307355,507307639⟩]
theorem checked25457 : checkPrefixCuts (2^48) 3340632065 9 Manual.Count131072.C025457.packed 128 cuts25457 = true := by
 decide +kernel
def pointBounds25457 : List (Nat × Nat × Nat) := [(3340670976,103130509485403,103130891632291)]
theorem point_links_checked25457 : (cuts25457.take 1).map (fun c => (3340632065-1+2*2^9*c.k,103130358495980+c.lower,103130740642783+c.upper)) = pointBounds25457 := by
 decide +kernel
def cuts25458 : List PrefixCut := [⟨12,46424239,46424267⟩,
⟨114,441992326,441992573⟩,
⟨128,495660562,495660838⟩]
theorem checked25458 : checkPrefixCuts (2^48) 3340763137 9 Manual.Count131072.C025458.packed 128 cuts25458 = true := by
 decide +kernel
def pointBounds25458 : List (Nat × Nat × Nat) := [(3340775424,103130912227574,103131294374689),(3340879872,103131307795661,103131689942995)]
theorem point_links_checked25458 : (cuts25458.take 2).map (fun c => (3340763137-1+2*2^9*c.k,103130865803335+c.lower,103131247950422+c.upper)) = pointBounds25458 := by
 decide +kernel
def cuts25459 : List PrefixCut := [⟨88,348964442,348964642⟩,
⟨128,509120983,509121280⟩]
theorem checked25459 : checkPrefixCuts (2^48) 3340894209 9 Manual.Count131072.C025459.packed 128 cuts25459 = true := by
 decide +kernel
def pointBounds25459 : List (Nat × Nat × Nat) := [(3340984320,103131710428339,103132092575902)]
theorem point_links_checked25459 : (cuts25459.take 1).map (fun c => (3340894209-1+2*2^9*c.k,103131361463897+c.lower,103131743611260+c.upper)) = pointBounds25459 := by
 decide +kernel
def cuts25460 : List PrefixCut := [⟨62,242463620,242463759⟩,
⟨128,503035316,503035600⟩]
theorem checked25460 : checkPrefixCuts (2^48) 3341025281 9 Manual.Count131072.C025460.packed 128 cuts25460 = true := by
 decide +kernel
def pointBounds25460 : List (Nat × Nat × Nat) := [(3341088768,103132113048500,103132495196299)]
theorem point_links_checked25460 : (cuts25460.take 1).map (fun c => (3341025281-1+2*2^9*c.k,103131870584880+c.lower,103132252732540+c.upper)) = pointBounds25460 := by
 decide +kernel
def cuts25461 : List PrefixCut := [⟨36,139508545,139508623⟩,
⟨128,496276135,496276416⟩]
theorem checked25461 : checkPrefixCuts (2^48) 3341156353 9 Manual.Count131072.C025461.packed 128 cuts25461 = true := by
 decide +kernel
def pointBounds25461 : List (Nat × Nat × Nat) := [(3341193216,103132513128741,103132895276763)]
theorem point_links_checked25461 : (cuts25461.take 1).map (fun c => (3341156353-1+2*2^9*c.k,103132373620196+c.lower,103132755768140+c.upper)) = pointBounds25461 := by
 decide +kernel
def cuts25462 : List PrefixCut := [⟨10,40604316,40604340⟩,
⟨112,441670326,441670576⟩,
⟨128,504849091,504849375⟩]
theorem checked25462 : checkPrefixCuts (2^48) 3341287425 9 Manual.Count131072.C025462.packed 128 cuts25462 = true := by
 decide +kernel
def pointBounds25462 : List (Nat × Nat × Nat) := [(3341297664,103132910500647,103133292648896),(3341402112,103133311566657,103133693715132)]
theorem point_links_checked25462 : (cuts25462.take 2).map (fun c => (3341287425-1+2*2^9*c.k,103132869896331+c.lower,103133252044556+c.upper)) = pointBounds25462 := by
 decide +kernel
def cuts25463 : List PrefixCut := [⟨86,337369263,337369450⟩,
⟨128,502807542,502807822⟩]
theorem checked25463 : checkPrefixCuts (2^48) 3341418497 9 Manual.Count131072.C025463.packed 128 cuts25463 = true := by
 decide +kernel
def pointBounds25463 : List (Nat × Nat × Nat) := [(3341506560,103133712114685,103134094263381)]
theorem point_links_checked25463 : (cuts25463.take 1).map (fun c => (3341418497-1+2*2^9*c.k,103133374745422+c.lower,103133756893931+c.upper)) = pointBounds25463 := by
 decide +kernel
def cuts25464 : List PrefixCut := [⟨60,235181527,235181659⟩,
⟨128,502619413,502619694⟩]
theorem checked25464 : checkPrefixCuts (2^48) 3341549569 9 Manual.Count131072.C025464.packed 128 cuts25464 = true := by
 decide +kernel
def pointBounds25464 : List (Nat × Nat × Nat) := [(3341611008,103134112734491,103134494883412)]
theorem point_links_checked25464 : (cuts25464.take 1).map (fun c => (3341549569-1+2*2^9*c.k,103133877552964+c.lower,103134259701753+c.upper)) = pointBounds25464 := by
 decide +kernel
def cuts25465 : List PrefixCut := [⟨34,133590518,133590595⟩,
⟨128,503694706,503694997⟩]
theorem checked25465 : checkPrefixCuts (2^48) 3341680641 9 Manual.Count131072.C025465.packed 128 cuts25465 = true := by
 decide +kernel
def pointBounds25465 : List (Nat × Nat × Nat) := [(3341715456,103134513762895,103134895912042)]
theorem point_links_checked25465 : (cuts25465.take 1).map (fun c => (3341680641-1+2*2^9*c.k,103134380172377+c.lower,103134762321447+c.upper)) = pointBounds25465 := by
 decide +kernel
def cuts25466 : List PrefixCut := [⟨8,31164407,31164425⟩,
⟨110,430820162,430820409⟩,
⟨128,501653522,501653810⟩]
theorem checked25466 : checkPrefixCuts (2^48) 3341811713 9 Manual.Count131072.C025466.packed 128 cuts25466 = true := by
 decide +kernel
def pointBounds25466 : List (Nat × Nat × Nat) := [(3341819904,103134915031490,103135297180869),(3341924352,103135314687245,103135696836853)]
theorem point_links_checked25466 : (cuts25466.take 2).map (fun c => (3341811713-1+2*2^9*c.k,103134883867083+c.lower,103135266016444+c.upper)) = pointBounds25466 := by
 decide +kernel
def cuts25467 : List PrefixCut := [⟨84,326535880,326536061⟩,
⟨128,499612499,499612777⟩]
theorem checked25467 : checkPrefixCuts (2^48) 3341942785 9 Manual.Count131072.C025467.packed 128 cuts25467 = true := by
 decide +kernel
def pointBounds25467 : List (Nat × Nat × Nat) := [(3342028800,103135712056485,103136094206315)]
theorem point_links_checked25467 : (cuts25467.take 1).map (fun c => (3341942785-1+2*2^9*c.k,103135385520605+c.lower,103135767670254+c.upper)) = pointBounds25467 := by
 decide +kernel
def cuts25468 : List PrefixCut := [⟨58,230765231,230765355⟩,
⟨128,505909426,505909706⟩]
theorem checked25468 : checkPrefixCuts (2^48) 3342073857 9 Manual.Count131072.C025468.packed 128 cuts25468 = true := by
 decide +kernel
def pointBounds25468 : List (Nat × Nat × Nat) := [(3342133248,103136115898335,103136498048386)]
theorem point_links_checked25468 : (cuts25468.take 1).map (fun c => (3342073857-1+2*2^9*c.k,103135885133104+c.lower,103136267283031+c.upper)) = pointBounds25468 := by
 decide +kernel
def cuts25469 : List PrefixCut := [⟨32,128011228,128011302⟩,
⟨128,509342461,509342751⟩]
theorem checked25469 : checkPrefixCuts (2^48) 3342204929 9 Manual.Count131072.C025469.packed 128 cuts25469 = true := by
 decide +kernel
def pointBounds25469 : List (Nat × Nat × Nat) := [(3342237696,103136519053758,103136901204039)]
theorem point_links_checked25469 : (cuts25469.take 1).map (fun c => (3342204929-1+2*2^9*c.k,103136391042530+c.lower,103136773192737+c.upper)) = pointBounds25469 := by
 decide +kernel
def cuts25470 : List PrefixCut := [⟨6,21727455,21727467⟩,
⟨108,422752342,422752580⟩,
⟨128,497111518,497111800⟩]
theorem checked25470 : checkPrefixCuts (2^48) 3342336001 9 Manual.Count131072.C025470.packed 128 cuts25470 = true := by
 decide +kernel
def pointBounds25470 : List (Nat × Nat × Nat) := [(3342342144,103136922112446,103137304262955),(3342446592,103137323137333,103137705288068)]
theorem point_links_checked25470 : (cuts25470.take 2).map (fun c => (3342336001-1+2*2^9*c.k,103136900384991+c.lower,103137282535488+c.upper)) = pointBounds25470 := by
 decide +kernel
def cuts25471 : List PrefixCut := [⟨83,321516227,321516409⟩,
⟨128,501302428,501302711⟩]
theorem checked25471 : checkPrefixCuts (2^48) 3342467073 9 Manual.Count131072.C025471.packed 128 cuts25471 = true := by
 decide +kernel
def pointBounds25471 : List (Nat × Nat × Nat) := [(3342552064,103137719012736,103138101163697)]
theorem point_links_checked25471 : (cuts25471.take 1).map (fun c => (3342467073-1+2*2^9*c.k,103137397496509+c.lower,103137779647288+c.upper)) = pointBounds25471 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S3.B000170
