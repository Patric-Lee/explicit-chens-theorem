import PlattAssemblyKernel
import PlattCertificates.Count131072.C022304
import PlattCertificates.Count131072.C022305
import PlattCertificates.Count131072.C022306
import PlattCertificates.Count131072.C022307
import PlattCertificates.Count131072.C022308
import PlattCertificates.Count131072.C022309
import PlattCertificates.Count131072.C022310
import PlattCertificates.Count131072.C022311
import PlattCertificates.Count131072.C022312
import PlattCertificates.Count131072.C022313
import PlattCertificates.Count131072.C022314
import PlattCertificates.Count131072.C022315
import PlattCertificates.Count131072.C022316
import PlattCertificates.Count131072.C022317
import PlattCertificates.Count131072.C022318
import PlattCertificates.Count131072.C022319
import PlattCertificates.Count131072.C022320
import PlattCertificates.Count131072.C022321
import PlattCertificates.Count131072.C022322
import PlattCertificates.Count131072.C022323
import PlattCertificates.Count131072.C022324
import PlattCertificates.Count131072.C022325
import PlattCertificates.Count131072.C022326
import PlattCertificates.Count131072.C022327
import PlattCertificates.Count131072.C022328
import PlattCertificates.Count131072.C022329
import PlattCertificates.Count131072.C022330
import PlattCertificates.Count131072.C022331
import PlattCertificates.Count131072.C022332
import PlattCertificates.Count131072.C022333
import PlattCertificates.Count131072.C022334
import PlattCertificates.Count131072.C022335
namespace ChenEffective.PlattWindow.Assembly.Prefix.S3.B000072
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts22304 : List PrefixCut := [⟨56,245091799,245091945⟩,
⟨128,566232796,566233119⟩]
theorem checked22304 : checkPrefixCuts (2^48) 2927362049 9 Manual.Count131072.C022304.packed 128 cuts22304 = true := by
 decide +kernel
def pointBounds22304 : List (Nat × Nat × Nat) := [(2927419392,101430556804968,101430937990697)]
theorem point_links_checked22304 : (cuts22304.take 1).map (fun c => (2927362049-1+2*2^9*c.k,101430311713169+c.lower,101430692898752+c.upper)) = pointBounds22304 := by
 decide +kernel
def cuts22305 : List PrefixCut := [⟨18,85379847,85379895⟩,
⟨108,495156908,495157182⟩,
⟨128,585244597,585244925⟩]
theorem checked22305 : checkPrefixCuts (2^48) 2927493121 9 Manual.Count131072.C022305.packed 128 cuts22305 = true := by
 decide +kernel
def pointBounds22305 : List (Nat × Nat × Nat) := [(2927511552,101430963325812,101431344511766),(2927603712,101431373102873,101431754289053)]
theorem point_links_checked22305 : (cuts22305.take 2).map (fun c => (2927493121-1+2*2^9*c.k,101430877945965+c.lower,101431259131871+c.upper)) = pointBounds22305 := by
 decide +kernel
def cuts22306 : List PrefixCut := [⟨70,321791627,321791815⟩,
⟨128,582526424,582526768⟩]
theorem checked22306 : checkPrefixCuts (2^48) 2927624193 9 Manual.Count131072.C022306.packed 128 cuts22306 = true := by
 decide +kernel
def pointBounds22306 : List (Nat × Nat × Nat) := [(2927695872,101431784982189,101432166168611)]
theorem point_links_checked22306 : (cuts22306.take 1).map (fun c => (2927624193-1+2*2^9*c.k,101431463190562+c.lower,101431844376796+c.upper)) = pointBounds22306 := by
 decide +kernel
def cuts22307 : List PrefixCut := [⟨32,141421394,141421478⟩,
⟨122,552794133,552794445⟩,
⟨128,579039252,579039579⟩]
theorem checked22307 : checkPrefixCuts (2^48) 2927755265 9 Manual.Count131072.C022307.packed 128 cuts22307 = true := by
 decide +kernel
def pointBounds22307 : List (Nat × Nat × Nat) := [(2927788032,101432187138380,101432568325042),(2927880192,101432598511119,101432979698009)]
theorem point_links_checked22307 : (cuts22307.take 2).map (fun c => (2927755265-1+2*2^9*c.k,101432045716986+c.lower,101432426903564+c.upper)) = pointBounds22307 := by
 decide +kernel
def cuts22308 : List PrefixCut := [⟨84,376366363,376366579⟩,
⟨128,576321573,576321897⟩]
theorem checked22308 : checkPrefixCuts (2^48) 2927886337 9 Manual.Count131072.C022308.packed 128 cuts22308 = true := by
 decide +kernel
def pointBounds22308 : List (Nat × Nat × Nat) := [(2927972352,101433001122601,101433382309722)]
theorem point_links_checked22308 : (cuts22308.take 1).map (fun c => (2927886337-1+2*2^9*c.k,101432624756238+c.lower,101433005943143+c.upper)) = pointBounds22308 := by
 decide +kernel
def cuts22309 : List PrefixCut := [⟨46,209853551,209853672⟩,
⟨128,574565619,574565959⟩]
theorem checked22309 : checkPrefixCuts (2^48) 2928017409 9 Manual.Count131072.C022309.packed 128 cuts22309 = true := by
 decide +kernel
def pointBounds22309 : List (Nat × Nat × Nat) := [(2928064512,101433410931362,101433792118712)]
theorem point_links_checked22309 : (cuts22309.take 1).map (fun c => (2928017409-1+2*2^9*c.k,101433201077811+c.lower,101433582265040+c.upper)) = pointBounds22309 := by
 decide +kernel
def cuts22310 : List PrefixCut := [⟨8,37585709,37585730⟩,
⟨98,443619720,443619978⟩,
⟨128,574251508,574251846⟩]
theorem checked22310 : checkPrefixCuts (2^48) 2928148481 9 Manual.Count131072.C022310.packed 128 cuts22310 = true := by
 decide +kernel
def pointBounds22310 : List (Nat × Nat × Nat) := [(2928156672,101433813229139,101434194416729),(2928248832,101434219263150,101434600450977)]
theorem point_links_checked22310 : (cuts22310.take 2).map (fun c => (2928148481-1+2*2^9*c.k,101433775643430+c.lower,101434156830999+c.upper)) = pointBounds22310 := by
 decide +kernel
def cuts22311 : List PrefixCut := [⟨60,277023454,277023608⟩,
⟨128,586913681,586914010⟩]
theorem checked22311 : checkPrefixCuts (2^48) 2928279553 9 Manual.Count131072.C022311.packed 128 cuts22311 = true := by
 decide +kernel
def pointBounds22311 : List (Nat × Nat × Nat) := [(2928340992,101434626918392,101435008106453)]
theorem point_links_checked22311 : (cuts22311.take 1).map (fun c => (2928279553-1+2*2^9*c.k,101434349894938+c.lower,101434731082845+c.upper)) = pointBounds22311 := by
 decide +kernel
def cuts22312 : List PrefixCut := [⟨22,99001832,99001890⟩,
⟨112,499134399,499134685⟩,
⟨128,573238777,573239104⟩]
theorem checked22312 : checkPrefixCuts (2^48) 2928410625 9 Manual.Count131072.C022312.packed 128 cuts22312 = true := by
 decide +kernel
def pointBounds22312 : List (Nat × Nat × Nat) := [(2928433152,101435035810451,101435416998745),(2928525312,101435435943018,101435817131540)]
theorem point_links_checked22312 : (cuts22312.take 2).map (fun c => (2928410625-1+2*2^9*c.k,101434936808619+c.lower,101435317996855+c.upper)) = pointBounds22312 := by
 decide +kernel
def cuts22313 : List PrefixCut := [⟨74,334858090,334858280⟩,
⟨128,577057712,577058041⟩]
theorem checked22313 : checkPrefixCuts (2^48) 2928541697 9 Manual.Count131072.C022313.packed 128 cuts22313 = true := by
 decide +kernel
def pointBounds22313 : List (Nat × Nat × Nat) := [(2928617472,101435844905486,101436226094239)]
theorem point_links_checked22313 : (cuts22313.take 1).map (fun c => (2928541697-1+2*2^9*c.k,101435510047396+c.lower,101435891235959+c.upper)) = pointBounds22313 := by
 decide +kernel
def cuts22314 : List PrefixCut := [⟨36,164923806,164923901⟩,
⟨126,566075884,566076210⟩,
⟨128,575302039,575302371⟩]
theorem checked22314 : checkPrefixCuts (2^48) 2928672769 9 Manual.Count131072.C022314.packed 128 cuts22314 = true := by
 decide +kernel
def pointBounds22314 : List (Nat × Nat × Nat) := [(2928709632,101436252028914,101436633217901),(2928801792,101436653180992,101437034370210)]
theorem point_links_checked22314 : (cuts22314.take 2).map (fun c => (2928672769-1+2*2^9*c.k,101436087105108+c.lower,101436468294000+c.upper)) = pointBounds22314 := by
 decide +kernel
def cuts22315 : List PrefixCut := [⟨88,397391124,397391357⟩,
⟨128,577678706,577679037⟩]
theorem checked22315 : checkPrefixCuts (2^48) 2928803841 9 Manual.Count131072.C022315.packed 128 cuts22315 = true := by
 decide +kernel
def pointBounds22315 : List (Nat × Nat × Nat) := [(2928893952,101437059798271,101437440987728)]
theorem point_links_checked22315 : (cuts22315.take 1).map (fun c => (2928803841-1+2*2^9*c.k,101436662407147+c.lower,101437043596371+c.upper)) = pointBounds22315 := by
 decide +kernel
def cuts22316 : List PrefixCut := [⟨50,232755698,232755828⟩,
⟨128,589280969,589281302⟩]
theorem checked22316 : checkPrefixCuts (2^48) 2928934913 9 Manual.Count131072.C022316.packed 128 cuts22316 = true := by
 decide +kernel
def pointBounds22316 : List (Nat × Nat × Nat) := [(2928986112,101437472841551,101437854031236)]
theorem point_links_checked22316 : (cuts22316.take 1).map (fun c => (2928934913-1+2*2^9*c.k,101437240085853+c.lower,101437621275408+c.upper)) = pointBounds22316 := by
 decide +kernel
def cuts22317 : List PrefixCut := [⟨12,52949423,52949455⟩,
⟨102,458663575,458663840⟩,
⟨128,574359895,574360227⟩]
theorem checked22317 : checkPrefixCuts (2^48) 2929065985 9 Manual.Count131072.C022317.packed 128 cuts22317 = true := by
 decide +kernel
def pointBounds22317 : List (Nat × Nat × Nat) := [(2929078272,101437882316245,101438263506165),(2929170432,101438288030397,101438669220550)]
theorem point_links_checked22317 : (cuts22317.take 2).map (fun c => (2929065985-1+2*2^9*c.k,101437829366822+c.lower,101438210556710+c.upper)) = pointBounds22317 := by
 decide +kernel
def cuts22318 : List PrefixCut := [⟨64,291926798,291926961⟩,
⟨128,581829193,581829519⟩]
theorem checked22318 : checkPrefixCuts (2^48) 2929197057 9 Manual.Count131072.C022318.packed 128 cuts22318 = true := by
 decide +kernel
def pointBounds22318 : List (Nat × Nat × Nat) := [(2929262592,101438695653515,101439076843898)]
theorem point_links_checked22318 : (cuts22318.take 1).map (fun c => (2929197057-1+2*2^9*c.k,101438403726717+c.lower,101438784916937+c.upper)) = pointBounds22318 := by
 decide +kernel
def cuts22319 : List PrefixCut := [⟨26,117131409,117131479⟩,
⟨116,520116842,520117141⟩,
⟨128,572771126,572771455⟩]
theorem checked22319 : checkPrefixCuts (2^48) 2929328129 9 Manual.Count131072.C022319.packed 128 cuts22319 = true := by
 decide +kernel
def pointBounds22319 : List (Nat × Nat × Nat) := [(2929354752,101439102687319,101439483877935),(2929446912,101439505672752,101439886863597)]
theorem point_links_checked22319 : (cuts22319.take 2).map (fun c => (2929328129-1+2*2^9*c.k,101438985555910+c.lower,101439366746456+c.upper)) = pointBounds22319 := by
 decide +kernel
def cuts22320 : List PrefixCut := [⟨78,351663627,351663826⟩,
⟨128,576684814,576685136⟩]
theorem checked22320 : checkPrefixCuts (2^48) 2929459201 9 Manual.Count131072.C022320.packed 128 cuts22320 = true := by
 decide +kernel
def pointBounds22320 : List (Nat × Nat × Nat) := [(2929539072,101439909990663,101440291181737)]
theorem point_links_checked22320 : (cuts22320.take 1).map (fun c => (2929459201-1+2*2^9*c.k,101439558327036+c.lower,101439939517911+c.upper)) = pointBounds22320 := by
 decide +kernel
def cuts22321 : List PrefixCut := [⟨40,181782012,181782113⟩,
⟨128,583480550,583480886⟩]
theorem checked22321 : checkPrefixCuts (2^48) 2929590273 9 Manual.Count131072.C022321.packed 128 cuts22321 = true := by
 decide +kernel
def pointBounds22321 : List (Nat × Nat × Nat) := [(2929631232,101440316793862,101440697985160)]
theorem point_links_checked22321 : (cuts22321.take 1).map (fun c => (2929590273-1+2*2^9*c.k,101440135011850+c.lower,101440516203047+c.upper)) = pointBounds22321 := by
 decide +kernel
def cuts22322 : List PrefixCut := [⟨2,9319335,9319340⟩,
⟨92,415040165,415040409⟩,
⟨128,580860364,580860703⟩]
theorem checked22322 : checkPrefixCuts (2^48) 2929721345 9 Manual.Count131072.C022322.packed 128 cuts22322 = true := by
 decide +kernel
def pointBounds22322 : List (Nat × Nat × Nat) := [(2929723392,101440727811735,101441109003273),(2929815552,101441133532565,101441514724342)]
theorem point_links_checked22322 : (cuts22322.take 2).map (fun c => (2929721345-1+2*2^9*c.k,101440718492400+c.lower,101441099683933+c.upper)) = pointBounds22322 := by
 decide +kernel
def cuts22323 : List PrefixCut := [⟨54,236813644,236813775⟩,
⟨128,574589801,574590122⟩]
theorem checked22323 : checkPrefixCuts (2^48) 2929852417 9 Manual.Count131072.C022323.packed 128 cuts22323 = true := by
 decide +kernel
def pointBounds22323 : List (Nat × Nat × Nat) := [(2929907712,101441536166408,101441917358411)]
theorem point_links_checked22323 : (cuts22323.take 1).map (fun c => (2929852417-1+2*2^9*c.k,101441299352764+c.lower,101441680544636+c.upper)) = pointBounds22323 := by
 decide +kernel
def cuts22324 : List PrefixCut := [⟨16,70224831,70224870⟩,
⟨106,476772010,476772286⟩,
⟨128,577350110,577350441⟩]
theorem checked22324 : checkPrefixCuts (2^48) 2929983489 9 Manual.Count131072.C022324.packed 128 cuts22324 = true := by
 decide +kernel
def pointBounds22324 : List (Nat × Nat × Nat) := [(2929999872,101441944167396,101442325359628),(2930092032,101442350714575,101442731907044)]
theorem point_links_checked22324 : (cuts22324.take 2).map (fun c => (2929983489-1+2*2^9*c.k,101441873942565+c.lower,101442255134758+c.upper)) = pointBounds22324 := by
 decide +kernel
def cuts22325 : List PrefixCut := [⟨68,307301100,307301275⟩,
⟨128,578380916,578381252⟩]
theorem checked22325 : checkPrefixCuts (2^48) 2930114561 9 Manual.Count131072.C022325.packed 128 cuts22325 = true := by
 decide +kernel
def pointBounds22325 : List (Nat × Nat × Nat) := [(2930184192,101442758593775,101443139786474)]
theorem point_links_checked22325 : (cuts22325.take 1).map (fun c => (2930114561-1+2*2^9*c.k,101442451292675+c.lower,101442832485199+c.upper)) = pointBounds22325 := by
 decide +kernel
def cuts22326 : List PrefixCut := [⟨30,134673252,134673333⟩,
⟨120,534746324,534746639⟩,
⟨128,574224643,574224981⟩]
theorem checked22326 : checkPrefixCuts (2^48) 2930245633 9 Manual.Count131072.C022326.packed 128 cuts22326 = true := by
 decide +kernel
def pointBounds22326 : List (Nat × Nat × Nat) := [(2930276352,101443164346843,101443545539784),(2930368512,101443564419915,101443945613090)]
theorem point_links_checked22326 : (cuts22326.take 2).map (fun c => (2930245633-1+2*2^9*c.k,101443029673591+c.lower,101443410866451+c.upper)) = pointBounds22326 := by
 decide +kernel
def cuts22327 : List PrefixCut := [⟨82,368554529,368554747⟩,
⟨128,569972693,569973028⟩]
theorem checked22327 : checkPrefixCuts (2^48) 2930376705 9 Manual.Count131072.C022327.packed 128 cuts22327 = true := by
 decide +kernel
def pointBounds22327 : List (Nat × Nat × Nat) := [(2930460672,101443972452763,101444353646179)]
theorem point_links_checked22327 : (cuts22327.take 1).map (fun c => (2930376705-1+2*2^9*c.k,101443603898234+c.lower,101443985091432+c.upper)) = pointBounds22327 := by
 decide +kernel
def cuts22328 : List PrefixCut := [⟨44,197957253,197957364⟩,
⟨128,576862617,576862951⟩]
theorem checked22328 : checkPrefixCuts (2^48) 2930507777 9 Manual.Count131072.C022328.packed 128 cuts22328 = true := by
 decide +kernel
def pointBounds22328 : List (Nat × Nat × Nat) := [(2930552832,101444371828180,101444753021824)]
theorem point_links_checked22328 : (cuts22328.take 1).map (fun c => (2930507777-1+2*2^9*c.k,101444173870927+c.lower,101444555064460+c.upper)) = pointBounds22328 := by
 decide +kernel
def cuts22329 : List PrefixCut := [⟨6,26028323,26028339⟩,
⟨96,431621603,431621850⟩,
⟨128,573859538,573859865⟩]
theorem checked22329 : checkPrefixCuts (2^48) 2930638849 9 Manual.Count131072.C022329.packed 128 cuts22329 = true := by
 decide +kernel
def pointBounds22329 : List (Nat × Nat × Nat) := [(2930644992,101444776761867,101445157955750),(2930737152,101445182355147,101445563549261)]
theorem point_links_checked22329 : (cuts22329.take 2).map (fun c => (2930638849-1+2*2^9*c.k,101444750733544+c.lower,101445131927411+c.upper)) = pointBounds22329 := by
 decide +kernel
def cuts22330 : List PrefixCut := [⟨58,264302928,264303077⟩,
⟨128,584302013,584302350⟩]
theorem checked22330 : checkPrefixCuts (2^48) 2930769921 9 Manual.Count131072.C022330.packed 128 cuts22330 = true := by
 decide +kernel
def pointBounds22330 : List (Nat × Nat × Nat) := [(2930829312,101445588896010,101445970090353)]
theorem point_links_checked22330 : (cuts22330.take 1).map (fun c => (2930769921-1+2*2^9*c.k,101445324593082+c.lower,101445705787276+c.upper)) = pointBounds22330 := by
 decide +kernel
def cuts22331 : List PrefixCut := [⟨20,90178415,90178468⟩,
⟨110,505048795,505049086⟩,
⟨128,585908577,585908915⟩]
theorem checked22331 : checkPrefixCuts (2^48) 2930900993 9 Manual.Count131072.C022331.packed 128 cuts22331 = true := by
 decide +kernel
def pointBounds22331 : List (Nat × Nat × Nat) := [(2930921472,101445999073510,101446380268094),(2931013632,101446413943890,101446795138712)]
theorem point_links_checked22331 : (cuts22331.take 2).map (fun c => (2930900993-1+2*2^9*c.k,101445908895095+c.lower,101446290089626+c.upper)) = pointBounds22331 := by
 decide +kernel
def cuts22332 : List PrefixCut := [⟨72,323722165,323722344⟩,
⟨128,574838891,574839215⟩]
theorem checked22332 : checkPrefixCuts (2^48) 2931032065 9 Manual.Count131072.C022332.packed 128 cuts22332 = true := by
 decide +kernel
def pointBounds22332 : List (Nat × Nat × Nat) := [(2931105792,101446818525837,101447199720885)]
theorem point_links_checked22332 : (cuts22332.take 1).map (fun c => (2931032065-1+2*2^9*c.k,101446494803672+c.lower,101446875998541+c.upper)) = pointBounds22332 := by
 decide +kernel
def cuts22333 : List PrefixCut := [⟨34,154892878,154892962⟩,
⟨124,559161252,559161575⟩,
⟨128,578750184,578750516⟩]
theorem checked22333 : checkPrefixCuts (2^48) 2931163137 9 Manual.Count131072.C022333.packed 128 cuts22333 = true := by
 decide +kernel
def pointBounds22333 : List (Nat × Nat × Nat) := [(2931197952,101447224535441,101447605730718),(2931290112,101447628803815,101448009999331)]
theorem point_links_checked22333 : (cuts22333.take 2).map (fun c => (2931163137-1+2*2^9*c.k,101447069642563+c.lower,101447450837756+c.upper)) = pointBounds22333 := by
 decide +kernel
def cuts22334 : List PrefixCut := [⟨86,388027520,388027740⟩,
⟨128,579684475,579684803⟩]
theorem checked22334 : checkPrefixCuts (2^48) 2931294209 9 Manual.Count131072.C022334.packed 128 cuts22334 = true := by
 decide +kernel
def pointBounds22334 : List (Nat × Nat × Nat) := [(2931382272,101448036420267,101448417616012)]
theorem point_links_checked22334 : (cuts22334.take 1).map (fun c => (2931294209-1+2*2^9*c.k,101447648392747+c.lower,101448029588272+c.upper)) = pointBounds22334 := by
 decide +kernel
def cuts22335 : List PrefixCut := [⟨48,209513462,209513586⟩,
⟨128,577834149,577834477⟩]
theorem checked22335 : checkPrefixCuts (2^48) 2931425281 9 Manual.Count131072.C022335.packed 128 cuts22335 = true := by
 decide +kernel
def pointBounds22335 : List (Nat × Nat × Nat) := [(2931474432,101448437590684,101448818786661)]
theorem point_links_checked22335 : (cuts22335.take 1).map (fun c => (2931425281-1+2*2^9*c.k,101448228077222+c.lower,101448609273075+c.upper)) = pointBounds22335 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S3.B000072
