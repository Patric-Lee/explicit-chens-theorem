import PlattAssemblyKernel
import PlattCertificates.Count131072.C021280
import PlattCertificates.Count131072.C021281
import PlattCertificates.Count131072.C021282
import PlattCertificates.Count131072.C021283
import PlattCertificates.Count131072.C021284
import PlattCertificates.Count131072.C021285
import PlattCertificates.Count131072.C021286
import PlattCertificates.Count131072.C021287
import PlattCertificates.Count131072.C021288
import PlattCertificates.Count131072.C021289
import PlattCertificates.Count131072.C021290
import PlattCertificates.Count131072.C021291
import PlattCertificates.Count131072.C021292
import PlattCertificates.Count131072.C021293
import PlattCertificates.Count131072.C021294
import PlattCertificates.Count131072.C021295
import PlattCertificates.Count131072.C021296
import PlattCertificates.Count131072.C021297
import PlattCertificates.Count131072.C021298
import PlattCertificates.Count131072.C021299
import PlattCertificates.Count131072.C021300
import PlattCertificates.Count131072.C021301
import PlattCertificates.Count131072.C021302
import PlattCertificates.Count131072.C021303
import PlattCertificates.Count131072.C021304
import PlattCertificates.Count131072.C021305
import PlattCertificates.Count131072.C021306
import PlattCertificates.Count131072.C021307
import PlattCertificates.Count131072.C021308
import PlattCertificates.Count131072.C021309
import PlattCertificates.Count131072.C021310
import PlattCertificates.Count131072.C021311
namespace ChenEffective.PlattWindow.Assembly.Prefix.S3.B000040
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts21280 : List PrefixCut := [⟨80,381623658,381623878⟩,
⟨128,611076128,611076482⟩]
theorem checked21280 : checkPrefixCuts (2^48) 2793144321 9 Manual.Count131072.C021280.packed 128 cuts21280 = true := by
 decide +kernel
def pointBounds21280 : List (Nat × Nat × Nat) := [(2793226240,100823919296616,100824300134034)]
theorem point_links_checked21280 : (cuts21280.take 1).map (fun c => (2793144321-1+2*2^9*c.k,100823537672958+c.lower,100823918510156+c.upper)) = pointBounds21280 := by
 decide +kernel
def cuts21281 : List PrefixCut := [⟨38,178359479,178359582⟩,
⟨124,591599866,591600209⟩,
⟨128,610341990,610342344⟩]
theorem checked21281 : checkPrefixCuts (2^48) 2793275393 9 Manual.Count131072.C021281.packed 128 cuts21281 = true := by
 decide +kernel
def pointBounds21281 : List (Nat × Nat × Nat) := [(2793314304,100824327108565,100824707946220),(2793402368,100824740348952,100825121186847)]
theorem point_links_checked21281 : (cuts21281.take 2).map (fun c => (2793275393-1+2*2^9*c.k,100824148749086+c.lower,100824529586638+c.upper)) = pointBounds21281 := by
 decide +kernel
def cuts21282 : List PrefixCut := [⟨82,392671584,392671813⟩,
⟨128,609305900,609306258⟩]
theorem checked21282 : checkPrefixCuts (2^48) 2793406465 9 Manual.Count131072.C021282.packed 128 cuts21282 = true := by
 decide +kernel
def pointBounds21282 : List (Nat × Nat × Nat) := [(2793490432,100825151762660,100825532600795)]
theorem point_links_checked21282 : (cuts21282.take 1).map (fun c => (2793406465-1+2*2^9*c.k,100824759091076+c.lower,100825139928982+c.upper)) = pointBounds21282 := by
 decide +kernel
def cuts21283 : List PrefixCut := [⟨40,188217017,188217129⟩,
⟨126,591242000,591242344⟩,
⟨128,600309915,600310264⟩]
theorem checked21283 : checkPrefixCuts (2^48) 2793537537 9 Manual.Count131072.C021283.packed 128 cuts21283 = true := by
 decide +kernel
def pointBounds21283 : List (Nat × Nat × Nat) := [(2793578496,100825556613993,100825937452369),(2793666560,100825959638976,100826340477584)]
theorem point_links_checked21283 : (cuts21283.take 2).map (fun c => (2793537537-1+2*2^9*c.k,100825368396976+c.lower,100825749235240+c.upper)) = pointBounds21283 := by
 decide +kernel
def cuts21284 : List PrefixCut := [⟨84,401299274,401299503⟩,
⟨128,608341886,608342230⟩]
theorem checked21284 : checkPrefixCuts (2^48) 2793668609 9 Manual.Count131072.C021284.packed 128 cuts21284 = true := by
 decide +kernel
def pointBounds21284 : List (Nat × Nat × Nat) := [(2793754624,100826370006165,100826750845007)]
theorem point_links_checked21284 : (cuts21284.take 1).map (fun c => (2793668609-1+2*2^9*c.k,100825968706891+c.lower,100826349545504+c.upper)) = pointBounds21284 := by
 decide +kernel
def cuts21285 : List PrefixCut := [⟨42,199382403,199382516⟩,
⟨128,604283505,604283850⟩]
theorem checked21285 : checkPrefixCuts (2^48) 2793799681 9 Manual.Count131072.C021285.packed 128 cuts21285 = true := by
 decide +kernel
def pointBounds21285 : List (Nat × Nat × Nat) := [(2793842688,100826776431180,100827157270250),(2793930752,100827181332282,100827562171584)]
theorem point_links_checked21285 : (cuts21285.take 2).map (fun c => (2793799681-1+2*2^9*c.k,100826577048777+c.lower,100826957887734+c.upper)) = pointBounds21285 := by
 decide +kernel
def cuts21286 : List PrefixCut := [⟨86,417884151,417884382⟩,
⟨128,614329424,614329772⟩]
theorem checked21286 : checkPrefixCuts (2^48) 2793930753 9 Manual.Count131072.C021286.packed 128 cuts21286 = true := by
 decide +kernel
def pointBounds21286 : List (Nat × Nat × Nat) := [(2794018816,100827599216433,100827980055966)]
theorem point_links_checked21286 : (cuts21286.take 1).map (fun c => (2793930753-1+2*2^9*c.k,100827181332282+c.lower,100827562171584+c.upper)) = pointBounds21286 := by
 decide +kernel
def cuts21287 : List PrefixCut := [⟨44,209034644,209034762⟩,
⟨128,597074446,597074787⟩]
theorem checked21287 : checkPrefixCuts (2^48) 2794061825 9 Manual.Count131072.C021287.packed 128 cuts21287 = true := by
 decide +kernel
def pointBounds21287 : List (Nat × Nat × Nat) := [(2794106880,100828004696350,100828385536118)]
theorem point_links_checked21287 : (cuts21287.take 1).map (fun c => (2794061825-1+2*2^9*c.k,100827795661706+c.lower,100828176501356+c.upper)) = pointBounds21287 := by
 decide +kernel
def cuts21288 : List PrefixCut := [⟨2,9771356,9771362⟩,
⟨88,418751558,418751803⟩,
⟨128,612458568,612458920⟩]
theorem checked21288 : checkPrefixCuts (2^48) 2794192897 9 Manual.Count131072.C021288.packed 128 cuts21288 = true := by
 decide +kernel
def pointBounds21288 : List (Nat × Nat × Nat) := [(2794194944,100828402507508,100828783347505),(2794283008,100828811487710,100829192327946)]
theorem point_links_checked21288 : (cuts21288.take 2).map (fun c => (2794192897-1+2*2^9*c.k,100828392736152+c.lower,100828773576143+c.upper)) = pointBounds21288 := by
 decide +kernel
def cuts21289 : List PrefixCut := [⟨46,213245621,213245745⟩,
⟨128,600241576,600241924⟩]
theorem checked21289 : checkPrefixCuts (2^48) 2794323969 9 Manual.Count131072.C021289.packed 128 cuts21289 = true := by
 decide +kernel
def pointBounds21289 : List (Nat × Nat × Nat) := [(2794371072,100829218440341,100829599280808)]
theorem point_links_checked21289 : (cuts21289.take 1).map (fun c => (2794323969-1+2*2^9*c.k,100829005194720+c.lower,100829386035063+c.upper)) = pointBounds21289 := by
 decide +kernel
def cuts21290 : List PrefixCut := [⟨4,19540872,19540883⟩,
⟨90,425762721,425762965⟩,
⟨128,606760531,606760879⟩]
theorem checked21290 : checkPrefixCuts (2^48) 2794455041 9 Manual.Count131072.C021290.packed 128 cuts21290 = true := by
 decide +kernel
def pointBounds21290 : List (Nat × Nat × Nat) := [(2794459136,100829624977168,100830005817870),(2794547200,100830031199017,100830412039952)]
theorem point_links_checked21290 : (cuts21290.take 2).map (fun c => (2794455041-1+2*2^9*c.k,100829605436296+c.lower,100829986276987+c.upper)) = pointBounds21290 := by
 decide +kernel
def cuts21291 : List PrefixCut := [⟨48,229340809,229340942⟩,
⟨128,614185192,614185547⟩]
theorem checked21291 : checkPrefixCuts (2^48) 2794586113 9 Manual.Count131072.C021291.packed 128 cuts21291 = true := by
 decide +kernel
def pointBounds21291 : List (Nat × Nat × Nat) := [(2794635264,100830441537636,100830822378808)]
theorem point_links_checked21291 : (cuts21291.take 1).map (fun c => (2794586113-1+2*2^9*c.k,100830212196827+c.lower,100830593037866+c.upper)) = pointBounds21291 := by
 decide +kernel
def cuts21292 : List PrefixCut := [⟨6,25984899,25984916⟩,
⟨92,430456185,430456433⟩,
⟨128,598545707,598546049⟩]
theorem checked21292 : checkPrefixCuts (2^48) 2794717185 9 Manual.Count131072.C021292.packed 128 cuts21292 = true := by
 decide +kernel
def pointBounds21292 : List (Nat × Nat × Nat) := [(2794723328,100830852366918,100831233208329),(2794811392,100831256838204,100831637679846)]
theorem point_links_checked21292 : (cuts21292.take 2).map (fun c => (2794717185-1+2*2^9*c.k,100830826382019+c.lower,100831207223413+c.upper)) = pointBounds21292 := by
 decide +kernel
def cuts21293 : List PrefixCut := [⟨50,234757639,234757773⟩,
⟨128,605365897,605366245⟩]
theorem checked21293 : checkPrefixCuts (2^48) 2794848257 9 Manual.Count131072.C021293.packed 128 cuts21293 = true := by
 decide +kernel
def pointBounds21293 : List (Nat × Nat × Nat) := [(2794899456,100831659685365,100832040527235)]
theorem point_links_checked21293 : (cuts21293.take 1).map (fun c => (2794848257-1+2*2^9*c.k,100831424927726+c.lower,100831805769462+c.upper)) = pointBounds21293 := by
 decide +kernel
def cuts21294 : List PrefixCut := [⟨8,37966608,37966630⟩,
⟨94,445924355,445924616⟩,
⟨128,608761497,608761849⟩]
theorem checked21294 : checkPrefixCuts (2^48) 2794979329 9 Manual.Count131072.C021294.packed 128 cuts21294 = true := by
 decide +kernel
def pointBounds21294 : List (Nat × Nat × Nat) := [(2794987520,100832068260231,100832449102337),(2795075584,100832476217978,100832857060323)]
theorem point_links_checked21294 : (cuts21294.take 2).map (fun c => (2794979329-1+2*2^9*c.k,100832030293623+c.lower,100832411135707+c.upper)) = pointBounds21294 := by
 decide +kernel
def cuts21295 : List PrefixCut := [⟨52,248733079,248733223⟩,
⟨128,610142819,610143176⟩]
theorem checked21295 : checkPrefixCuts (2^48) 2795110401 9 Manual.Count131072.C021295.packed 128 cuts21295 = true := by
 decide +kernel
def pointBounds21295 : List (Nat × Nat × Nat) := [(2795163648,100832887788199,100833268630779)]
theorem point_links_checked21295 : (cuts21295.take 1).map (fun c => (2795110401-1+2*2^9*c.k,100832639055120+c.lower,100833019897556+c.upper)) = pointBounds21295 := by
 decide +kernel
def cuts21296 : List PrefixCut := [⟨10,46018847,46018872⟩,
⟨96,456858261,456858529⟩,
⟨128,608704428,608704780⟩]
theorem checked21296 : checkPrefixCuts (2^48) 2795241473 9 Manual.Count131072.C021296.packed 128 cuts21296 = true := by
 decide +kernel
def pointBounds21296 : List (Nat × Nat × Nat) := [(2795251712,100833295216786,100833676059604),(2795339776,100833706056200,100834086899261)]
theorem point_links_checked21296 : (cuts21296.take 2).map (fun c => (2795241473-1+2*2^9*c.k,100833249197939+c.lower,100833630040732+c.upper)) = pointBounds21296 := by
 decide +kernel
def cuts21297 : List PrefixCut := [⟨54,255858793,255858935⟩,
⟨128,609380767,609381111⟩]
theorem checked21297 : checkPrefixCuts (2^48) 2795372545 9 Manual.Count131072.C021297.packed 128 cuts21297 = true := by
 decide +kernel
def pointBounds21297 : List (Nat × Nat × Nat) := [(2795427840,100834113761160,100834494604447)]
theorem point_links_checked21297 : (cuts21297.take 1).map (fun c => (2795372545-1+2*2^9*c.k,100833857902367+c.lower,100834238745512+c.upper)) = pointBounds21297 := by
 decide +kernel
def cuts21298 : List PrefixCut := [⟨12,57996411,57996445⟩,
⟨98,464970836,464971105⟩,
⟨128,604619914,604620267⟩]
theorem checked21298 : checkPrefixCuts (2^48) 2795503617 9 Manual.Count131072.C021298.packed 128 cuts21298 = true := by
 decide +kernel
def pointBounds21298 : List (Nat × Nat × Nat) := [(2795515904,100834525279545,100834906123068),(2795603968,100834932253970,100835313097728)]
theorem point_links_checked21298 : (cuts21298.take 2).map (fun c => (2795503617-1+2*2^9*c.k,100834467283134+c.lower,100834848126623+c.upper)) = pointBounds21298 := by
 decide +kernel
def cuts21299 : List PrefixCut := [⟨56,268117953,268118109⟩,
⟨128,612343994,612344348⟩]
theorem checked21299 : checkPrefixCuts (2^48) 2795634689 9 Manual.Count131072.C021299.packed 128 cuts21299 = true := by
 decide +kernel
def pointBounds21299 : List (Nat × Nat × Nat) := [(2795692032,100835340021001,100835720864999)]
theorem point_links_checked21299 : (cuts21299.take 1).map (fun c => (2795634689-1+2*2^9*c.k,100835071903048+c.lower,100835452746890+c.upper)) = pointBounds21299 := by
 decide +kernel
def cuts21300 : List PrefixCut := [⟨14,64937787,64937825⟩,
⟨100,471571731,471572009⟩,
⟨128,598321314,598321666⟩]
theorem checked21300 : checkPrefixCuts (2^48) 2795765761 9 Manual.Count131072.C021300.packed 128 cuts21300 = true := by
 decide +kernel
def pointBounds21300 : List (Nat × Nat × Nat) := [(2795780096,100835749184829,100836130029063),(2795868160,100836155818773,100836536663247)]
theorem point_links_checked21300 : (cuts21300.take 2).map (fun c => (2795765761-1+2*2^9*c.k,100835684247042+c.lower,100836065091238+c.upper)) = pointBounds21300 := by
 decide +kernel
def cuts21301 : List PrefixCut := [⟨58,270810929,270811087⟩,
⟨128,604333444,604333797⟩]
theorem checked21301 : checkPrefixCuts (2^48) 2795896833 9 Manual.Count131072.C021301.packed 128 cuts21301 = true := by
 decide +kernel
def pointBounds21301 : List (Nat × Nat × Nat) := [(2795956224,100836553379285,100836934223991)]
theorem point_links_checked21301 : (cuts21301.take 1).map (fun c => (2795896833-1+2*2^9*c.k,100836282568356+c.lower,100836663412904+c.upper)) = pointBounds21301 := by
 decide +kernel
def cuts21302 : List PrefixCut := [⟨16,78522026,78522074⟩,
⟨102,484312236,484312517⟩,
⟨128,610043211,610043565⟩]
theorem checked21302 : checkPrefixCuts (2^48) 2796027905 9 Manual.Count131072.C021302.packed 128 cuts21302 = true := by
 decide +kernel
def pointBounds21302 : List (Nat × Nat × Nat) := [(2796044288,100836965423826,100837346268775),(2796132352,100837371214036,100837752059218)]
theorem point_links_checked21302 : (cuts21302.take 2).map (fun c => (2796027905-1+2*2^9*c.k,100836886901800+c.lower,100837267746701+c.upper)) = pointBounds21302 := by
 decide +kernel
def cuts21303 : List PrefixCut := [⟨60,287092961,287093126⟩,
⟨128,611222557,611222909⟩]
theorem checked21303 : checkPrefixCuts (2^48) 2796158977 9 Manual.Count131072.C021303.packed 128 cuts21303 = true := by
 decide +kernel
def pointBounds21303 : List (Nat × Nat × Nat) := [(2796220416,100837784037972,100838164883392)]
theorem point_links_checked21303 : (cuts21303.take 1).map (fun c => (2796158977-1+2*2^9*c.k,100837496945011+c.lower,100837877790266+c.upper)) = pointBounds21303 := by
 decide +kernel
def cuts21304 : List PrefixCut := [⟨18,85258844,85258894⟩,
⟨104,492621202,492621486⟩,
⟨128,604852458,604852809⟩]
theorem checked21304 : checkPrefixCuts (2^48) 2796290049 9 Manual.Count131072.C021304.packed 128 cuts21304 = true := by
 decide +kernel
def pointBounds21304 : List (Nat × Nat × Nat) := [(2796308480,100838193426412,100838574272069),(2796396544,100838600788770,100838981634661)]
theorem point_links_checked21304 : (cuts21304.take 2).map (fun c => (2796290049-1+2*2^9*c.k,100838108167568+c.lower,100838489013175+c.upper)) = pointBounds21304 := by
 decide +kernel
def cuts21305 : List PrefixCut := [⟨62,291394103,291394275⟩,
⟨128,608346919,608347276⟩]
theorem checked21305 : checkPrefixCuts (2^48) 2796421121 9 Manual.Count131072.C021305.packed 128 cuts21305 = true := by
 decide +kernel
def pointBounds21305 : List (Nat × Nat × Nat) := [(2796484608,100839004414129,100839385260259)]
theorem point_links_checked21305 : (cuts21305.take 1).map (fun c => (2796421121-1+2*2^9*c.k,100838713020026+c.lower,100839093865984+c.upper)) = pointBounds21305 := by
 decide +kernel
def cuts21306 : List PrefixCut := [⟨20,94913246,94913299⟩,
⟨106,501431948,501432241⟩,
⟨128,603487372,603487721⟩]
theorem checked21306 : checkPrefixCuts (2^48) 2796552193 9 Manual.Count131072.C021306.packed 128 cuts21306 = true := by
 decide +kernel
def pointBounds21306 : List (Nat × Nat × Nat) := [(2796572672,100839416280191,100839797126559),(2796660736,100839822798893,100840203645501)]
theorem point_links_checked21306 : (cuts21306.take 2).map (fun c => (2796552193-1+2*2^9*c.k,100839321366945+c.lower,100839702213260+c.upper)) = pointBounds21306 := by
 decide +kernel
def cuts21307 : List PrefixCut := [⟨64,300927930,300928099⟩,
⟨128,600943041,600943386⟩]
theorem checked21307 : checkPrefixCuts (2^48) 2796683265 9 Manual.Count131072.C021307.packed 128 cuts21307 = true := by
 decide +kernel
def pointBounds21307 : List (Nat × Nat × Nat) := [(2796748800,100840225782247,100840606629080)]
theorem point_links_checked21307 : (cuts21307.take 1).map (fun c => (2796683265-1+2*2^9*c.k,100839924854317+c.lower,100840305700981+c.upper)) = pointBounds21307 := by
 decide +kernel
def cuts21308 : List PrefixCut := [⟨22,105471617,105471677⟩,
⟨108,508228421,508228716⟩,
⟨128,604638579,604638927⟩]
theorem checked21308 : checkPrefixCuts (2^48) 2796814337 9 Manual.Count131072.C021308.packed 128 cuts21308 = true := by
 decide +kernel
def pointBounds21308 : List (Nat × Nat × Nat) := [(2796836864,100840631268975,100841012116044),(2796924928,100841034025779,100841414873083)]
theorem point_links_checked21308 : (cuts21308.take 2).map (fun c => (2796814337-1+2*2^9*c.k,100840525797358+c.lower,100840906644367+c.upper)) = pointBounds21308 := by
 decide +kernel
def cuts21309 : List PrefixCut := [⟨66,310862516,310862698⟩,
⟨128,614975315,614975671⟩]
theorem checked21309 : checkPrefixCuts (2^48) 2796945409 9 Manual.Count131072.C021309.packed 128 cuts21309 = true := by
 decide +kernel
def pointBounds21309 : List (Nat × Nat × Nat) := [(2797012992,100841441298453,100841822145992)]
theorem point_links_checked21309 : (cuts21309.take 1).map (fun c => (2796945409-1+2*2^9*c.k,100841130435937+c.lower,100841511283294+c.upper)) = pointBounds21309 := by
 decide +kernel
def cuts21310 : List PrefixCut := [⟨24,112606507,112606571⟩,
⟨110,519752814,519753111⟩,
⟨128,603474848,603475193⟩]
theorem checked21310 : checkPrefixCuts (2^48) 2797076481 9 Manual.Count131072.C021310.packed 128 cuts21310 = true := by
 decide +kernel
def pointBounds21310 : List (Nat × Nat × Nat) := [(2797101056,100841858017759,100842238865536),(2797189120,100842265164066,100842646012076)]
theorem point_links_checked21310 : (cuts21310.take 2).map (fun c => (2797076481-1+2*2^9*c.k,100841745411252+c.lower,100842126258965+c.upper)) = pointBounds21310 := by
 decide +kernel
def cuts21311 : List PrefixCut := [⟨68,321298307,321298497⟩,
⟨128,600226599,600226957⟩]
theorem checked21311 : checkPrefixCuts (2^48) 2797207553 9 Manual.Count131072.C021311.packed 128 cuts21311 = true := by
 decide +kernel
def pointBounds21311 : List (Nat × Nat × Nat) := [(2797277184,100842670184407,100843051032655)]
theorem point_links_checked21311 : (cuts21311.take 1).map (fun c => (2797207553-1+2*2^9*c.k,100842348886100+c.lower,100842729734158+c.upper)) = pointBounds21311 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S3.B000040
