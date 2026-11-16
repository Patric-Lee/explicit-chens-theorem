import PlattAssemblyKernel
import PlattCertificates.Count131072.C023328
import PlattCertificates.Count131072.C023329
import PlattCertificates.Count131072.C023330
import PlattCertificates.Count131072.C023331
import PlattCertificates.Count131072.C023332
import PlattCertificates.Count131072.C023333
import PlattCertificates.Count131072.C023334
import PlattCertificates.Count131072.C023335
import PlattCertificates.Count131072.C023336
import PlattCertificates.Count131072.C023337
import PlattCertificates.Count131072.C023338
import PlattCertificates.Count131072.C023339
import PlattCertificates.Count131072.C023340
import PlattCertificates.Count131072.C023341
import PlattCertificates.Count131072.C023342
import PlattCertificates.Count131072.C023343
import PlattCertificates.Count131072.C023344
import PlattCertificates.Count131072.C023345
import PlattCertificates.Count131072.C023346
import PlattCertificates.Count131072.C023347
import PlattCertificates.Count131072.C023348
import PlattCertificates.Count131072.C023349
import PlattCertificates.Count131072.C023350
import PlattCertificates.Count131072.C023351
import PlattCertificates.Count131072.C023352
import PlattCertificates.Count131072.C023353
import PlattCertificates.Count131072.C023354
import PlattCertificates.Count131072.C023355
import PlattCertificates.Count131072.C023356
import PlattCertificates.Count131072.C023357
import PlattCertificates.Count131072.C023358
import PlattCertificates.Count131072.C023359
namespace ChenEffective.PlattWindow.Assembly.Prefix.S3.B000104
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts23328 : List PrefixCut := [⟨82,354507266,354507463⟩,
⟨128,558785892,558786200⟩]
theorem checked23328 : checkPrefixCuts (2^48) 3061579777 9 Manual.Count131072.C023328.packed 128 cuts23328 = true := by
 decide +kernel
def pointBounds23328 : List (Nat × Nat × Nat) := [(3061663744,102008865115822,102009246630818)]
theorem point_links_checked23328 : (cuts23328.take 1).map (fun c => (3061579777-1+2*2^9*c.k,102008510608556+c.lower,102008892123355+c.upper)) = pointBounds23328 := by
 decide +kernel
def cuts23329 : List PrefixCut := [⟨48,205102775,205102889⟩,
⟨128,549936553,549936854⟩]
theorem checked23329 : checkPrefixCuts (2^48) 3061710849 9 Manual.Count131072.C023329.packed 128 cuts23329 = true := by
 decide +kernel
def pointBounds23329 : List (Nat × Nat × Nat) := [(3061760000,102009274497223,102009656012444)]
theorem point_links_checked23329 : (cuts23329.take 1).map (fun c => (3061710849-1+2*2^9*c.k,102009069394448+c.lower,102009450909555+c.upper)) = pointBounds23329 := by
 decide +kernel
def cuts23330 : List PrefixCut := [⟨14,62696064,62696098⟩,
⟨108,467271422,467271684⟩,
⟨128,553406359,553406671⟩]
theorem checked23330 : checkPrefixCuts (2^48) 3061841921 9 Manual.Count131072.C023330.packed 128 cuts23330 = true := by
 decide +kernel
def pointBounds23330 : List (Nat × Nat × Nat) := [(3061856256,102009682027065,102010063542507),(3061952512,102010086602423,102010468118093)]
theorem point_links_checked23330 : (cuts23330.take 2).map (fun c => (3061841921-1+2*2^9*c.k,102009619331001+c.lower,102010000846409+c.upper)) = pointBounds23330 := by
 decide +kernel
def cuts23331 : List PrefixCut := [⟨74,312360662,312360837⟩,
⟨128,543087077,543087379⟩]
theorem checked23331 : checkPrefixCuts (2^48) 3061972993 9 Manual.Count131072.C023331.packed 128 cuts23331 = true := by
 decide +kernel
def pointBounds23331 : List (Nat × Nat × Nat) := [(3062048768,102010485098022,102010866613917)]
theorem point_links_checked23331 : (cuts23331.take 1).map (fun c => (3061972993-1+2*2^9*c.k,102010172737360+c.lower,102010554253080+c.upper)) = pointBounds23331 := by
 decide +kernel
def cuts23332 : List PrefixCut := [⟨40,174099219,174099320⟩,
⟨128,555748914,555749233⟩]
theorem checked23332 : checkPrefixCuts (2^48) 3062104065 9 Manual.Count131072.C023332.packed 128 cuts23332 = true := by
 decide +kernel
def pointBounds23332 : List (Nat × Nat × Nat) := [(3062145024,102010889923656,102011271439779)]
theorem point_links_checked23332 : (cuts23332.take 1).map (fun c => (3062104065-1+2*2^9*c.k,102010715824437+c.lower,102011097340459+c.upper)) = pointBounds23332 := by
 decide +kernel
def cuts23333 : List PrefixCut := [⟨6,25828966,25828981⟩,
⟨100,427503999,427504242⟩,
⟨128,549107031,549107346⟩]
theorem checked23333 : checkPrefixCuts (2^48) 3062235137 9 Manual.Count131072.C023333.packed 128 cuts23333 = true := by
 decide +kernel
def pointBounds23333 : List (Nat × Nat × Nat) := [(3062241280,102011297402317,102011678918673),(3062337536,102011699077350,102012080593934)]
theorem point_links_checked23333 : (cuts23333.take 2).map (fun c => (3062235137-1+2*2^9*c.k,102011271573351+c.lower,102011653089692+c.upper)) = pointBounds23333 := by
 decide +kernel
def cuts23334 : List PrefixCut := [⟨66,289986051,289986208⟩,
⟨128,554966082,554966392⟩]
theorem checked23334 : checkPrefixCuts (2^48) 3062366209 9 Manual.Count131072.C023334.packed 128 cuts23334 = true := by
 decide +kernel
def pointBounds23334 : List (Nat × Nat × Nat) := [(3062433792,102012110666433,102012492183246)]
theorem point_links_checked23334 : (cuts23334.take 1).map (fun c => (3062366209-1+2*2^9*c.k,102011820680382+c.lower,102012202197038+c.upper)) = pointBounds23334 := by
 decide +kernel
def cuts23335 : List PrefixCut := [⟨32,136302175,136302252⟩,
⟨126,534446856,534447160⟩,
⟨128,544372742,544373052⟩]
theorem checked23335 : checkPrefixCuts (2^48) 3062497281 9 Manual.Count131072.C023335.packed 128 cuts23335 = true := by
 decide +kernel
def pointBounds23335 : List (Nat × Nat × Nat) := [(3062530048,102012511948639,102012893465682),(3062626304,102012910093320,102013291610590)]
theorem point_links_checked23335 : (cuts23335.take 2).map (fun c => (3062497281-1+2*2^9*c.k,102012375646464+c.lower,102012757163430+c.upper)) = pointBounds23335 := by
 decide +kernel
def cuts23336 : List PrefixCut := [⟨92,392066355,392066577⟩,
⟨128,545360449,545360757⟩]
theorem checked23336 : checkPrefixCuts (2^48) 3062628353 9 Manual.Count131072.C023336.packed 128 cuts23336 = true := by
 decide +kernel
def pointBounds23336 : List (Nat × Nat × Nat) := [(3062722560,102013312085561,102013693603059)]
theorem point_links_checked23336 : (cuts23336.take 1).map (fun c => (3062628353-1+2*2^9*c.k,102012920019206+c.lower,102013301536482+c.upper)) = pointBounds23336 := by
 decide +kernel
def cuts23337 : List PrefixCut := [⟨58,251258701,251258840⟩,
⟨128,556548924,556549239⟩]
theorem checked23337 : checkPrefixCuts (2^48) 3062759425 9 Manual.Count131072.C023337.packed 128 cuts23337 = true := by
 decide +kernel
def pointBounds23337 : List (Nat × Nat × Nat) := [(3062818816,102013716638356,102014098156079)]
theorem point_links_checked23337 : (cuts23337.take 1).map (fun c => (3062759425-1+2*2^9*c.k,102013465379655+c.lower,102013846897239+c.upper)) = pointBounds23337 := by
 decide +kernel
def cuts23338 : List PrefixCut := [⟨24,102466366,102466424⟩,
⟨118,511404843,511405136⟩,
⟨128,556157549,556157869⟩]
theorem checked23338 : checkPrefixCuts (2^48) 3062890497 9 Manual.Count131072.C023338.packed 128 cuts23338 = true := by
 decide +kernel
def pointBounds23338 : List (Nat × Nat × Nat) := [(3062915072,102014124394945,102014505912902),(3063011328,102014533333422,102014914851614)]
theorem point_links_checked23338 : (cuts23338.take 2).map (fun c => (3062890497-1+2*2^9*c.k,102014021928579+c.lower,102014403446478+c.upper)) = pointBounds23338 := by
 decide +kernel
def cuts23339 : List PrefixCut := [⟨84,365183759,365183975⟩,
⟨128,557787857,557788179⟩]
theorem checked23339 : checkPrefixCuts (2^48) 3063021569 9 Manual.Count131072.C023339.packed 128 cuts23339 = true := by
 decide +kernel
def pointBounds23339 : List (Nat × Nat × Nat) := [(3063107584,102014943269887,102015324788322)]
theorem point_links_checked23339 : (cuts23339.take 1).map (fun c => (3063021569-1+2*2^9*c.k,102014578086128+c.lower,102014959604347+c.upper)) = pointBounds23339 := by
 decide +kernel
def cuts23340 : List PrefixCut := [⟨50,218422091,218422216⟩,
⟨128,557580129,557580449⟩]
theorem checked23340 : checkPrefixCuts (2^48) 3063152641 9 Manual.Count131072.C023340.packed 128 cuts23340 = true := by
 decide +kernel
def pointBounds23340 : List (Nat × Nat × Nat) := [(3063203840,102015354296076,102015735814742)]
theorem point_links_checked23340 : (cuts23340.take 1).map (fun c => (3063152641-1+2*2^9*c.k,102015135873985+c.lower,102015517392526+c.upper)) = pointBounds23340 := by
 decide +kernel
def cuts23341 : List PrefixCut := [⟨16,71211970,71212009⟩,
⟨110,479455787,479456054⟩,
⟨128,556178091,556178403⟩]
theorem checked23341 : checkPrefixCuts (2^48) 3063283713 9 Manual.Count131072.C023341.packed 128 cuts23341 = true := by
 decide +kernel
def pointBounds23341 : List (Nat × Nat × Nat) := [(3063300096,102015764666084,102016146184984),(3063396352,102016172909901,102016554429029)]
theorem point_links_checked23341 : (cuts23341.take 2).map (fun c => (3063283713-1+2*2^9*c.k,102015693454114+c.lower,102016074972975+c.upper)) = pointBounds23341 := by
 decide +kernel
def cuts23342 : List PrefixCut := [⟨76,333805684,333805871⟩,
⟨128,558451282,558451592⟩]
theorem checked23342 : checkPrefixCuts (2^48) 3063414785 9 Manual.Count131072.C023342.packed 128 cuts23342 = true := by
 decide +kernel
def pointBounds23342 : List (Nat × Nat × Nat) := [(3063492608,102016583437889,102016964957249)]
theorem point_links_checked23342 : (cuts23342.take 1).map (fun c => (3063414785-1+2*2^9*c.k,102016249632205+c.lower,102016631151378+c.upper)) = pointBounds23342 := by
 decide +kernel
def cuts23343 : List PrefixCut := [⟨42,183021261,183021364⟩,
⟨128,554201043,554201359⟩]
theorem checked23343 : checkPrefixCuts (2^48) 3063545857 9 Manual.Count131072.C023343.packed 128 cuts23343 = true := by
 decide +kernel
def pointBounds23343 : List (Nat × Nat × Nat) := [(3063588864,102016991104748,102017372624334)]
theorem point_links_checked23343 : (cuts23343.take 1).map (fun c => (3063545857-1+2*2^9*c.k,102016808083487+c.lower,102017189602970+c.upper)) = pointBounds23343 := by
 decide +kernel
def cuts23344 : List PrefixCut := [⟨8,37393021,37393041⟩,
⟨102,441359354,441359605⟩,
⟨128,553717992,553718308⟩]
theorem checked23344 : checkPrefixCuts (2^48) 3063676929 9 Manual.Count131072.C023344.packed 128 cuts23344 = true := by
 decide +kernel
def pointBounds23344 : List (Nat × Nat × Nat) := [(3063685120,102017399677551,102017781197370),(3063781376,102017803643884,102018185163934)]
theorem point_links_checked23344 : (cuts23344.take 2).map (fun c => (3063676929-1+2*2^9*c.k,102017362284530+c.lower,102017743804329+c.upper)) = pointBounds23344 := by
 decide +kernel
def cuts23345 : List PrefixCut := [⟨68,295269831,295269999⟩,
⟨128,555164197,555164510⟩]
theorem checked23345 : checkPrefixCuts (2^48) 3063808001 9 Manual.Count131072.C023345.packed 128 cuts23345 = true := by
 decide +kernel
def pointBounds23345 : List (Nat × Nat × Nat) := [(3063877632,102018211272353,102018592792636)]
theorem point_links_checked23345 : (cuts23345.take 1).map (fun c => (3063808001-1+2*2^9*c.k,102017916002522+c.lower,102018297522637+c.upper)) = pointBounds23345 := by
 decide +kernel
def cuts23346 : List PrefixCut := [⟨34,140647583,140647666⟩,
⟨128,551741315,551741629⟩]
theorem checked23346 : checkPrefixCuts (2^48) 3063939073 9 Manual.Count131072.C023346.packed 128 cuts23346 = true := by
 decide +kernel
def pointBounds23346 : List (Nat × Nat × Nat) := [(3063973888,102018611814302,102018993334813),(3064070144,102019022908034,102019404428776)]
theorem point_links_checked23346 : (cuts23346.take 2).map (fun c => (3063939073-1+2*2^9*c.k,102018471166719+c.lower,102018852687147+c.upper)) = pointBounds23346 := by
 decide +kernel
def cuts23347 : List PrefixCut := [⟨94,400057431,400057656⟩,
⟨128,547492185,547492495⟩]
theorem checked23347 : checkPrefixCuts (2^48) 3064070145 9 Manual.Count131072.C023347.packed 128 cuts23347 = true := by
 decide +kernel
def pointBounds23347 : List (Nat × Nat × Nat) := [(3064166400,102019422965465,102019804486432)]
theorem point_links_checked23347 : (cuts23347.take 1).map (fun c => (3064070145-1+2*2^9*c.k,102019022908034+c.lower,102019404428776+c.upper)) = pointBounds23347 := by
 decide +kernel
def cuts23348 : List PrefixCut := [⟨60,257662324,257662475⟩,
⟨128,543151613,543151926⟩]
theorem checked23348 : checkPrefixCuts (2^48) 3064201217 9 Manual.Count131072.C023348.packed 128 cuts23348 = true := by
 decide +kernel
def pointBounds23348 : List (Nat × Nat × Nat) := [(3064262656,102019828062543,102020209583746)]
theorem point_links_checked23348 : (cuts23348.take 1).map (fun c => (3064201217-1+2*2^9*c.k,102019570400219+c.lower,102019951921271+c.upper)) = pointBounds23348 := by
 decide +kernel
def cuts23349 : List PrefixCut := [⟨26,108572393,108572455⟩,
⟨120,517501858,517502148⟩,
⟨128,550752067,550752377⟩]
theorem checked23349 : checkPrefixCuts (2^48) 3064332289 9 Manual.Count131072.C023349.packed 128 cuts23349 = true := by
 decide +kernel
def pointBounds23349 : List (Nat × Nat × Nat) := [(3064358912,102020222124225,102020603645652),(3064455168,102020631053690,102021012575345)]
theorem point_links_checked23349 : (cuts23349.take 2).map (fun c => (3064332289-1+2*2^9*c.k,102020113551832+c.lower,102020495073197+c.upper)) = pointBounds23349 := by
 decide +kernel
def cuts23350 : List PrefixCut := [⟨86,371808716,371808934⟩,
⟨128,553851457,553851772⟩]
theorem checked23350 : checkPrefixCuts (2^48) 3064463361 9 Manual.Count131072.C023350.packed 128 cuts23350 = true := by
 decide +kernel
def pointBounds23350 : List (Nat × Nat × Nat) := [(3064551424,102021036112615,102021417634508)]
theorem point_links_checked23350 : (cuts23350.take 1).map (fun c => (3064463361-1+2*2^9*c.k,102020664303899+c.lower,102021045825574+c.upper)) = pointBounds23350 := by
 decide +kernel
def cuts23351 : List PrefixCut := [⟨52,233382085,233382211⟩,
⟨128,558971165,558971474⟩]
theorem checked23351 : checkPrefixCuts (2^48) 3064594433 9 Manual.Count131072.C023351.packed 128 cuts23351 = true := by
 decide +kernel
def pointBounds23351 : List (Nat × Nat × Nat) := [(3064647680,102021451537441,102021833059557)]
theorem point_links_checked23351 : (cuts23351.take 1).map (fun c => (3064594433-1+2*2^9*c.k,102021218155356+c.lower,102021599677346+c.upper)) = pointBounds23351 := by
 decide +kernel
def cuts23352 : List PrefixCut := [⟨18,74392950,74392995⟩,
⟨112,474637927,474638199⟩,
⟨128,546089250,546089560⟩]
theorem checked23352 : checkPrefixCuts (2^48) 3064725505 9 Manual.Count131072.C023352.packed 128 cuts23352 = true := by
 decide +kernel
def pointBounds23352 : List (Nat × Nat × Nat) := [(3064743936,102021851519471,102022233041815),(3064840192,102022251764448,102022633287019)]
theorem point_links_checked23352 : (cuts23352.take 2).map (fun c => (3064725505-1+2*2^9*c.k,102021777126521+c.lower,102022158648820+c.upper)) = pointBounds23352 := by
 decide +kernel
def cuts23353 : List PrefixCut := [⟨78,333189343,333189529⟩,
⟨128,549647583,549647896⟩]
theorem checked23353 : checkPrefixCuts (2^48) 3064856577 9 Manual.Count131072.C023353.packed 128 cuts23353 = true := by
 decide +kernel
def pointBounds23353 : List (Nat × Nat × Nat) := [(3064936448,102022656405114,102023037927909)]
theorem point_links_checked23353 : (cuts23353.take 1).map (fun c => (3064856577-1+2*2^9*c.k,102022323215771+c.lower,102022704738380+c.upper)) = pointBounds23353 := by
 decide +kernel
def cuts23354 : List PrefixCut := [⟨44,191200278,191200391⟩,
⟨128,552838379,552838700⟩]
theorem checked23354 : checkPrefixCuts (2^48) 3064987649 9 Manual.Count131072.C023354.packed 128 cuts23354 = true := by
 decide +kernel
def pointBounds23354 : List (Nat × Nat × Nat) := [(3065032704,102023064063632,102023445586667)]
theorem point_links_checked23354 : (cuts23354.take 1).map (fun c => (3064987649-1+2*2^9*c.k,102022872863354+c.lower,102023254386276+c.upper)) = pointBounds23354 := by
 decide +kernel
def cuts23355 : List PrefixCut := [⟨10,42977139,42977166⟩,
⟨104,445100249,445100498⟩,
⟨128,549141471,549141776⟩]
theorem checked23355 : checkPrefixCuts (2^48) 3065118721 9 Manual.Count131072.C023355.packed 128 cuts23355 = true := by
 decide +kernel
def pointBounds23355 : List (Nat × Nat × Nat) := [(3065128960,102023468678872,102023850202142),(3065225216,102023870801982,102024252325474)]
theorem point_links_checked23355 : (cuts23355.take 2).map (fun c => (3065118721-1+2*2^9*c.k,102023425701733+c.lower,102023807224976+c.upper)) = pointBounds23355 := by
 decide +kernel
def cuts23356 : List PrefixCut := [⟨70,305507212,305507389⟩,
⟨128,552974713,552975029⟩]
theorem checked23356 : checkPrefixCuts (2^48) 3065249793 9 Manual.Count131072.C023356.packed 128 cuts23356 = true := by
 decide +kernel
def pointBounds23356 : List (Nat × Nat × Nat) := [(3065321472,102024280350416,102024661874141)]
theorem point_links_checked23356 : (cuts23356.take 1).map (fun c => (3065249793-1+2*2^9*c.k,102023974843204+c.lower,102024356366752+c.upper)) = pointBounds23356 := by
 decide +kernel
def cuts23357 : List PrefixCut := [⟨36,157660516,157660597⟩,
⟨128,553869321,553869622⟩]
theorem checked23357 : checkPrefixCuts (2^48) 3065380865 9 Manual.Count131072.C023357.packed 128 cuts23357 = true := by
 decide +kernel
def pointBounds23357 : List (Nat × Nat × Nat) := [(3065417728,102024685478433,102025067002378)]
theorem point_links_checked23357 : (cuts23357.take 1).map (fun c => (3065380865-1+2*2^9*c.k,102024527817917+c.lower,102024909341781+c.upper)) = pointBounds23357 := by
 decide +kernel
def cuts23358 : List PrefixCut := [⟨2,8171965,8171970⟩,
⟨96,417498269,417498510⟩,
⟨128,555590198,555590515⟩]
theorem checked23358 : checkPrefixCuts (2^48) 3065511937 9 Manual.Count131072.C023358.packed 128 cuts23358 = true := by
 decide +kernel
def pointBounds23358 : List (Nat × Nat × Nat) := [(3065513984,102025089859203,102025471383373),(3065610240,102025499185507,102025880709913)]
theorem point_links_checked23358 : (cuts23358.take 2).map (fun c => (3065511937-1+2*2^9*c.k,102025081687238+c.lower,102025463211403+c.upper)) = pointBounds23358 := by
 decide +kernel
def cuts23359 : List PrefixCut := [⟨62,267640724,267640867⟩,
⟨128,554189194,554189493⟩]
theorem checked23359 : checkPrefixCuts (2^48) 3065643009 9 Manual.Count131072.C023359.packed 128 cuts23359 = true := by
 decide +kernel
def pointBounds23359 : List (Nat × Nat × Nat) := [(3065706496,102025904918160,102026286442785)]
theorem point_links_checked23359 : (cuts23359.take 1).map (fun c => (3065643009-1+2*2^9*c.k,102025637277436+c.lower,102026018801918+c.upper)) = pointBounds23359 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S3.B000104
