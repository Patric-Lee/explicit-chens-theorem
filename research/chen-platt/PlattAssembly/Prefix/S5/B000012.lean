import PlattAssemblyKernel
import PlattCertificates.Count131072.C040384
import PlattCertificates.Count131072.C040385
import PlattCertificates.Count131072.C040386
import PlattCertificates.Count131072.C040387
import PlattCertificates.Count131072.C040388
import PlattCertificates.Count131072.C040389
import PlattCertificates.Count131072.C040390
import PlattCertificates.Count131072.C040391
import PlattCertificates.Count131072.C040392
import PlattCertificates.Count131072.C040393
import PlattCertificates.Count131072.C040394
import PlattCertificates.Count131072.C040395
import PlattCertificates.Count131072.C040396
import PlattCertificates.Count131072.C040397
import PlattCertificates.Count131072.C040398
import PlattCertificates.Count131072.C040399
import PlattCertificates.Count131072.C040400
import PlattCertificates.Count131072.C040401
import PlattCertificates.Count131072.C040402
import PlattCertificates.Count131072.C040403
import PlattCertificates.Count131072.C040404
import PlattCertificates.Count131072.C040405
import PlattCertificates.Count131072.C040406
import PlattCertificates.Count131072.C040407
import PlattCertificates.Count131072.C040408
import PlattCertificates.Count131072.C040409
import PlattCertificates.Count131072.C040410
import PlattCertificates.Count131072.C040411
import PlattCertificates.Count131072.C040412
import PlattCertificates.Count131072.C040413
import PlattCertificates.Count131072.C040414
import PlattCertificates.Count131072.C040415
namespace ChenEffective.PlattWindow.Assembly.Prefix.S5.B000012
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts40384 : List PrefixCut := [⟨64,315630515,315630702⟩]
theorem checked40384 : checkPrefixCuts (2^48) 5297143809 10 Manual.Count131072.C040384.packed 64 cuts40384 = true := by
 decide +kernel
def cuts40385 : List PrefixCut := [⟨11,54889155,54889189⟩,
⟨64,315516454,315516644⟩]
theorem checked40385 : checkPrefixCuts (2^48) 5297274881 10 Manual.Count131072.C040385.packed 64 cuts40385 = true := by
 decide +kernel
def pointBounds40385 : List (Nat × Nat × Nat) := [(5297297408,108986657819299,108987043396409)]
theorem point_links_checked40385 : (cuts40385.take 1).map (fun c => (5297274881-1+2*2^10*c.k,108986602930144+c.lower,108986988507220+c.upper)) = pointBounds40385 := by
 decide +kernel
def cuts40386 : List PrefixCut := [⟨28,137564413,137564493⟩,
⟨64,314020871,314021060⟩]
theorem checked40386 : checkPrefixCuts (2^48) 5297405953 10 Manual.Count131072.C040386.packed 64 cuts40386 = true := by
 decide +kernel
def pointBounds40386 : List (Nat × Nat × Nat) := [(5297463296,108987056011011,108987441588357)]
theorem point_links_checked40386 : (cuts40386.take 1).map (fun c => (5297405953-1+2*2^10*c.k,108986918446598+c.lower,108987304023864+c.upper)) = pointBounds40386 := by
 decide +kernel
def cuts40387 : List PrefixCut := [⟨45,219863121,219863249⟩,
⟨64,312525403,312525586⟩]
theorem checked40387 : checkPrefixCuts (2^48) 5297537025 10 Manual.Count131072.C040387.packed 64 cuts40387 = true := by
 decide +kernel
def pointBounds40387 : List (Nat × Nat × Nat) := [(5297629184,108987452330590,108987837908173)]
theorem point_links_checked40387 : (cuts40387.take 1).map (fun c => (5297537025-1+2*2^10*c.k,108987232467469+c.lower,108987618044924+c.upper)) = pointBounds40387 := by
 decide +kernel
def cuts40388 : List PrefixCut := [⟨62,294612595,294612770⟩,
⟨64,303963573,303963752⟩]
theorem checked40388 : checkPrefixCuts (2^48) 5297668097 10 Manual.Count131072.C040388.packed 64 cuts40388 = true := by
 decide +kernel
def pointBounds40388 : List (Nat × Nat × Nat) := [(5297795072,108987839605467,108988225183280)]
theorem point_links_checked40388 : (cuts40388.take 1).map (fun c => (5297668097-1+2*2^10*c.k,108987544992872+c.lower,108987930570510+c.upper)) = pointBounds40388 := by
 decide +kernel
def cuts40389 : List PrefixCut := [⟨64,313519354,313519541⟩]
theorem checked40389 : checkPrefixCuts (2^48) 5297799169 10 Manual.Count131072.C040389.packed 64 cuts40389 = true := by
 decide +kernel
def cuts40390 : List PrefixCut := [⟨15,74008786,74008831⟩,
⟨64,310270791,310270975⟩]
theorem checked40390 : checkPrefixCuts (2^48) 5297930241 10 Manual.Count131072.C040390.packed 64 cuts40390 = true := by
 decide +kernel
def pointBounds40390 : List (Nat × Nat × Nat) := [(5297960960,108988236484585,108988622062634)]
theorem point_links_checked40390 : (cuts40390.take 1).map (fun c => (5297930241-1+2*2^10*c.k,108988162475799+c.lower,108988548053803+c.upper)) = pointBounds40390 := by
 decide +kernel
def cuts40391 : List PrefixCut := [⟨32,154973139,154973234⟩,
⟨64,310263111,310263300⟩]
theorem checked40391 : checkPrefixCuts (2^48) 5298061313 10 Manual.Count131072.C040391.packed 64 cuts40391 = true := by
 decide +kernel
def pointBounds40391 : List (Nat × Nat × Nat) := [(5298126848,108988627719729,108989013298012)]
theorem point_links_checked40391 : (cuts40391.take 1).map (fun c => (5298061313-1+2*2^10*c.k,108988472746590+c.lower,108988858324778+c.upper)) = pointBounds40391 := by
 decide +kernel
def cuts40392 : List PrefixCut := [⟨49,237951736,237951874⟩,
⟨64,309617941,309618122⟩]
theorem checked40392 : checkPrefixCuts (2^48) 5298192385 10 Manual.Count131072.C040392.packed 64 cuts40392 = true := by
 decide +kernel
def pointBounds40392 : List (Nat × Nat × Nat) := [(5298292736,108989020961437,108989406539952)]
theorem point_links_checked40392 : (cuts40392.take 1).map (fun c => (5298192385-1+2*2^10*c.k,108988783009701+c.lower,108989168588078+c.upper)) = pointBounds40392 := by
 decide +kernel
def cuts40393 : List PrefixCut := [⟨64,313966490,313966673⟩]
theorem checked40393 : checkPrefixCuts (2^48) 5298323457 10 Manual.Count131072.C040393.packed 64 cuts40393 = true := by
 decide +kernel
def cuts40394 : List PrefixCut := [⟨2,8712326,8712332⟩,
⟨64,312843129,312843313⟩]
theorem checked40394 : checkPrefixCuts (2^48) 5298454529 10 Manual.Count131072.C040394.packed 64 cuts40394 = true := by
 decide +kernel
def pointBounds40394 : List (Nat × Nat × Nat) := [(5298458624,108989415306458,108989800885205)]
theorem point_links_checked40394 : (cuts40394.take 1).map (fun c => (5298454529-1+2*2^10*c.k,108989406594132+c.lower,108989792172873+c.upper)) = pointBounds40394 := by
 decide +kernel
def cuts40395 : List PrefixCut := [⟨19,91051883,91051941⟩,
⟨64,309169955,309170142⟩]
theorem checked40395 : checkPrefixCuts (2^48) 5298585601 10 Manual.Count131072.C040395.packed 64 cuts40395 = true := by
 decide +kernel
def pointBounds40395 : List (Nat × Nat × Nat) := [(5298624512,108989810489144,108990196068127)]
theorem point_links_checked40395 : (cuts40395.take 1).map (fun c => (5298585601-1+2*2^10*c.k,108989719437261+c.lower,108990105016186+c.upper)) = pointBounds40395 := by
 decide +kernel
def cuts40396 : List PrefixCut := [⟨36,177264661,177264766⟩,
⟨64,311765278,311765459⟩]
theorem checked40396 : checkPrefixCuts (2^48) 5298716673 10 Manual.Count131072.C040396.packed 64 cuts40396 = true := by
 decide +kernel
def pointBounds40396 : List (Nat × Nat × Nat) := [(5298790400,108990205871877,108990591451094)]
theorem point_links_checked40396 : (cuts40396.take 1).map (fun c => (5298716673-1+2*2^10*c.k,108990028607216+c.lower,108990414186328+c.upper)) = pointBounds40396 := by
 decide +kernel
def cuts40397 : List PrefixCut := [⟨53,258266902,258267056⟩,
⟨64,311385720,311385905⟩]
theorem checked40397 : checkPrefixCuts (2^48) 5298847745 10 Manual.Count131072.C040397.packed 64 cuts40397 = true := by
 decide +kernel
def pointBounds40397 : List (Nat × Nat × Nat) := [(5298956288,108990598639396,108990984218843)]
theorem point_links_checked40397 : (cuts40397.take 1).map (fun c => (5298847745-1+2*2^10*c.k,108990340372494+c.lower,108990725951787+c.upper)) = pointBounds40397 := by
 decide +kernel
def cuts40398 : List PrefixCut := [⟨64,310368788,310368971⟩]
theorem checked40398 : checkPrefixCuts (2^48) 5298978817 10 Manual.Count131072.C040398.packed 64 cuts40398 = true := by
 decide +kernel
def cuts40399 : List PrefixCut := [⟨6,28417771,28417788⟩,
⟨64,311370298,311370483⟩]
theorem checked40399 : checkPrefixCuts (2^48) 5299109889 10 Manual.Count131072.C040399.packed 64 cuts40399 = true := by
 decide +kernel
def pointBounds40399 : List (Nat × Nat × Nat) := [(5299122176,108990990544773,108991376124451)]
theorem point_links_checked40399 : (cuts40399.take 1).map (fun c => (5299109889-1+2*2^10*c.k,108990962127002+c.lower,108991347706663+c.upper)) = pointBounds40399 := by
 decide +kernel
def cuts40400 : List PrefixCut := [⟨23,111012110,111012179⟩,
⟨64,310194062,310194249⟩]
theorem checked40400 : checkPrefixCuts (2^48) 5299240961 10 Manual.Count131072.C040400.packed 64 cuts40400 = true := by
 decide +kernel
def pointBounds40400 : List (Nat × Nat × Nat) := [(5299288064,108991384509410,108991770089325)]
theorem point_links_checked40400 : (cuts40400.take 1).map (fun c => (5299240961-1+2*2^10*c.k,108991273497300+c.lower,108991659077146+c.upper)) = pointBounds40400 := by
 decide +kernel
def cuts40401 : List PrefixCut := [⟨40,194929686,194929806⟩,
⟨64,311195573,311195762⟩]
theorem checked40401 : checkPrefixCuts (2^48) 5299372033 10 Manual.Count131072.C040401.packed 64 cuts40401 = true := by
 decide +kernel
def pointBounds40401 : List (Nat × Nat × Nat) := [(5299453952,108991778621048,108992164201201)]
theorem point_links_checked40401 : (cuts40401.take 1).map (fun c => (5299372033-1+2*2^10*c.k,108991583691362+c.lower,108991969271395+c.upper)) = pointBounds40401 := by
 decide +kernel
def cuts40402 : List PrefixCut := [⟨57,276133774,276133939⟩,
⟨64,311028495,311028681⟩]
theorem checked40402 : checkPrefixCuts (2^48) 5299503105 10 Manual.Count131072.C040402.packed 64 cuts40402 = true := by
 decide +kernel
def pointBounds40402 : List (Nat × Nat × Nat) := [(5299619840,108992171020709,108992556601096)]
theorem point_links_checked40402 : (cuts40402.take 1).map (fun c => (5299503105-1+2*2^10*c.k,108991894886935+c.lower,108992280467157+c.upper)) = pointBounds40402 := by
 decide +kernel
def cuts40403 : List PrefixCut := [⟨64,312242370,312242551⟩]
theorem checked40403 : checkPrefixCuts (2^48) 5299634177 10 Manual.Count131072.C040403.packed 64 cuts40403 = true := by
 decide +kernel
def cuts40404 : List PrefixCut := [⟨10,49286749,49286777⟩,
⟨64,314518411,314518589⟩]
theorem checked40404 : checkPrefixCuts (2^48) 5299765249 10 Manual.Count131072.C040404.packed 64 cuts40404 = true := by
 decide +kernel
def pointBounds40404 : List (Nat × Nat × Nat) := [(5299785728,108992567444549,108992953025166)]
theorem point_links_checked40404 : (cuts40404.take 1).map (fun c => (5299765249-1+2*2^10*c.k,108992518157800+c.lower,108992903738389+c.upper)) = pointBounds40404 := by
 decide +kernel
def cuts40405 : List PrefixCut := [⟨27,134631905,134631985⟩,
⟨64,312864277,312864463⟩]
theorem checked40405 : checkPrefixCuts (2^48) 5299896321 10 Manual.Count131072.C040405.packed 64 cuts40405 = true := by
 decide +kernel
def pointBounds40405 : List (Nat × Nat × Nat) := [(5299951616,108992967308116,108993352888963)]
theorem point_links_checked40405 : (cuts40405.take 1).map (fun c => (5299896321-1+2*2^10*c.k,108992832676211+c.lower,108993218256978+c.upper)) = pointBounds40405 := by
 decide +kernel
def cuts40406 : List PrefixCut := [⟨44,211315715,211315842⟩,
⟨64,307705088,307705271⟩]
theorem checked40406 : checkPrefixCuts (2^48) 5300027393 10 Manual.Count131072.C040406.packed 64 cuts40406 = true := by
 decide +kernel
def pointBounds40406 : List (Nat × Nat × Nat) := [(5300117504,108993356856203,108993742437283)]
theorem point_links_checked40406 : (cuts40406.take 1).map (fun c => (5300027393-1+2*2^10*c.k,108993145540488+c.lower,108993531121441+c.upper)) = pointBounds40406 := by
 decide +kernel
def cuts40407 : List PrefixCut := [⟨61,299678595,299678774⟩,
⟨64,314282635,314282823⟩]
theorem checked40407 : checkPrefixCuts (2^48) 5300158465 10 Manual.Count131072.C040407.packed 64 cuts40407 = true := by
 decide +kernel
def pointBounds40407 : List (Nat × Nat × Nat) := [(5300283392,108993752924171,108994138505486)]
theorem point_links_checked40407 : (cuts40407.take 1).map (fun c => (5300158465-1+2*2^10*c.k,108993453245576+c.lower,108993838826712+c.upper)) = pointBounds40407 := by
 decide +kernel
def cuts40408 : List PrefixCut := [⟨64,313159690,313159878⟩]
theorem checked40408 : checkPrefixCuts (2^48) 5300289537 10 Manual.Count131072.C040408.packed 64 cuts40408 = true := by
 decide +kernel
def cuts40409 : List PrefixCut := [⟨14,66858073,66858111⟩,
⟨64,310656016,310656198⟩]
theorem checked40409 : checkPrefixCuts (2^48) 5300420609 10 Manual.Count131072.C040409.packed 64 cuts40409 = true := by
 decide +kernel
def pointBounds40409 : List (Nat × Nat × Nat) := [(5300449280,108994147545974,108994533127524)]
theorem point_links_checked40409 : (cuts40409.take 1).map (fun c => (5300420609-1+2*2^10*c.k,108994080687901+c.lower,108994466269413+c.upper)) = pointBounds40409 := by
 decide +kernel
def cuts40410 : List PrefixCut := [⟨31,150386639,150386727⟩,
⟨64,310595266,310595449⟩]
theorem checked40410 : checkPrefixCuts (2^48) 5300551681 10 Manual.Count131072.C040410.packed 64 cuts40410 = true := by
 decide +kernel
def pointBounds40410 : List (Nat × Nat × Nat) := [(5300615168,108994541730556,108994927312338)]
theorem point_links_checked40410 : (cuts40410.take 1).map (fun c => (5300551681-1+2*2^10*c.k,108994391343917+c.lower,108994776925611+c.upper)) = pointBounds40410 := by
 decide +kernel
def cuts40411 : List PrefixCut := [⟨48,230512033,230512174⟩,
⟨64,307720133,307720317⟩]
theorem checked40411 : checkPrefixCuts (2^48) 5300682753 10 Manual.Count131072.C040411.packed 64 cuts40411 = true := by
 decide +kernel
def pointBounds40411 : List (Nat × Nat × Nat) := [(5300781056,108994932451216,108995318033234)]
theorem point_links_checked40411 : (cuts40411.take 1).map (fun c => (5300682753-1+2*2^10*c.k,108994701939183+c.lower,108995087521060+c.upper)) = pointBounds40411 := by
 decide +kernel
def cuts40412 : List PrefixCut := [⟨64,311641899,311642086⟩]
theorem checked40412 : checkPrefixCuts (2^48) 5300813825 10 Manual.Count131072.C040412.packed 64 cuts40412 = true := by
 decide +kernel
def cuts40413 : List PrefixCut := [⟨1,4832008,4832011⟩,
⟨64,308554490,308554671⟩]
theorem checked40413 : checkPrefixCuts (2^48) 5300944897 10 Manual.Count131072.C040413.packed 64 cuts40413 = true := by
 decide +kernel
def pointBounds40413 : List (Nat × Nat × Nat) := [(5300946944,108995326133223,108995711715474)]
theorem point_links_checked40413 : (cuts40413.take 1).map (fun c => (5300944897-1+2*2^10*c.k,108995321301215+c.lower,108995706883463+c.upper)) = pointBounds40413 := by
 decide +kernel
def cuts40414 : List PrefixCut := [⟨18,87292303,87292357⟩,
⟨64,310776946,310777132⟩]
theorem checked40414 : checkPrefixCuts (2^48) 5301075969 10 Manual.Count131072.C040414.packed 64 cuts40414 = true := by
 decide +kernel
def pointBounds40414 : List (Nat × Nat × Nat) := [(5301112832,108995717148008,108996102730491)]
theorem point_links_checked40414 : (cuts40414.take 1).map (fun c => (5301075969-1+2*2^10*c.k,108995629855705+c.lower,108996015438134+c.upper)) = pointBounds40414 := by
 decide +kernel
def cuts40415 : List PrefixCut := [⟨35,170066544,170066646⟩,
⟨64,309866617,309866802⟩]
theorem checked40415 : checkPrefixCuts (2^48) 5301207041 10 Manual.Count131072.C040415.packed 64 cuts40415 = true := by
 decide +kernel
def pointBounds40415 : List (Nat × Nat × Nat) := [(5301278720,108996110699195,108996496281912)]
theorem point_links_checked40415 : (cuts40415.take 1).map (fun c => (5301207041-1+2*2^10*c.k,108995940632651+c.lower,108996326215266+c.upper)) = pointBounds40415 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S5.B000012
