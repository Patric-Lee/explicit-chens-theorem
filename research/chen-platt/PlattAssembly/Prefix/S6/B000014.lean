import PlattAssemblyKernel
import PlattCertificates.Count131072.C050448
import PlattCertificates.Count131072.C050449
import PlattCertificates.Count131072.C050450
import PlattCertificates.Count131072.C050451
import PlattCertificates.Count131072.C050452
import PlattCertificates.Count131072.C050453
import PlattCertificates.Count131072.C050454
import PlattCertificates.Count131072.C050455
import PlattCertificates.Count131072.C050456
import PlattCertificates.Count131072.C050457
import PlattCertificates.Count131072.C050458
import PlattCertificates.Count131072.C050459
import PlattCertificates.Count131072.C050460
import PlattCertificates.Count131072.C050461
import PlattCertificates.Count131072.C050462
import PlattCertificates.Count131072.C050463
import PlattCertificates.Count131072.C050464
import PlattCertificates.Count131072.C050465
import PlattCertificates.Count131072.C050466
import PlattCertificates.Count131072.C050467
import PlattCertificates.Count131072.C050468
import PlattCertificates.Count131072.C050469
import PlattCertificates.Count131072.C050470
import PlattCertificates.Count131072.C050471
import PlattCertificates.Count131072.C050472
import PlattCertificates.Count131072.C050473
import PlattCertificates.Count131072.C050474
import PlattCertificates.Count131072.C050475
import PlattCertificates.Count131072.C050476
import PlattCertificates.Count131072.C050477
import PlattCertificates.Count131072.C050478
import PlattCertificates.Count131072.C050479
namespace ChenEffective.PlattWindow.Assembly.Prefix.S6.B000014
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts50448 : List PrefixCut := [⟨24,91211749,91211799⟩,
⟨64,247682587,247682729⟩]
theorem checked50448 : checkPrefixCuts (2^48) 6616252417 10 Manual.Count131072.C050448.packed 64 cuts50448 = true := by
 decide +kernel
def pointBounds50448 : List (Nat × Nat × Nat) := [(6616301568,111767953465109,111768340650390)]
theorem point_links_checked50448 : (cuts50448.take 1).map (fun c => (6616252417-1+2*2^10*c.k,111767862253360+c.lower,111768249438591+c.upper)) = pointBounds50448 := by
 decide +kernel
def cuts50449 : List PrefixCut := [⟨61,232830769,232830902⟩,
⟨64,243636254,243636393⟩]
theorem checked50449 : checkPrefixCuts (2^48) 6616383489 10 Manual.Count131072.C050449.packed 64 cuts50449 = true := by
 decide +kernel
def pointBounds50449 : List (Nat × Nat × Nat) := [(6616508416,111768342766716,111768729952222)]
theorem point_links_checked50449 : (cuts50449.take 1).map (fun c => (6616383489-1+2*2^10*c.k,111768109935947+c.lower,111768497121320+c.upper)) = pointBounds50449 := by
 decide +kernel
def cuts50450 : List PrefixCut := [⟨64,248863939,248864076⟩]
theorem checked50450 : checkPrefixCuts (2^48) 6616514561 10 Manual.Count131072.C050450.packed 64 cuts50450 = true := by
 decide +kernel
def cuts50451 : List PrefixCut := [⟨34,129875226,129875301⟩,
⟨64,245370717,245370858⟩]
theorem checked50451 : checkPrefixCuts (2^48) 6616645633 10 Manual.Count131072.C050451.packed 64 cuts50451 = true := by
 decide +kernel
def pointBounds50451 : List (Nat × Nat × Nat) := [(6616715264,111768732311366,111769119497090)]
theorem point_links_checked50451 : (cuts50451.take 1).map (fun c => (6616645633-1+2*2^10*c.k,111768602436140+c.lower,111768989621789+c.upper)) = pointBounds50451 := by
 decide +kernel
def cuts50452 : List PrefixCut := [⟨64,247833148,247833290⟩]
theorem checked50452 : checkPrefixCuts (2^48) 6616776705 10 Manual.Count131072.C050452.packed 64 cuts50452 = true := by
 decide +kernel
def cuts50453 : List PrefixCut := [⟨7,26714298,26714313⟩,
⟨64,247232707,247232845⟩]
theorem checked50453 : checkPrefixCuts (2^48) 6616907777 10 Manual.Count131072.C050453.packed 64 cuts50453 = true := by
 decide +kernel
def pointBounds50453 : List (Nat × Nat × Nat) := [(6616922112,111769122354303,111769509540250)]
theorem point_links_checked50453 : (cuts50453.take 1).map (fun c => (6616907777-1+2*2^10*c.k,111769095640005+c.lower,111769482825937+c.upper)) = pointBounds50453 := by
 decide +kernel
def cuts50454 : List PrefixCut := [⟨44,167640706,167640799⟩,
⟨64,242378535,242378673⟩]
theorem checked50454 : checkPrefixCuts (2^48) 6617038849 10 Manual.Count131072.C050454.packed 64 cuts50454 = true := by
 decide +kernel
def pointBounds50454 : List (Nat × Nat × Nat) := [(6617128960,111769510513418,111769897699581)]
theorem point_links_checked50454 : (cuts50454.take 1).map (fun c => (6617038849-1+2*2^10*c.k,111769342872712+c.lower,111769730058782+c.upper)) = pointBounds50454 := by
 decide +kernel
def cuts50455 : List PrefixCut := [⟨64,248031081,248031222⟩]
theorem checked50455 : checkPrefixCuts (2^48) 6617169921 10 Manual.Count131072.C050455.packed 64 cuts50455 = true := by
 decide +kernel
def cuts50456 : List PrefixCut := [⟨17,66058558,66058597⟩,
⟨64,248579144,248579289⟩]
theorem checked50456 : checkPrefixCuts (2^48) 6617300993 10 Manual.Count131072.C050456.packed 64 cuts50456 = true := by
 decide +kernel
def pointBounds50456 : List (Nat × Nat × Nat) := [(6617335808,111769899340886,111770286527274)]
theorem point_links_checked50456 : (cuts50456.take 1).map (fun c => (6617300993-1+2*2^10*c.k,111769833282328+c.lower,111770220468677+c.upper)) = pointBounds50456 := by
 decide +kernel
def cuts50457 : List PrefixCut := [⟨54,211399011,211399129⟩,
⟨64,250658438,250658579⟩]
theorem checked50457 : checkPrefixCuts (2^48) 6617432065 10 Manual.Count131072.C050457.packed 64 cuts50457 = true := by
 decide +kernel
def pointBounds50457 : List (Nat × Nat × Nat) := [(6617542656,111770293260483,111770680447095)]
theorem point_links_checked50457 : (cuts50457.take 1).map (fun c => (6617432065-1+2*2^10*c.k,111770081861472+c.lower,111770469047966+c.upper)) = pointBounds50457 := by
 decide +kernel
def cuts50458 : List PrefixCut := [⟨64,244528557,244528692⟩]
theorem checked50458 : checkPrefixCuts (2^48) 6617563137 10 Manual.Count131072.C050458.packed 64 cuts50458 = true := by
 decide +kernel
def cuts50459 : List PrefixCut := [⟨27,100379068,100379127⟩,
⟨64,242269429,242269571⟩]
theorem checked50459 : checkPrefixCuts (2^48) 6617694209 10 Manual.Count131072.C050459.packed 64 cuts50459 = true := by
 decide +kernel
def pointBounds50459 : List (Nat × Nat × Nat) := [(6617749504,111770677427535,111771064614364)]
theorem point_links_checked50459 : (cuts50459.take 1).map (fun c => (6617694209-1+2*2^10*c.k,111770577048467+c.lower,111770964235237+c.upper)) = pointBounds50459 := by
 decide +kernel
def cuts50460 : List PrefixCut := [⟨64,243370509,243370648⟩]
theorem checked50460 : checkPrefixCuts (2^48) 6617825281 10 Manual.Count131072.C050460.packed 64 cuts50460 = true := by
 decide +kernel
def pointBounds50460 : List (Nat × Nat × Nat) := [(6617956352,111771062688405,111771449875456)]
theorem point_links_checked50460 : (cuts50460.take 1).map (fun c => (6617825281-1+2*2^10*c.k,111770819317896+c.lower,111771206504808+c.upper)) = pointBounds50460 := by
 decide +kernel
def cuts50461 : List PrefixCut := [⟨64,247959101,247959242⟩]
theorem checked50461 : checkPrefixCuts (2^48) 6617956353 10 Manual.Count131072.C050461.packed 64 cuts50461 = true := by
 decide +kernel
def cuts50462 : List PrefixCut := [⟨37,145455714,145455797⟩,
⟨64,249400231,249400372⟩]
theorem checked50462 : checkPrefixCuts (2^48) 6618087425 10 Manual.Count131072.C050462.packed 64 cuts50462 = true := by
 decide +kernel
def pointBounds50462 : List (Nat × Nat × Nat) := [(6618163200,111771456103220,111771843290495)]
theorem point_links_checked50462 : (cuts50462.take 1).map (fun c => (6618087425-1+2*2^10*c.k,111771310647506+c.lower,111771697834698+c.upper)) = pointBounds50462 := by
 decide +kernel
def cuts50463 : List PrefixCut := [⟨64,249437817,249437956⟩]
theorem checked50463 : checkPrefixCuts (2^48) 6618218497 10 Manual.Count131072.C050463.packed 64 cuts50463 = true := by
 decide +kernel
def cuts50464 : List PrefixCut := [⟨10,37085641,37085660⟩,
⟨64,241522453,241522590⟩]
theorem checked50464 : checkPrefixCuts (2^48) 6618349569 10 Manual.Count131072.C050464.packed 64 cuts50464 = true := by
 decide +kernel
def pointBounds50464 : List (Nat × Nat × Nat) := [(6618370048,111771846571195,111772233758686)]
theorem point_links_checked50464 : (cuts50464.take 1).map (fun c => (6618349569-1+2*2^10*c.k,111771809485554+c.lower,111772196673026+c.upper)) = pointBounds50464 := by
 decide +kernel
def cuts50465 : List PrefixCut := [⟨47,182914300,182914406⟩,
⟨64,248790010,248790156⟩]
theorem checked50465 : checkPrefixCuts (2^48) 6618480641 10 Manual.Count131072.C050465.packed 64 cuts50465 = true := by
 decide +kernel
def pointBounds50465 : List (Nat × Nat × Nat) := [(6618576896,111772233922307,111772621110022)]
theorem point_links_checked50465 : (cuts50465.take 1).map (fun c => (6618480641-1+2*2^10*c.k,111772051008007+c.lower,111772438195616+c.upper)) = pointBounds50465 := by
 decide +kernel
def cuts50466 : List PrefixCut := [⟨64,243086404,243086544⟩]
theorem checked50466 : checkPrefixCuts (2^48) 6618611713 10 Manual.Count131072.C050466.packed 64 cuts50466 = true := by
 decide +kernel
def cuts50467 : List PrefixCut := [⟨20,77271216,77271260⟩,
⟨64,246951511,246951658⟩]
theorem checked50467 : checkPrefixCuts (2^48) 6618742785 10 Manual.Count131072.C050467.packed 64 cuts50467 = true := by
 decide +kernel
def pointBounds50467 : List (Nat × Nat × Nat) := [(6618783744,111772620155637,111773007343576)]
theorem point_links_checked50467 : (cuts50467.take 1).map (fun c => (6618742785-1+2*2^10*c.k,111772542884421+c.lower,111772930072316+c.upper)) = pointBounds50467 := by
 decide +kernel
def cuts50468 : List PrefixCut := [⟨57,217519081,217519207⟩,
⟨64,245670832,245670975⟩]
theorem checked50468 : checkPrefixCuts (2^48) 6618873857 10 Manual.Count131072.C050468.packed 64 cuts50468 = true := by
 decide +kernel
def pointBounds50468 : List (Nat × Nat × Nat) := [(6618990592,111773007355013,111773394543181)]
theorem point_links_checked50468 : (cuts50468.take 1).map (fun c => (6618873857-1+2*2^10*c.k,111772789835932+c.lower,111773177023974+c.upper)) = pointBounds50468 := by
 decide +kernel
def cuts50469 : List PrefixCut := [⟨64,246601537,246601675⟩]
theorem checked50469 : checkPrefixCuts (2^48) 6619004929 10 Manual.Count131072.C050469.packed 64 cuts50469 = true := by
 decide +kernel
def cuts50470 : List PrefixCut := [⟨30,118004708,118004775⟩,
⟨64,248255099,248255240⟩]
theorem checked50470 : checkPrefixCuts (2^48) 6619136001 10 Manual.Count131072.C050470.packed 64 cuts50470 = true := by
 decide +kernel
def pointBounds50470 : List (Nat × Nat × Nat) := [(6619197440,111773400113009,111773787301399)]
theorem point_links_checked50470 : (cuts50470.take 1).map (fun c => (6619136001-1+2*2^10*c.k,111773282108301+c.lower,111773669296624+c.upper)) = pointBounds50470 := by
 decide +kernel
def cuts50471 : List PrefixCut := [⟨64,246421644,246421789⟩]
theorem checked50471 : checkPrefixCuts (2^48) 6619267073 10 Manual.Count131072.C050471.packed 64 cuts50471 = true := by
 decide +kernel
def cuts50472 : List PrefixCut := [⟨4,15435742,15435751⟩,
⟨64,247692453,247692588⟩]
theorem checked50472 : checkPrefixCuts (2^48) 6619398145 10 Manual.Count131072.C050472.packed 64 cuts50472 = true := by
 decide +kernel
def pointBounds50472 : List (Nat × Nat × Nat) := [(6619406336,111773792220786,111774179409404)]
theorem point_links_checked50472 : (cuts50472.take 1).map (fun c => (6619398145-1+2*2^10*c.k,111773776785044+c.lower,111774163973653+c.upper)) = pointBounds50472 := by
 decide +kernel
def cuts50473 : List PrefixCut := [⟨42,161114394,161114486⟩,
⟨64,247517463,247517606⟩]
theorem checked50473 : checkPrefixCuts (2^48) 6619529217 10 Manual.Count131072.C050473.packed 64 cuts50473 = true := by
 decide +kernel
def pointBounds50473 : List (Nat × Nat × Nat) := [(6619615232,111774185591891,111774572780727)]
theorem point_links_checked50473 : (cuts50473.take 1).map (fun c => (6619529217-1+2*2^10*c.k,111774024477497+c.lower,111774411666241+c.upper)) = pointBounds50473 := by
 decide +kernel
def cuts50474 : List PrefixCut := [⟨64,249936228,249936369⟩]
theorem checked50474 : checkPrefixCuts (2^48) 6619660289 10 Manual.Count131072.C050474.packed 64 cuts50474 = true := by
 decide +kernel
def cuts50475 : List PrefixCut := [⟨16,62079347,62079383⟩,
⟨64,246104514,246104655⟩]
theorem checked50475 : checkPrefixCuts (2^48) 6619791361 10 Manual.Count131072.C050475.packed 64 cuts50475 = true := by
 decide +kernel
def pointBounds50475 : List (Nat × Nat × Nat) := [(6619824128,111774584010535,111774971199599)]
theorem point_links_checked50475 : (cuts50475.take 1).map (fun c => (6619791361-1+2*2^10*c.k,111774521931188+c.lower,111774909120216+c.upper)) = pointBounds50475 := by
 decide +kernel
def cuts50476 : List PrefixCut := [⟨54,208215603,208215725⟩,
⟨64,247630335,247630480⟩]
theorem checked50476 : checkPrefixCuts (2^48) 6619922433 10 Manual.Count131072.C050476.packed 64 cuts50476 = true := by
 decide +kernel
def pointBounds50476 : List (Nat × Nat × Nat) := [(6620033024,111774976251305,111775363440596)]
theorem point_links_checked50476 : (cuts50476.take 1).map (fun c => (6619922433-1+2*2^10*c.k,111774768035702+c.lower,111775155224871+c.upper)) = pointBounds50476 := by
 decide +kernel
def cuts50477 : List PrefixCut := [⟨64,243628722,243628859⟩]
theorem checked50477 : checkPrefixCuts (2^48) 6620053505 10 Manual.Count131072.C050477.packed 64 cuts50477 = true := by
 decide +kernel
def cuts50478 : List PrefixCut := [⟨28,108632201,108632263⟩,
⟨64,248470853,248470995⟩]
theorem checked50478 : checkPrefixCuts (2^48) 6620184577 10 Manual.Count131072.C050478.packed 64 cuts50478 = true := by
 decide +kernel
def pointBounds50478 : List (Nat × Nat × Nat) := [(6620241920,111775367926960,111775755116473)]
theorem point_links_checked50478 : (cuts50478.take 1).map (fun c => (6620184577-1+2*2^10*c.k,111775259294759+c.lower,111775646484210+c.upper)) = pointBounds50478 := by
 decide +kernel
def cuts50479 : List PrefixCut := [⟨64,246340133,246340272⟩]
theorem checked50479 : checkPrefixCuts (2^48) 6620315649 10 Manual.Count131072.C050479.packed 64 cuts50479 = true := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S6.B000014
