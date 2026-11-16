import PlattAssemblyKernel
import PlattCertificates.Count131072.C045504
import PlattCertificates.Count131072.C045505
import PlattCertificates.Count131072.C045506
import PlattCertificates.Count131072.C045507
import PlattCertificates.Count131072.C045508
import PlattCertificates.Count131072.C045509
import PlattCertificates.Count131072.C045510
import PlattCertificates.Count131072.C045511
import PlattCertificates.Count131072.C045512
import PlattCertificates.Count131072.C045513
import PlattCertificates.Count131072.C045514
import PlattCertificates.Count131072.C045515
import PlattCertificates.Count131072.C045516
import PlattCertificates.Count131072.C045517
import PlattCertificates.Count131072.C045518
import PlattCertificates.Count131072.C045519
import PlattCertificates.Count131072.C045520
import PlattCertificates.Count131072.C045521
import PlattCertificates.Count131072.C045522
import PlattCertificates.Count131072.C045523
import PlattCertificates.Count131072.C045524
import PlattCertificates.Count131072.C045525
import PlattCertificates.Count131072.C045526
import PlattCertificates.Count131072.C045527
import PlattCertificates.Count131072.C045528
import PlattCertificates.Count131072.C045529
import PlattCertificates.Count131072.C045530
import PlattCertificates.Count131072.C045531
import PlattCertificates.Count131072.C045532
import PlattCertificates.Count131072.C045533
import PlattCertificates.Count131072.C045534
import PlattCertificates.Count131072.C045535
namespace ChenEffective.PlattWindow.Assembly.Prefix.S5.B000172
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts45504 : List PrefixCut := [⟨64,271981388,271981543⟩]
theorem checked45504 : checkPrefixCuts (2^48) 5968232449 10 Manual.Count131072.C045504.packed 64 cuts45504 = true := by
 decide +kernel
def cuts45505 : List PrefixCut := [⟨2,9243582,9243588⟩,
⟨64,273956136,273956297⟩]
theorem checked45505 : checkPrefixCuts (2^48) 5968363521 10 Manual.Count131072.C045505.packed 64 cuts45505 = true := by
 decide +kernel
def pointBounds45505 : List (Nat × Nat × Nat) := [(5968367616,110482092052020,110482478501742)]
theorem point_links_checked45505 : (cuts45505.take 1).map (fun c => (5968363521-1+2*2^10*c.k,110482082808438+c.lower,110482469258154+c.upper)) = pointBounds45505 := by
 decide +kernel
def cuts45506 : List PrefixCut := [⟨30,130727172,130727248⟩,
⟨64,274940483,274940640⟩]
theorem checked45506 : checkPrefixCuts (2^48) 5968494593 10 Manual.Count131072.C045506.packed 64 cuts45506 = true := by
 decide +kernel
def pointBounds45506 : List (Nat × Nat × Nat) := [(5968556032,110482487491746,110482873941699)]
theorem point_links_checked45506 : (cuts45506.take 1).map (fun c => (5968494593-1+2*2^10*c.k,110482356764574+c.lower,110482743214451+c.upper)) = pointBounds45506 := by
 decide +kernel
def cuts45507 : List PrefixCut := [⟨58,248525880,248526015⟩,
⟨64,273566825,273566977⟩]
theorem checked45507 : checkPrefixCuts (2^48) 5968625665 10 Manual.Count131072.C045507.packed 64 cuts45507 = true := by
 decide +kernel
def pointBounds45507 : List (Nat × Nat × Nat) := [(5968744448,110482880230937,110483266681106)]
theorem point_links_checked45507 : (cuts45507.take 1).map (fun c => (5968625665-1+2*2^10*c.k,110482631705057+c.lower,110483018155091+c.upper)) = pointBounds45507 := by
 decide +kernel
def cuts45508 : List PrefixCut := [⟨64,277191935,277192095⟩]
theorem checked45508 : checkPrefixCuts (2^48) 5968756737 10 Manual.Count131072.C045508.packed 64 cuts45508 = true := by
 decide +kernel
def cuts45509 : List PrefixCut := [⟨22,92285912,92285966⟩,
⟨64,274733697,274733853⟩]
theorem checked45509 : checkPrefixCuts (2^48) 5968887809 10 Manual.Count131072.C045509.packed 64 cuts45509 = true := by
 decide +kernel
def pointBounds45509 : List (Nat × Nat × Nat) := [(5968932864,110483274749729,110483661200129)]
theorem point_links_checked45509 : (cuts45509.take 1).map (fun c => (5968887809-1+2*2^10*c.k,110483182463817+c.lower,110483568914163+c.upper)) = pointBounds45509 := by
 decide +kernel
def cuts45510 : List PrefixCut := [⟨50,217434341,217434463⟩,
⟨64,278735911,278736068⟩]
theorem checked45510 : checkPrefixCuts (2^48) 5969018881 10 Manual.Count131072.C045510.packed 64 cuts45510 = true := by
 decide +kernel
def pointBounds45510 : List (Nat × Nat × Nat) := [(5969121280,110483674631855,110484061082479)]
theorem point_links_checked45510 : (cuts45510.take 1).map (fun c => (5969018881-1+2*2^10*c.k,110483457197514+c.lower,110483843648016+c.upper)) = pointBounds45510 := by
 decide +kernel
def cuts45511 : List PrefixCut := [⟨64,271750947,271751104⟩]
theorem checked45511 : checkPrefixCuts (2^48) 5969149953 10 Manual.Count131072.C045511.packed 64 cuts45511 = true := by
 decide +kernel
def cuts45512 : List PrefixCut := [⟨14,61724309,61724346⟩,
⟨64,275894462,275894621⟩]
theorem checked45512 : checkPrefixCuts (2^48) 5969281025 10 Manual.Count131072.C045512.packed 64 cuts45512 = true := by
 decide +kernel
def pointBounds45512 : List (Nat × Nat × Nat) := [(5969309696,110484069408681,110484455859534)]
theorem point_links_checked45512 : (cuts45512.take 1).map (fun c => (5969281025-1+2*2^10*c.k,110484007684372+c.lower,110484394135188+c.upper)) = pointBounds45512 := by
 decide +kernel
def cuts45513 : List PrefixCut := [⟨42,182197367,182197476⟩,
⟨64,277302975,277303136⟩]
theorem checked45513 : checkPrefixCuts (2^48) 5969412097 10 Manual.Count131072.C045513.packed 64 cuts45513 = true := by
 decide +kernel
def pointBounds45513 : List (Nat × Nat × Nat) := [(5969498112,110484465776201,110484852227285)]
theorem point_links_checked45513 : (cuts45513.take 1).map (fun c => (5969412097-1+2*2^10*c.k,110484283578834+c.lower,110484670029809+c.upper)) = pointBounds45513 := by
 decide +kernel
def cuts45514 : List PrefixCut := [⟨64,273524801,273524953⟩]
theorem checked45514 : checkPrefixCuts (2^48) 5969543169 10 Manual.Count131072.C045514.packed 64 cuts45514 = true := by
 decide +kernel
def cuts45515 : List PrefixCut := [⟨6,24188334,24188349⟩,
⟨64,273565915,273566076⟩]
theorem checked45515 : checkPrefixCuts (2^48) 5969674241 10 Manual.Count131072.C045515.packed 64 cuts45515 = true := by
 decide +kernel
def pointBounds45515 : List (Nat × Nat × Nat) := [(5969686528,110484858594944,110485245046247)]
theorem point_links_checked45515 : (cuts45515.take 1).map (fun c => (5969674241-1+2*2^10*c.k,110484834406610+c.lower,110485220857898+c.upper)) = pointBounds45515 := by
 decide +kernel
def cuts45516 : List PrefixCut := [⟨34,143617337,143617419⟩,
⟨64,272003982,272004137⟩]
theorem checked45516 : checkPrefixCuts (2^48) 5969805313 10 Manual.Count131072.C045516.packed 64 cuts45516 = true := by
 decide +kernel
def pointBounds45516 : List (Nat × Nat × Nat) := [(5969874944,110485251589862,110485638041393)]
theorem point_links_checked45516 : (cuts45516.take 1).map (fun c => (5969805313-1+2*2^10*c.k,110485107972525+c.lower,110485494423974+c.upper)) = pointBounds45516 := by
 decide +kernel
def cuts45517 : List PrefixCut := [⟨62,264973011,264973159⟩,
⟨64,273365303,273365456⟩]
theorem checked45517 : checkPrefixCuts (2^48) 5969936385 10 Manual.Count131072.C045517.packed 64 cuts45517 = true := by
 decide +kernel
def pointBounds45517 : List (Nat × Nat × Nat) := [(5970063360,110485644949518,110486031401270)]
theorem point_links_checked45517 : (cuts45517.take 1).map (fun c => (5969936385-1+2*2^10*c.k,110485379976507+c.lower,110485766428111+c.upper)) = pointBounds45517 := by
 decide +kernel
def cuts45518 : List PrefixCut := [⟨64,274537975,274538135⟩]
theorem checked45518 : checkPrefixCuts (2^48) 5970067457 10 Manual.Count131072.C045518.packed 64 cuts45518 = true := by
 decide +kernel
def cuts45519 : List PrefixCut := [⟨26,110652706,110652766⟩,
⟨64,273164729,273164886⟩]
theorem checked45519 : checkPrefixCuts (2^48) 5970198529 10 Manual.Count131072.C045519.packed 64 cuts45519 = true := by
 decide +kernel
def pointBounds45519 : List (Nat × Nat × Nat) := [(5970251776,110486038532491,110486424984468)]
theorem point_links_checked45519 : (cuts45519.take 1).map (fun c => (5970198529-1+2*2^10*c.k,110485927879785+c.lower,110486314331702+c.upper)) = pointBounds45519 := by
 decide +kernel
def cuts45520 : List PrefixCut := [⟨54,231011425,231011568⟩,
⟨64,273205902,273206070⟩]
theorem checked45520 : checkPrefixCuts (2^48) 5970329601 10 Manual.Count131072.C045520.packed 64 cuts45520 = true := by
 decide +kernel
def pointBounds45520 : List (Nat × Nat × Nat) := [(5970440192,110486432055939,110486818508156)]
theorem point_links_checked45520 : (cuts45520.take 1).map (fun c => (5970329601-1+2*2^10*c.k,110486201044514+c.lower,110486587496588+c.upper)) = pointBounds45520 := by
 decide +kernel
def cuts45521 : List PrefixCut := [⟨64,277678572,277678732⟩]
theorem checked45521 : checkPrefixCuts (2^48) 5970460673 10 Manual.Count131072.C045521.packed 64 cuts45521 = true := by
 decide +kernel
def cuts45522 : List PrefixCut := [⟨18,78069478,78069521⟩,
⟨64,274042461,274042615⟩]
theorem checked45522 : checkPrefixCuts (2^48) 5970591745 10 Manual.Count131072.C045522.packed 64 cuts45522 = true := by
 decide +kernel
def pointBounds45522 : List (Nat × Nat × Nat) := [(5970628608,110486829998466,110487216450911)]
theorem point_links_checked45522 : (cuts45522.take 1).map (fun c => (5970591745-1+2*2^10*c.k,110486751928988+c.lower,110487138381390+c.upper)) = pointBounds45522 := by
 decide +kernel
def cuts45523 : List PrefixCut := [⟨46,199175562,199175678⟩,
⟨64,277949217,277949383⟩]
theorem checked45523 : checkPrefixCuts (2^48) 5970722817 10 Manual.Count131072.C045523.packed 64 cuts45523 = true := by
 decide +kernel
def pointBounds45523 : List (Nat × Nat × Nat) := [(5970817024,110487225147011,110487611599683)]
theorem point_links_checked45523 : (cuts45523.take 1).map (fun c => (5970722817-1+2*2^10*c.k,110487025971449+c.lower,110487412424005+c.upper)) = pointBounds45523 := by
 decide +kernel
def cuts45524 : List PrefixCut := [⟨64,275727455,275727618⟩]
theorem checked45524 : checkPrefixCuts (2^48) 5970853889 10 Manual.Count131072.C045524.packed 64 cuts45524 = true := by
 decide +kernel
def cuts45525 : List PrefixCut := [⟨10,41342099,41342124⟩,
⟨64,267849053,267849210⟩]
theorem checked45525 : checkPrefixCuts (2^48) 5970984961 10 Manual.Count131072.C045525.packed 64 cuts45525 = true := by
 decide +kernel
def pointBounds45525 : List (Nat × Nat × Nat) := [(5971005440,110487620990220,110488007443130)]
theorem point_links_checked45525 : (cuts45525.take 1).map (fun c => (5970984961-1+2*2^10*c.k,110487579648121+c.lower,110487966101006+c.upper)) = pointBounds45525 := by
 decide +kernel
def cuts45526 : List PrefixCut := [⟨38,163525557,163525649⟩,
⟨64,273122773,273122923⟩]
theorem checked45526 : checkPrefixCuts (2^48) 5971116033 10 Manual.Count131072.C045526.packed 64 cuts45526 = true := by
 decide +kernel
def pointBounds45526 : List (Nat × Nat × Nat) := [(5971193856,110488011022731,110488397475865)]
theorem point_links_checked45526 : (cuts45526.take 1).map (fun c => (5971116033-1+2*2^10*c.k,110487847497174+c.lower,110488233950216+c.upper)) = pointBounds45526 := by
 decide +kernel
def cuts45527 : List PrefixCut := [⟨64,272174017,272174169⟩]
theorem checked45527 : checkPrefixCuts (2^48) 5971247105 10 Manual.Count131072.C045527.packed 64 cuts45527 = true := by
 decide +kernel
def cuts45528 : List PrefixCut := [⟨2,8578993,8578998⟩,
⟨64,274854849,274855011⟩]
theorem checked45528 : checkPrefixCuts (2^48) 5971378177 10 Manual.Count131072.C045528.packed 64 cuts45528 = true := by
 decide +kernel
def pointBounds45528 : List (Nat × Nat × Nat) := [(5971382272,110488401372957,110488787826306)]
theorem point_links_checked45528 : (cuts45528.take 1).map (fun c => (5971378177-1+2*2^10*c.k,110488392793964+c.lower,110488779247308+c.upper)) = pointBounds45528 := by
 decide +kernel
def cuts45529 : List PrefixCut := [⟨30,129435638,129435711⟩,
⟨64,275932917,275933078⟩]
theorem checked45529 : checkPrefixCuts (2^48) 5971509249 10 Manual.Count131072.C045529.packed 64 cuts45529 = true := by
 decide +kernel
def pointBounds45529 : List (Nat × Nat × Nat) := [(5971570688,110488797084451,110489183538030)]
theorem point_links_checked45529 : (cuts45529.take 1).map (fun c => (5971509249-1+2*2^10*c.k,110488667648813+c.lower,110489054102319+c.upper)) = pointBounds45529 := by
 decide +kernel
def cuts45530 : List PrefixCut := [⟨58,249814423,249814563⟩,
⟨64,275596879,275597032⟩]
theorem checked45530 : checkPrefixCuts (2^48) 5971640321 10 Manual.Count131072.C045530.packed 64 cuts45530 = true := by
 decide +kernel
def pointBounds45530 : List (Nat × Nat × Nat) := [(5971759104,110489193396153,110489579849960)]
theorem point_links_checked45530 : (cuts45530.take 1).map (fun c => (5971640321-1+2*2^10*c.k,110488943581730+c.lower,110489330035397+c.upper)) = pointBounds45530 := by
 decide +kernel
def cuts45531 : List PrefixCut := [⟨64,276062188,276062348⟩]
theorem checked45531 : checkPrefixCuts (2^48) 5971771393 10 Manual.Count131072.C045531.packed 64 cuts45531 = true := by
 decide +kernel
def cuts45532 : List PrefixCut := [⟨22,93747590,93747647⟩,
⟨64,274500765,274500928⟩]
theorem checked45532 : checkPrefixCuts (2^48) 5971902465 10 Manual.Count131072.C045532.packed 64 cuts45532 = true := by
 decide +kernel
def pointBounds45532 : List (Nat × Nat × Nat) := [(5971947520,110489588988387,110489975442424)]
theorem point_links_checked45532 : (cuts45532.take 1).map (fun c => (5971902465-1+2*2^10*c.k,110489495240797+c.lower,110489881694777+c.upper)) = pointBounds45532 := by
 decide +kernel
def cuts45533 : List PrefixCut := [⟨50,215769206,215769326⟩,
⟨64,275013182,275013337⟩]
theorem checked45533 : checkPrefixCuts (2^48) 5972033537 10 Manual.Count131072.C045533.packed 64 cuts45533 = true := by
 decide +kernel
def pointBounds45533 : List (Nat × Nat × Nat) := [(5972135936,110489985510768,110490371965031)]
theorem point_links_checked45533 : (cuts45533.take 1).map (fun c => (5972033537-1+2*2^10*c.k,110489769741562+c.lower,110490156195705+c.upper)) = pointBounds45533 := by
 decide +kernel
def cuts45534 : List PrefixCut := [⟨64,277033812,277033968⟩]
theorem checked45534 : checkPrefixCuts (2^48) 5972164609 10 Manual.Count131072.C045534.packed 64 cuts45534 = true := by
 decide +kernel
def cuts45535 : List PrefixCut := [⟨14,59195266,59195300⟩,
⟨64,272503230,272503387⟩]
theorem checked45535 : checkPrefixCuts (2^48) 5972295681 10 Manual.Count131072.C045535.packed 64 cuts45535 = true := by
 decide +kernel
def pointBounds45535 : List (Nat × Nat × Nat) := [(5972324352,110490380983822,110490767438310)]
theorem point_links_checked45535 : (cuts45535.take 1).map (fun c => (5972295681-1+2*2^10*c.k,110490321788556+c.lower,110490708243010+c.upper)) = pointBounds45535 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S5.B000172
