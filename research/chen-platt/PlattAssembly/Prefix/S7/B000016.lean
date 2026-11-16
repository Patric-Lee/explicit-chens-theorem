import PlattAssemblyKernel
import PlattCertificates.Count131072.C060512
import PlattCertificates.Count131072.C060513
import PlattCertificates.Count131072.C060514
import PlattCertificates.Count131072.C060515
import PlattCertificates.Count131072.C060516
import PlattCertificates.Count131072.C060517
import PlattCertificates.Count131072.C060518
import PlattCertificates.Count131072.C060519
import PlattCertificates.Count131072.C060520
import PlattCertificates.Count131072.C060521
import PlattCertificates.Count131072.C060522
import PlattCertificates.Count131072.C060523
import PlattCertificates.Count131072.C060524
import PlattCertificates.Count131072.C060525
import PlattCertificates.Count131072.C060526
import PlattCertificates.Count131072.C060527
import PlattCertificates.Count131072.C060528
import PlattCertificates.Count131072.C060529
import PlattCertificates.Count131072.C060530
import PlattCertificates.Count131072.C060531
import PlattCertificates.Count131072.C060532
import PlattCertificates.Count131072.C060533
import PlattCertificates.Count131072.C060534
import PlattCertificates.Count131072.C060535
import PlattCertificates.Count131072.C060536
import PlattCertificates.Count131072.C060537
import PlattCertificates.Count131072.C060538
import PlattCertificates.Count131072.C060539
import PlattCertificates.Count131072.C060540
import PlattCertificates.Count131072.C060541
import PlattCertificates.Count131072.C060542
import PlattCertificates.Count131072.C060543
namespace ChenEffective.PlattWindow.Assembly.Prefix.S7.B000016
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts60512 : List PrefixCut := [⟨64,202572984,202573099⟩]
theorem checked60512 : checkPrefixCuts (2^48) 7935361025 10 Manual.Count131072.C060512.packed 64 cuts60512 = true := by
 decide +kernel
def cuts60513 : List PrefixCut := [⟨36,113327330,113327393⟩,
⟨64,201789311,201789426⟩]
theorem checked60513 : checkPrefixCuts (2^48) 7935492097 10 Manual.Count131072.C060513.packed 64 cuts60513 = true := by
 decide +kernel
def pointBounds60513 : List (Nat × Nat × Nat) := [(7935565824,114022002956585,114022391423957)]
theorem point_links_checked60513 : (cuts60513.take 1).map (fun c => (7935492097-1+2*2^10*c.k,114021889629255+c.lower,114022278096564+c.upper)) = pointBounds60513 := by
 decide +kernel
def cuts60514 : List PrefixCut := [⟨64,203133806,203133922⟩]
theorem checked60514 : checkPrefixCuts (2^48) 7935623169 10 Manual.Count131072.C060514.packed 64 cuts60514 = true := by
 decide +kernel
def cuts60515 : List PrefixCut := [⟨30,94808824,94808874⟩,
⟨64,200895932,200896043⟩]
theorem checked60515 : checkPrefixCuts (2^48) 7935754241 10 Manual.Count131072.C060515.packed 64 cuts60515 = true := by
 decide +kernel
def pointBounds60515 : List (Nat × Nat × Nat) := [(7935815680,114022389361196,114022777828786)]
theorem point_links_checked60515 : (cuts60515.take 1).map (fun c => (7935754241-1+2*2^10*c.k,114022294552372+c.lower,114022683019912+c.upper)) = pointBounds60515 := by
 decide +kernel
def cuts60516 : List PrefixCut := [⟨64,205645373,205645496⟩]
theorem checked60516 : checkPrefixCuts (2^48) 7935885313 10 Manual.Count131072.C060516.packed 64 cuts60516 = true := by
 decide +kernel
def cuts60517 : List PrefixCut := [⟨24,75050129,75050169⟩,
⟨64,202485322,202485435⟩]
theorem checked60517 : checkPrefixCuts (2^48) 7936016385 10 Manual.Count131072.C060517.packed 64 cuts60517 = true := by
 decide +kernel
def pointBounds60517 : List (Nat × Nat × Nat) := [(7936065536,114022776143806,114023164611620)]
theorem point_links_checked60517 : (cuts60517.take 1).map (fun c => (7936016385-1+2*2^10*c.k,114022701093677+c.lower,114023089561451+c.upper)) = pointBounds60517 := by
 decide +kernel
def cuts60518 : List PrefixCut := [⟨64,203333211,203333328⟩]
theorem checked60518 : checkPrefixCuts (2^48) 7936147457 10 Manual.Count131072.C060518.packed 64 cuts60518 = true := by
 decide +kernel
def cuts60519 : List PrefixCut := [⟨18,56498581,56498611⟩,
⟨64,201662908,201663023⟩]
theorem checked60519 : checkPrefixCuts (2^48) 7936278529 10 Manual.Count131072.C060519.packed 64 cuts60519 = true := by
 decide +kernel
def pointBounds60519 : List (Nat × Nat × Nat) := [(7936315392,114023163410791,114023551878825)]
theorem point_links_checked60519 : (cuts60519.take 1).map (fun c => (7936278529-1+2*2^10*c.k,114023106912210+c.lower,114023495380214+c.upper)) = pointBounds60519 := by
 decide +kernel
def cuts60520 : List PrefixCut := [⟨64,205560826,205560945⟩]
theorem checked60520 : checkPrefixCuts (2^48) 7936409601 10 Manual.Count131072.C060520.packed 64 cuts60520 = true := by
 decide +kernel
def cuts60521 : List PrefixCut := [⟨12,37948231,37948253⟩,
⟨64,205202780,205202899⟩]
theorem checked60521 : checkPrefixCuts (2^48) 7936540673 10 Manual.Count131072.C060521.packed 64 cuts60521 = true := by
 decide +kernel
def pointBounds60521 : List (Nat × Nat × Nat) := [(7936565248,114023552084175,114023940552435)]
theorem point_links_checked60521 : (cuts60521.take 1).map (fun c => (7936540673-1+2*2^10*c.k,114023514135944+c.lower,114023902604182+c.upper)) = pointBounds60521 := by
 decide +kernel
def cuts60522 : List PrefixCut := [⟨64,204277312,204277427⟩]
theorem checked60522 : checkPrefixCuts (2^48) 7936671745 10 Manual.Count131072.C060522.packed 64 cuts60522 = true := by
 decide +kernel
def cuts60523 : List PrefixCut := [⟨6,18299677,18299689⟩,
⟨64,202429795,202429915⟩]
theorem checked60523 : checkPrefixCuts (2^48) 7936802817 10 Manual.Count131072.C060523.packed 64 cuts60523 = true := by
 decide +kernel
def pointBounds60523 : List (Nat × Nat × Nat) := [(7936815104,114023941915713,114024330384197)]
theorem point_links_checked60523 : (cuts60523.take 1).map (fun c => (7936802817-1+2*2^10*c.k,114023923616036+c.lower,114024312084508+c.upper)) = pointBounds60523 := by
 decide +kernel
def cuts60524 : List PrefixCut := [⟨64,205440857,205440979⟩]
theorem checked60524 : checkPrefixCuts (2^48) 7936933889 10 Manual.Count131072.C060524.packed 64 cuts60524 = true := by
 decide +kernel
def pointBounds60524 : List (Nat × Nat × Nat) := [(7937064960,114024331486688,114024719955402)]
theorem point_links_checked60524 : (cuts60524.take 1).map (fun c => (7936933889-1+2*2^10*c.k,114024126045831+c.lower,114024514514423+c.upper)) = pointBounds60524 := by
 decide +kernel
def cuts60525 : List PrefixCut := [⟨64,205011923,205012042⟩]
theorem checked60525 : checkPrefixCuts (2^48) 7937064961 10 Manual.Count131072.C060525.packed 64 cuts60525 = true := by
 decide +kernel
def cuts60526 : List PrefixCut := [⟨58,182170849,182170957⟩,
⟨64,201745985,201746105⟩]
theorem checked60526 : checkPrefixCuts (2^48) 7937196033 10 Manual.Count131072.C060526.packed 64 cuts60526 = true := by
 decide +kernel
def pointBounds60526 : List (Nat × Nat × Nat) := [(7937314816,114024718669460,114025107138401)]
theorem point_links_checked60526 : (cuts60526.take 1).map (fun c => (7937196033-1+2*2^10*c.k,114024536498611+c.lower,114024924967444+c.upper)) = pointBounds60526 := by
 decide +kernel
def cuts60527 : List PrefixCut := [⟨64,205359776,205359892⟩]
theorem checked60527 : checkPrefixCuts (2^48) 7937327105 10 Manual.Count131072.C060527.packed 64 cuts60527 = true := by
 decide +kernel
def cuts60528 : List PrefixCut := [⟨52,166420132,166420225⟩,
⟨64,203051405,203051520⟩]
theorem checked60528 : checkPrefixCuts (2^48) 7937458177 10 Manual.Count131072.C060528.packed 64 cuts60528 = true := by
 decide +kernel
def pointBounds60528 : List (Nat × Nat × Nat) := [(7937564672,114025110024504,114025498493666)]
theorem point_links_checked60528 : (cuts60528.take 1).map (fun c => (7937458177-1+2*2^10*c.k,114024943604372+c.lower,114025332073441+c.upper)) = pointBounds60528 := by
 decide +kernel
def cuts60529 : List PrefixCut := [⟨64,201133170,201133289⟩]
theorem checked60529 : checkPrefixCuts (2^48) 7937589249 10 Manual.Count131072.C060529.packed 64 cuts60529 = true := by
 decide +kernel
def cuts60530 : List PrefixCut := [⟨46,143826609,143826690⟩,
⟨64,201697195,201697311⟩]
theorem checked60530 : checkPrefixCuts (2^48) 7937720321 10 Manual.Count131072.C060530.packed 64 cuts60530 = true := by
 decide +kernel
def pointBounds60530 : List (Nat × Nat × Nat) := [(7937814528,114025491615556,114025880084940)]
theorem point_links_checked60530 : (cuts60530.take 1).map (fun c => (7937720321-1+2*2^10*c.k,114025347788947+c.lower,114025736258250+c.upper)) = pointBounds60530 := by
 decide +kernel
def cuts60531 : List PrefixCut := [⟨64,204707938,204708052⟩]
theorem checked60531 : checkPrefixCuts (2^48) 7937851393 10 Manual.Count131072.C060531.packed 64 cuts60531 = true := by
 decide +kernel
def cuts60532 : List PrefixCut := [⟨40,125205966,125206037⟩,
⟨64,202825221,202825337⟩]
theorem checked60532 : checkPrefixCuts (2^48) 7937982465 10 Manual.Count131072.C060532.packed 64 cuts60532 = true := by
 decide +kernel
def pointBounds60532 : List (Nat × Nat × Nat) := [(7938064384,114025879400046,114026267869650)]
theorem point_links_checked60532 : (cuts60532.take 1).map (fun c => (7937982465-1+2*2^10*c.k,114025754194080+c.lower,114026142663613+c.upper)) = pointBounds60532 := by
 decide +kernel
def cuts60533 : List PrefixCut := [⟨64,204736626,204736740⟩]
theorem checked60533 : checkPrefixCuts (2^48) 7938113537 10 Manual.Count131072.C060533.packed 64 cuts60533 = true := by
 decide +kernel
def cuts60534 : List PrefixCut := [⟨34,107898458,107898522⟩,
⟨64,205619690,205619809⟩]
theorem checked60534 : checkPrefixCuts (2^48) 7938244609 10 Manual.Count131072.C060534.packed 64 cuts60534 = true := by
 decide +kernel
def pointBounds60534 : List (Nat × Nat × Nat) := [(7938314240,114026269654385,114026658124212)]
theorem point_links_checked60534 : (cuts60534.take 1).map (fun c => (7938244609-1+2*2^10*c.k,114026161755927+c.lower,114026550225690+c.upper)) = pointBounds60534 := by
 decide +kernel
def cuts60535 : List PrefixCut := [⟨64,206219081,206219196⟩]
theorem checked60535 : checkPrefixCuts (2^48) 7938375681 10 Manual.Count131072.C060535.packed 64 cuts60535 = true := by
 decide +kernel
def cuts60536 : List PrefixCut := [⟨28,90946631,90946686⟩,
⟨64,203804635,203804757⟩]
theorem checked60536 : checkPrefixCuts (2^48) 7938506753 10 Manual.Count131072.C060536.packed 64 cuts60536 = true := by
 decide +kernel
def pointBounds60536 : List (Nat × Nat × Nat) := [(7938564096,114026664541329,114027053011381)]
theorem point_links_checked60536 : (cuts60536.take 1).map (fun c => (7938506753-1+2*2^10*c.k,114026573594698+c.lower,114026962064695+c.upper)) = pointBounds60536 := by
 decide +kernel
def cuts60537 : List PrefixCut := [⟨64,201142058,201142172⟩]
theorem checked60537 : checkPrefixCuts (2^48) 7938637825 10 Manual.Count131072.C060537.packed 64 cuts60537 = true := by
 decide +kernel
def cuts60538 : List PrefixCut := [⟨22,73286799,73286842⟩,
⟨64,208513473,208513591⟩]
theorem checked60538 : checkPrefixCuts (2^48) 7938768897 10 Manual.Count131072.C060538.packed 64 cuts60538 = true := by
 decide +kernel
def pointBounds60538 : List (Nat × Nat × Nat) := [(7938813952,114027051828190,114027440298466)]
theorem point_links_checked60538 : (cuts60538.take 1).map (fun c => (7938768897-1+2*2^10*c.k,114026978541391+c.lower,114027367011624+c.upper)) = pointBounds60538 := by
 decide +kernel
def cuts60539 : List PrefixCut := [⟨64,206701824,206701944⟩]
theorem checked60539 : checkPrefixCuts (2^48) 7938899969 10 Manual.Count131072.C060539.packed 64 cuts60539 = true := by
 decide +kernel
def cuts60540 : List PrefixCut := [⟨16,49707197,49707226⟩,
⟨64,202798446,202798563⟩]
theorem checked60540 : checkPrefixCuts (2^48) 7939031041 10 Manual.Count131072.C060540.packed 64 cuts60540 = true := by
 decide +kernel
def pointBounds60540 : List (Nat × Nat × Nat) := [(7939063808,114027443463885,114027831934385)]
theorem point_links_checked60540 : (cuts60540.take 1).map (fun c => (7939031041-1+2*2^10*c.k,114027393756688+c.lower,114027782227159+c.upper)) = pointBounds60540 := by
 decide +kernel
def cuts60541 : List PrefixCut := [⟨64,207297713,207297829⟩]
theorem checked60541 : checkPrefixCuts (2^48) 7939162113 10 Manual.Count131072.C060541.packed 64 cuts60541 = true := by
 decide +kernel
def cuts60542 : List PrefixCut := [⟨10,31837107,31837125⟩,
⟨64,202968998,202969113⟩]
theorem checked60542 : checkPrefixCuts (2^48) 7939293185 10 Manual.Count131072.C060542.packed 64 cuts60542 = true := by
 decide +kernel
def pointBounds60542 : List (Nat × Nat × Nat) := [(7939313664,114027835689954,114028224160676)]
theorem point_links_checked60542 : (cuts60542.take 1).map (fun c => (7939293185-1+2*2^10*c.k,114027803852847+c.lower,114028192323551+c.upper)) = pointBounds60542 := by
 decide +kernel
def cuts60543 : List PrefixCut := [⟨64,205624596,205624712⟩]
theorem checked60543 : checkPrefixCuts (2^48) 7939424257 10 Manual.Count131072.C060543.packed 64 cuts60543 = true := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S7.B000016
