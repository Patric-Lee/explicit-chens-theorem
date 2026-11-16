import PlattAssemblyKernel
import PlattCertificates.Count131072.C055632
import PlattCertificates.Count131072.C055633
import PlattCertificates.Count131072.C055634
import PlattCertificates.Count131072.C055635
import PlattCertificates.Count131072.C055636
import PlattCertificates.Count131072.C055637
import PlattCertificates.Count131072.C055638
import PlattCertificates.Count131072.C055639
import PlattCertificates.Count131072.C055640
import PlattCertificates.Count131072.C055641
import PlattCertificates.Count131072.C055642
import PlattCertificates.Count131072.C055643
import PlattCertificates.Count131072.C055644
import PlattCertificates.Count131072.C055645
import PlattCertificates.Count131072.C055646
import PlattCertificates.Count131072.C055647
import PlattCertificates.Count131072.C055648
import PlattCertificates.Count131072.C055649
import PlattCertificates.Count131072.C055650
import PlattCertificates.Count131072.C055651
import PlattCertificates.Count131072.C055652
import PlattCertificates.Count131072.C055653
import PlattCertificates.Count131072.C055654
import PlattCertificates.Count131072.C055655
import PlattCertificates.Count131072.C055656
import PlattCertificates.Count131072.C055657
import PlattCertificates.Count131072.C055658
import PlattCertificates.Count131072.C055659
import PlattCertificates.Count131072.C055660
import PlattCertificates.Count131072.C055661
import PlattCertificates.Count131072.C055662
import PlattCertificates.Count131072.C055663
namespace ChenEffective.PlattWindow.Assembly.Prefix.S6.B000176
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts55632 : List PrefixCut := [⟨64,222377570,222377697⟩]
theorem checked55632 : checkPrefixCuts (2^48) 7295729665 10 Manual.Count131072.C055632.packed 64 cuts55632 = true := by
 decide +kernel
def cuts55633 : List PrefixCut := [⟨25,89042521,89042570⟩,
⟨64,224958448,224958576⟩]
theorem checked55633 : checkPrefixCuts (2^48) 7295860737 10 Manual.Count131072.C055633.packed 64 cuts55633 = true := by
 decide +kernel
def pointBounds55633 : List (Nat × Nat × Nat) := [(7295911936,112982364081039,112982751956188)]
theorem point_links_checked55633 : (cuts55633.take 1).map (fun c => (7295860737-1+2*2^10*c.k,112982275038518+c.lower,112982662913618+c.upper)) = pointBounds55633 := by
 decide +kernel
def cuts55634 : List PrefixCut := [⟨64,224375713,224375836⟩]
theorem checked55634 : checkPrefixCuts (2^48) 7295991809 10 Manual.Count131072.C055634.packed 64 cuts55634 = true := by
 decide +kernel
def cuts55635 : List PrefixCut := [⟨9,30245657,30245674⟩,
⟨64,222095544,222095668⟩]
theorem checked55635 : checkPrefixCuts (2^48) 7296122881 10 Manual.Count131072.C055635.packed 64 cuts55635 = true := by
 decide +kernel
def pointBounds55635 : List (Nat × Nat × Nat) := [(7296141312,112982754618336,112983142493704)]
theorem point_links_checked55635 : (cuts55635.take 1).map (fun c => (7296122881-1+2*2^10*c.k,112982724372679+c.lower,112983112248030+c.upper)) = pointBounds55635 := by
 decide +kernel
def cuts55636 : List PrefixCut := [⟨57,197749259,197749374⟩,
⟨64,222708802,222708931⟩]
theorem checked55636 : checkPrefixCuts (2^48) 7296253953 10 Manual.Count131072.C055636.packed 64 cuts55636 = true := by
 decide +kernel
def pointBounds55636 : List (Nat × Nat × Nat) := [(7296370688,112983144217482,112983532093072)]
theorem point_links_checked55636 : (cuts55636.take 1).map (fun c => (7296253953-1+2*2^10*c.k,112982946468223+c.lower,112983334343698+c.upper)) = pointBounds55636 := by
 decide +kernel
def cuts55637 : List PrefixCut := [⟨64,220042993,220043121⟩]
theorem checked55637 : checkPrefixCuts (2^48) 7296385025 10 Manual.Count131072.C055637.packed 64 cuts55637 = true := by
 decide +kernel
def cuts55638 : List PrefixCut := [⟨41,144352867,144352949⟩,
⟨64,224513893,224514020⟩]
theorem checked55638 : checkPrefixCuts (2^48) 7296516097 10 Manual.Count131072.C055638.packed 64 cuts55638 = true := by
 decide +kernel
def pointBounds55638 : List (Nat × Nat × Nat) := [(7296600064,112983533572885,112983921448699)]
theorem point_links_checked55638 : (cuts55638.take 1).map (fun c => (7296516097-1+2*2^10*c.k,112983389220018+c.lower,112983777095750+c.upper)) = pointBounds55638 := by
 decide +kernel
def cuts55639 : List PrefixCut := [⟨64,223584029,223584155⟩]
theorem checked55639 : checkPrefixCuts (2^48) 7296647169 10 Manual.Count131072.C055639.packed 64 cuts55639 = true := by
 decide +kernel
def cuts55640 : List PrefixCut := [⟨25,85752432,85752481⟩,
⟨64,221419826,221419953⟩]
theorem checked55640 : checkPrefixCuts (2^48) 7296778241 10 Manual.Count131072.C055640.packed 64 cuts55640 = true := by
 decide +kernel
def pointBounds55640 : List (Nat × Nat × Nat) := [(7296829440,112983923070372,112984310946406)]
theorem point_links_checked55640 : (cuts55640.take 1).map (fun c => (7296778241-1+2*2^10*c.k,112983837317940+c.lower,112984225193925+c.upper)) = pointBounds55640 := by
 decide +kernel
def cuts55641 : List PrefixCut := [⟨64,224694642,224694768⟩]
theorem checked55641 : checkPrefixCuts (2^48) 7296909313 10 Manual.Count131072.C055641.packed 64 cuts55641 = true := by
 decide +kernel
def cuts55642 : List PrefixCut := [⟨9,30396150,30396168⟩,
⟨64,222376203,222376330⟩]
theorem checked55642 : checkPrefixCuts (2^48) 7297040385 10 Manual.Count131072.C055642.packed 64 cuts55642 = true := by
 decide +kernel
def pointBounds55642 : List (Nat × Nat × Nat) := [(7297058816,112984313828558,112984701704814)]
theorem point_links_checked55642 : (cuts55642.take 1).map (fun c => (7297040385-1+2*2^10*c.k,112984283432408+c.lower,112984671308646+c.upper)) = pointBounds55642 := by
 decide +kernel
def cuts55643 : List PrefixCut := [⟨57,196798647,196798757⟩,
⟨64,221022176,221022300⟩]
theorem checked55643 : checkPrefixCuts (2^48) 7297171457 10 Manual.Count131072.C055643.packed 64 cuts55643 = true := by
 decide +kernel
def pointBounds55643 : List (Nat × Nat × Nat) := [(7297288192,112984702607258,112985090483733)]
theorem point_links_checked55643 : (cuts55643.take 1).map (fun c => (7297171457-1+2*2^10*c.k,112984505808611+c.lower,112984893684976+c.upper)) = pointBounds55643 := by
 decide +kernel
def cuts55644 : List PrefixCut := [⟨64,221712502,221712627⟩]
theorem checked55644 : checkPrefixCuts (2^48) 7297302529 10 Manual.Count131072.C055644.packed 64 cuts55644 = true := by
 decide +kernel
def cuts55645 : List PrefixCut := [⟨41,142367569,142367649⟩,
⟨64,221399955,221400079⟩]
theorem checked55645 : checkPrefixCuts (2^48) 7297433601 10 Manual.Count131072.C055645.packed 64 cuts55645 = true := by
 decide +kernel
def pointBounds55645 : List (Nat × Nat × Nat) := [(7297517568,112985090910858,112985478787552)]
theorem point_links_checked55645 : (cuts55645.take 1).map (fun c => (7297433601-1+2*2^10*c.k,112984948543289+c.lower,112985336419903+c.upper)) = pointBounds55645 := by
 decide +kernel
def cuts55646 : List PrefixCut := [⟨64,221318830,221318952⟩]
theorem checked55646 : checkPrefixCuts (2^48) 7297564673 10 Manual.Count131072.C055646.packed 64 cuts55646 = true := by
 decide +kernel
def cuts55647 : List PrefixCut := [⟨25,87207318,87207368⟩,
⟨64,224477591,224477719⟩]
theorem checked55647 : checkPrefixCuts (2^48) 7297695745 10 Manual.Count131072.C055647.packed 64 cuts55647 = true := by
 decide +kernel
def pointBounds55647 : List (Nat × Nat × Nat) := [(7297746944,112985478469392,112985866346302)]
theorem point_links_checked55647 : (cuts55647.take 1).map (fun c => (7297695745-1+2*2^10*c.k,112985391262074+c.lower,112985779138934+c.upper)) = pointBounds55647 := by
 decide +kernel
def cuts55648 : List PrefixCut := [⟨64,223200792,223200918⟩]
theorem checked55648 : checkPrefixCuts (2^48) 7297826817 10 Manual.Count131072.C055648.packed 64 cuts55648 = true := by
 decide +kernel
def cuts55649 : List PrefixCut := [⟨9,31317984,31318002⟩,
⟨64,224816660,224816784⟩]
theorem checked55649 : checkPrefixCuts (2^48) 7297957889 10 Manual.Count131072.C055649.packed 64 cuts55649 = true := by
 decide +kernel
def pointBounds55649 : List (Nat × Nat × Nat) := [(7297976320,112985870258441,112986258135573)]
theorem point_links_checked55649 : (cuts55649.take 1).map (fun c => (7297957889-1+2*2^10*c.k,112985838940457+c.lower,112986226817571+c.upper)) = pointBounds55649 := by
 decide +kernel
def cuts55650 : List PrefixCut := [⟨57,195886847,195886960⟩,
⟨64,220145897,220146023⟩]
theorem checked55650 : checkPrefixCuts (2^48) 7298088961 10 Manual.Count131072.C055650.packed 64 cuts55650 = true := by
 decide +kernel
def pointBounds55650 : List (Nat × Nat × Nat) := [(7298205696,112986259643964,112986647521315)]
theorem point_links_checked55650 : (cuts55650.take 1).map (fun c => (7298088961-1+2*2^10*c.k,112986063757117+c.lower,112986451634355+c.upper)) = pointBounds55650 := by
 decide +kernel
def cuts55651 : List PrefixCut := [⟨64,221838899,221839024⟩]
theorem checked55651 : checkPrefixCuts (2^48) 7298220033 10 Manual.Count131072.C055651.packed 64 cuts55651 = true := by
 decide +kernel
def cuts55652 : List PrefixCut := [⟨41,143043871,143043952⟩,
⟨64,221873486,221873612⟩]
theorem checked55652 : checkPrefixCuts (2^48) 7298351105 10 Manual.Count131072.C055652.packed 64 cuts55652 = true := by
 decide +kernel
def pointBounds55652 : List (Nat × Nat × Nat) := [(7298435072,112986648785784,112987036663354)]
theorem point_links_checked55652 : (cuts55652.take 1).map (fun c => (7298351105-1+2*2^10*c.k,112986505741913+c.lower,112986893619402+c.upper)) = pointBounds55652 := by
 decide +kernel
def cuts55653 : List PrefixCut := [⟨64,219748364,219748489⟩]
theorem checked55653 : checkPrefixCuts (2^48) 7298482177 10 Manual.Count131072.C055653.packed 64 cuts55653 = true := by
 decide +kernel
def cuts55654 : List PrefixCut := [⟨25,88160495,88160544⟩,
⟨64,222366876,222367003⟩]
theorem checked55654 : checkPrefixCuts (2^48) 7298613249 10 Manual.Count131072.C055654.packed 64 cuts55654 = true := by
 decide +kernel
def pointBounds55654 : List (Nat × Nat × Nat) := [(7298664448,112987035524258,112987423402047)]
theorem point_links_checked55654 : (cuts55654.take 1).map (fun c => (7298613249-1+2*2^10*c.k,112986947363763+c.lower,112987335241503+c.upper)) = pointBounds55654 := by
 decide +kernel
def cuts55655 : List PrefixCut := [⟨64,220897400,220897523⟩]
theorem checked55655 : checkPrefixCuts (2^48) 7298744321 10 Manual.Count131072.C055655.packed 64 cuts55655 = true := by
 decide +kernel
def cuts55656 : List PrefixCut := [⟨9,31661125,31661142⟩,
⟨64,222397455,222397580⟩]
theorem checked55656 : checkPrefixCuts (2^48) 7298875393 10 Manual.Count131072.C055656.packed 64 cuts55656 = true := by
 decide +kernel
def pointBounds55656 : List (Nat × Nat × Nat) := [(7298893824,112987422289164,112987810167171)]
theorem point_links_checked55656 : (cuts55656.take 1).map (fun c => (7298875393-1+2*2^10*c.k,112987390628039+c.lower,112987778506029+c.upper)) = pointBounds55656 := by
 decide +kernel
def cuts55657 : List PrefixCut := [⟨57,198908706,198908821⟩,
⟨64,222162074,222162202⟩]
theorem checked55657 : checkPrefixCuts (2^48) 7299006465 10 Manual.Count131072.C055657.packed 64 cuts55657 = true := by
 decide +kernel
def pointBounds55657 : List (Nat × Nat × Nat) := [(7299123200,112987811934200,112988199812430)]
theorem point_links_checked55657 : (cuts55657.take 1).map (fun c => (7299006465-1+2*2^10*c.k,112987613025494+c.lower,112988000903609+c.upper)) = pointBounds55657 := by
 decide +kernel
def cuts55658 : List PrefixCut := [⟨64,222273769,222273895⟩]
theorem checked55658 : checkPrefixCuts (2^48) 7299137537 10 Manual.Count131072.C055658.packed 64 cuts55658 = true := by
 decide +kernel
def cuts55659 : List PrefixCut := [⟨41,142987331,142987412⟩,
⟨64,223503744,223503872⟩]
theorem checked55659 : checkPrefixCuts (2^48) 7299268609 10 Manual.Count131072.C055659.packed 64 cuts55659 = true := by
 decide +kernel
def pointBounds55659 : List (Nat × Nat × Nat) := [(7299352576,112988200448668,112988588327118)]
theorem point_links_checked55659 : (cuts55659.take 1).map (fun c => (7299268609-1+2*2^10*c.k,112988057461337+c.lower,112988445339706+c.upper)) = pointBounds55659 := by
 decide +kernel
def cuts55660 : List PrefixCut := [⟨64,217561330,217561456⟩]
theorem checked55660 : checkPrefixCuts (2^48) 7299399681 10 Manual.Count131072.C055660.packed 64 cuts55660 = true := by
 decide +kernel
def cuts55661 : List PrefixCut := [⟨25,89229106,89229158⟩,
⟨64,224922457,224922585⟩]
theorem checked55661 : checkPrefixCuts (2^48) 7299530753 10 Manual.Count131072.C055661.packed 64 cuts55661 = true := by
 decide +kernel
def pointBounds55661 : List (Nat × Nat × Nat) := [(7299581952,112988587755517,112988975634192)]
theorem point_links_checked55661 : (cuts55661.take 1).map (fun c => (7299530753-1+2*2^10*c.k,112988498526411+c.lower,112988886405034+c.upper)) = pointBounds55661 := by
 decide +kernel
def cuts55662 : List PrefixCut := [⟨64,224609948,224610073⟩]
theorem checked55662 : checkPrefixCuts (2^48) 7299661825 10 Manual.Count131072.C055662.packed 64 cuts55662 = true := by
 decide +kernel
def cuts55663 : List PrefixCut := [⟨9,31155874,31155893⟩,
⟨64,223256337,223256463⟩]
theorem checked55663 : checkPrefixCuts (2^48) 7299792897 10 Manual.Count131072.C055663.packed 64 cuts55663 = true := by
 decide +kernel
def pointBounds55663 : List (Nat × Nat × Nat) := [(7299811328,112988979214690,112989367093585)]
theorem point_links_checked55663 : (cuts55663.take 1).map (fun c => (7299792897-1+2*2^10*c.k,112988948058816+c.lower,112989335937692+c.upper)) = pointBounds55663 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S6.B000176
