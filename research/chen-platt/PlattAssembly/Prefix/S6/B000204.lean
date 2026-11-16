import PlattAssemblyKernel
import PlattCertificates.Count131072.C056528
import PlattCertificates.Count131072.C056529
import PlattCertificates.Count131072.C056530
import PlattCertificates.Count131072.C056531
import PlattCertificates.Count131072.C056532
import PlattCertificates.Count131072.C056533
import PlattCertificates.Count131072.C056534
import PlattCertificates.Count131072.C056535
import PlattCertificates.Count131072.C056536
import PlattCertificates.Count131072.C056537
import PlattCertificates.Count131072.C056538
import PlattCertificates.Count131072.C056539
import PlattCertificates.Count131072.C056540
import PlattCertificates.Count131072.C056541
import PlattCertificates.Count131072.C056542
import PlattCertificates.Count131072.C056543
import PlattCertificates.Count131072.C056544
import PlattCertificates.Count131072.C056545
import PlattCertificates.Count131072.C056546
import PlattCertificates.Count131072.C056547
import PlattCertificates.Count131072.C056548
import PlattCertificates.Count131072.C056549
import PlattCertificates.Count131072.C056550
import PlattCertificates.Count131072.C056551
import PlattCertificates.Count131072.C056552
import PlattCertificates.Count131072.C056553
import PlattCertificates.Count131072.C056554
import PlattCertificates.Count131072.C056555
import PlattCertificates.Count131072.C056556
import PlattCertificates.Count131072.C056557
import PlattCertificates.Count131072.C056558
import PlattCertificates.Count131072.C056559
namespace ChenEffective.PlattWindow.Assembly.Prefix.S6.B000204
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts56528 : List PrefixCut := [⟨64,221474562,221474685⟩]
theorem checked56528 : checkPrefixCuts (2^48) 7413170177 10 Manual.Count131072.C056528.packed 64 cuts56528 = true := by
 decide +kernel
def cuts56529 : List PrefixCut := [⟨38,131029991,131030066⟩,
⟨64,221470639,221470766⟩]
theorem checked56529 : checkPrefixCuts (2^48) 7413301249 10 Manual.Count131072.C056529.packed 64 cuts56529 = true := by
 decide +kernel
def pointBounds56529 : List (Nat × Nat × Nat) := [(7413379072,113180278194484,113180666181999)]
theorem point_links_checked56529 : (cuts56529.take 1).map (fun c => (7413301249-1+2*2^10*c.k,113180147164493+c.lower,113180535151933+c.upper)) = pointBounds56529 := by
 decide +kernel
def cuts56530 : List PrefixCut := [⟨64,222112178,222112303⟩]
theorem checked56530 : checkPrefixCuts (2^48) 7413432321 10 Manual.Count131072.C056530.packed 64 cuts56530 = true := by
 decide +kernel
def cuts56531 : List PrefixCut := [⟨24,80870624,80870671⟩,
⟨64,215653811,215653937⟩]
theorem checked56531 : checkPrefixCuts (2^48) 7413563393 10 Manual.Count131072.C056531.packed 64 cuts56531 = true := by
 decide +kernel
def pointBounds56531 : List (Nat × Nat × Nat) := [(7413612544,113180671617934,113181059605673)]
theorem point_links_checked56531 : (cuts56531.take 1).map (fun c => (7413563393-1+2*2^10*c.k,113180590747310+c.lower,113180978735002+c.upper)) = pointBounds56531 := by
 decide +kernel
def cuts56532 : List PrefixCut := [⟨64,221155160,221155284⟩]
theorem checked56532 : checkPrefixCuts (2^48) 7413694465 10 Manual.Count131072.C056532.packed 64 cuts56532 = true := by
 decide +kernel
def cuts56533 : List PrefixCut := [⟨10,33903784,33903803⟩,
⟨64,216253659,216253779⟩]
theorem checked56533 : checkPrefixCuts (2^48) 7413825537 10 Manual.Count131072.C056533.packed 64 cuts56533 = true := by
 decide +kernel
def pointBounds56533 : List (Nat × Nat × Nat) := [(7413846016,113181061460065,113181449448026)]
theorem point_links_checked56533 : (cuts56533.take 1).map (fun c => (7413825537-1+2*2^10*c.k,113181027556281+c.lower,113181415544223+c.upper)) = pointBounds56533 := by
 decide +kernel
def cuts56534 : List PrefixCut := [⟨60,205277999,205278114⟩,
⟨64,217958273,217958396⟩]
theorem checked56534 : checkPrefixCuts (2^48) 7413956609 10 Manual.Count131072.C056534.packed 64 cuts56534 = true := by
 decide +kernel
def pointBounds56534 : List (Nat × Nat × Nat) := [(7414079488,113181449087939,113181837076116)]
theorem point_links_checked56534 : (cuts56534.take 1).map (fun c => (7413956609-1+2*2^10*c.k,113181243809940+c.lower,113181631798002+c.upper)) = pointBounds56534 := by
 decide +kernel
def cuts56535 : List PrefixCut := [⟨64,219055369,219055491⟩]
theorem checked56535 : checkPrefixCuts (2^48) 7414087681 10 Manual.Count131072.C056535.packed 64 cuts56535 = true := by
 decide +kernel
def cuts56536 : List PrefixCut := [⟨46,158879180,158879269⟩,
⟨64,217912616,217912737⟩]
theorem checked56536 : checkPrefixCuts (2^48) 7414218753 10 Manual.Count131072.C056536.packed 64 cuts56536 = true := by
 decide +kernel
def pointBounds56536 : List (Nat × Nat × Nat) := [(7414312960,113181839702762,113182227691158)]
theorem point_links_checked56536 : (cuts56536.take 1).map (fun c => (7414218753-1+2*2^10*c.k,113181680823582+c.lower,113182068811889+c.upper)) = pointBounds56536 := by
 decide +kernel
def cuts56537 : List PrefixCut := [⟨64,219389304,219389424⟩]
theorem checked56537 : checkPrefixCuts (2^48) 7414349825 10 Manual.Count131072.C056537.packed 64 cuts56537 = true := by
 decide +kernel
def cuts56538 : List PrefixCut := [⟨32,111116801,111116863⟩,
⟨64,219878950,219879076⟩]
theorem checked56538 : checkPrefixCuts (2^48) 7414480897 10 Manual.Count131072.C056538.packed 64 cuts56538 = true := by
 decide +kernel
def pointBounds56538 : List (Nat × Nat × Nat) := [(7414546432,113182229242303,113182617230913)]
theorem point_links_checked56538 : (cuts56538.take 1).map (fun c => (7414480897-1+2*2^10*c.k,113182118125502+c.lower,113182506114050+c.upper)) = pointBounds56538 := by
 decide +kernel
def cuts56539 : List PrefixCut := [⟨64,218546378,218546504⟩]
theorem checked56539 : checkPrefixCuts (2^48) 7414611969 10 Manual.Count131072.C056539.packed 64 cuts56539 = true := by
 decide +kernel
def cuts56540 : List PrefixCut := [⟨18,61269732,61269770⟩,
⟨64,218770289,218770418⟩]
theorem checked56540 : checkPrefixCuts (2^48) 7414743041 10 Manual.Count131072.C056540.packed 64 cuts56540 = true := by
 decide +kernel
def pointBounds56540 : List (Nat × Nat × Nat) := [(7414779904,113182617820562,113183005809400)]
theorem point_links_checked56540 : (cuts56540.take 1).map (fun c => (7414743041-1+2*2^10*c.k,113182556550830+c.lower,113182944539630+c.upper)) = pointBounds56540 := by
 decide +kernel
def cuts56541 : List PrefixCut := [⟨64,217779447,217779573⟩]
theorem checked56541 : checkPrefixCuts (2^48) 7414874113 10 Manual.Count131072.C056541.packed 64 cuts56541 = true := by
 decide +kernel
def cuts56542 : List PrefixCut := [⟨4,13855456,13855464⟩,
⟨64,219673604,219673730⟩]
theorem checked56542 : checkPrefixCuts (2^48) 7415005185 10 Manual.Count131072.C056542.packed 64 cuts56542 = true := by
 decide +kernel
def pointBounds56542 : List (Nat × Nat × Nat) := [(7415013376,113183006956022,113183394945085)]
theorem point_links_checked56542 : (cuts56542.take 1).map (fun c => (7415005185-1+2*2^10*c.k,113182993100566+c.lower,113183381089621+c.upper)) = pointBounds56542 := by
 decide +kernel
def cuts56543 : List PrefixCut := [⟨54,186721415,186721519⟩,
⟨64,220239111,220239234⟩]
theorem checked56543 : checkPrefixCuts (2^48) 7415136257 10 Manual.Count131072.C056543.packed 64 cuts56543 = true := by
 decide +kernel
def pointBounds56543 : List (Nat × Nat × Nat) := [(7415246848,113183399495585,113183787484870)]
theorem point_links_checked56543 : (cuts56543.take 1).map (fun c => (7415136257-1+2*2^10*c.k,113183212774170+c.lower,113183600763351+c.upper)) = pointBounds56543 := by
 decide +kernel
def cuts56544 : List PrefixCut := [⟨64,218565044,218565165⟩]
theorem checked56544 : checkPrefixCuts (2^48) 7415267329 10 Manual.Count131072.C056544.packed 64 cuts56544 = true := by
 decide +kernel
def cuts56545 : List PrefixCut := [⟨40,136155178,136155255⟩,
⟨64,218409333,218409458⟩]
theorem checked56545 : checkPrefixCuts (2^48) 7415398401 10 Manual.Count131072.C056545.packed 64 cuts56545 = true := by
 decide +kernel
def pointBounds56545 : List (Nat × Nat × Nat) := [(7415480320,113183787733503,113184175723005)]
theorem point_links_checked56545 : (cuts56545.take 1).map (fun c => (7415398401-1+2*2^10*c.k,113183651578325+c.lower,113184039567750+c.upper)) = pointBounds56545 := by
 decide +kernel
def cuts56546 : List PrefixCut := [⟨64,220341306,220341429⟩]
theorem checked56546 : checkPrefixCuts (2^48) 7415529473 10 Manual.Count131072.C056546.packed 64 cuts56546 = true := by
 decide +kernel
def cuts56547 : List PrefixCut := [⟨26,88970467,88970518⟩,
⟨64,219160752,219160877⟩]
theorem checked56547 : checkPrefixCuts (2^48) 7415660545 10 Manual.Count131072.C056547.packed 64 cuts56547 = true := by
 decide +kernel
def pointBounds56547 : List (Nat × Nat × Nat) := [(7415713792,113184179299431,113184567289155)]
theorem point_links_checked56547 : (cuts56547.take 1).map (fun c => (7415660545-1+2*2^10*c.k,113184090328964+c.lower,113184478318637+c.upper)) = pointBounds56547 := by
 decide +kernel
def cuts56548 : List PrefixCut := [⟨64,219156898,219157020⟩]
theorem checked56548 : checkPrefixCuts (2^48) 7415791617 10 Manual.Count131072.C056548.packed 64 cuts56548 = true := by
 decide +kernel
def cuts56549 : List PrefixCut := [⟨12,41675045,41675069⟩,
⟨64,218887318,218887442⟩]
theorem checked56549 : checkPrefixCuts (2^48) 7415922689 10 Manual.Count131072.C056549.packed 64 cuts56549 = true := by
 decide +kernel
def pointBounds56549 : List (Nat × Nat × Nat) := [(7415947264,113184570321659,113184958311603)]
theorem point_links_checked56549 : (cuts56549.take 1).map (fun c => (7415922689-1+2*2^10*c.k,113184528646614+c.lower,113184916636534+c.upper)) = pointBounds56549 := by
 decide +kernel
def cuts56550 : List PrefixCut := [⟨62,212165568,212165686⟩,
⟨64,219035268,219035390⟩]
theorem checked56550 : checkPrefixCuts (2^48) 7416053761 10 Manual.Count131072.C056550.packed 64 cuts56550 = true := by
 decide +kernel
def pointBounds56550 : List (Nat × Nat × Nat) := [(7416180736,113184959699500,113185347689662)]
theorem point_links_checked56550 : (cuts56550.take 1).map (fun c => (7416053761-1+2*2^10*c.k,113184747533932+c.lower,113185135523976+c.upper)) = pointBounds56550 := by
 decide +kernel
def cuts56551 : List PrefixCut := [⟨64,216830066,216830193⟩]
theorem checked56551 : checkPrefixCuts (2^48) 7416184833 10 Manual.Count131072.C056551.packed 64 cuts56551 = true := by
 decide +kernel
def cuts56552 : List PrefixCut := [⟨48,166424850,166424946⟩,
⟨64,220925184,220925311⟩]
theorem checked56552 : checkPrefixCuts (2^48) 7416315905 10 Manual.Count131072.C056552.packed 64 cuts56552 = true := by
 decide +kernel
def pointBounds56552 : List (Nat × Nat × Nat) := [(7416414208,113185349824116,113185737814505)]
theorem point_links_checked56552 : (cuts56552.take 1).map (fun c => (7416315905-1+2*2^10*c.k,113185183399266+c.lower,113185571389559+c.upper)) = pointBounds56552 := by
 decide +kernel
def cuts56553 : List PrefixCut := [⟨64,218340493,218340619⟩]
theorem checked56553 : checkPrefixCuts (2^48) 7416446977 10 Manual.Count131072.C056553.packed 64 cuts56553 = true := by
 decide +kernel
def cuts56554 : List PrefixCut := [⟨34,118751645,118751714⟩,
⟨64,219247508,219247635⟩]
theorem checked56554 : checkPrefixCuts (2^48) 7416578049 10 Manual.Count131072.C056554.packed 64 cuts56554 = true := by
 decide +kernel
def pointBounds56554 : List (Nat × Nat × Nat) := [(7416647680,113185741416588,113186129407203)]
theorem point_links_checked56554 : (cuts56554.take 1).map (fun c => (7416578049-1+2*2^10*c.k,113185622664943+c.lower,113186010655489+c.upper)) = pointBounds56554 := by
 decide +kernel
def cuts56555 : List PrefixCut := [⟨64,223152589,223152716⟩]
theorem checked56555 : checkPrefixCuts (2^48) 7416709121 10 Manual.Count131072.C056555.packed 64 cuts56555 = true := by
 decide +kernel
def cuts56556 : List PrefixCut := [⟨20,69070236,69070275⟩,
⟨64,217911473,217911599⟩]
theorem checked56556 : checkPrefixCuts (2^48) 7416840193 10 Manual.Count131072.C056556.packed 64 cuts56556 = true := by
 decide +kernel
def pointBounds56556 : List (Nat × Nat × Nat) := [(7416881152,113186134135276,113186522126115)]
theorem point_links_checked56556 : (cuts56556.take 1).map (fun c => (7416840193-1+2*2^10*c.k,113186065065040+c.lower,113186453055840+c.upper)) = pointBounds56556 := by
 decide +kernel
def cuts56557 : List PrefixCut := [⟨64,219425612,219425734⟩]
theorem checked56557 : checkPrefixCuts (2^48) 7416971265 10 Manual.Count131072.C056557.packed 64 cuts56557 = true := by
 decide +kernel
def cuts56558 : List PrefixCut := [⟨6,19885489,19885502⟩,
⟨64,217296585,217296709⟩]
theorem checked56558 : checkPrefixCuts (2^48) 7417102337 10 Manual.Count131072.C056558.packed 64 cuts56558 = true := by
 decide +kernel
def pointBounds56558 : List (Nat × Nat × Nat) := [(7417114624,113186522287614,113186910278675)]
theorem point_links_checked56558 : (cuts56558.take 1).map (fun c => (7417102337-1+2*2^10*c.k,113186502402125+c.lower,113186890393173+c.upper)) = pointBounds56558 := by
 decide +kernel
def cuts56559 : List PrefixCut := [⟨56,190880845,190880956⟩,
⟨64,217254805,217254930⟩]
theorem checked56559 : checkPrefixCuts (2^48) 7417233409 10 Manual.Count131072.C056559.packed 64 cuts56559 = true := by
 decide +kernel
def pointBounds56559 : List (Nat × Nat × Nat) := [(7417348096,113186910579555,113187298570838)]
theorem point_links_checked56559 : (cuts56559.take 1).map (fun c => (7417233409-1+2*2^10*c.k,113186719698710+c.lower,113187107689882+c.upper)) = pointBounds56559 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S6.B000204
