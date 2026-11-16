import PlattAssemblyKernel
import PlattCertificates.Count131072.C046528
import PlattCertificates.Count131072.C046529
import PlattCertificates.Count131072.C046530
import PlattCertificates.Count131072.C046531
import PlattCertificates.Count131072.C046532
import PlattCertificates.Count131072.C046533
import PlattCertificates.Count131072.C046534
import PlattCertificates.Count131072.C046535
import PlattCertificates.Count131072.C046536
import PlattCertificates.Count131072.C046537
import PlattCertificates.Count131072.C046538
import PlattCertificates.Count131072.C046539
import PlattCertificates.Count131072.C046540
import PlattCertificates.Count131072.C046541
import PlattCertificates.Count131072.C046542
import PlattCertificates.Count131072.C046543
import PlattCertificates.Count131072.C046544
import PlattCertificates.Count131072.C046545
import PlattCertificates.Count131072.C046546
import PlattCertificates.Count131072.C046547
import PlattCertificates.Count131072.C046548
import PlattCertificates.Count131072.C046549
import PlattCertificates.Count131072.C046550
import PlattCertificates.Count131072.C046551
import PlattCertificates.Count131072.C046552
import PlattCertificates.Count131072.C046553
import PlattCertificates.Count131072.C046554
import PlattCertificates.Count131072.C046555
import PlattCertificates.Count131072.C046556
import PlattCertificates.Count131072.C046557
import PlattCertificates.Count131072.C046558
import PlattCertificates.Count131072.C046559
namespace ChenEffective.PlattWindow.Assembly.Prefix.S5.B000204
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts46528 : List PrefixCut := [⟨64,266737411,266737562⟩]
theorem checked46528 : checkPrefixCuts (2^48) 6102450177 10 Manual.Count131072.C046528.packed 64 cuts46528 = true := by
 decide +kernel
def cuts46529 : List PrefixCut := [⟨26,107560482,107560547⟩,
⟨64,264102652,264102811⟩]
theorem checked46529 : checkPrefixCuts (2^48) 6102581249 10 Manual.Count131072.C046529.packed 64 cuts46529 = true := by
 decide +kernel
def pointBounds46529 : List (Nat × Nat × Nat) := [(6102634496,110760159554261,110760546163736)]
theorem point_links_checked46529 : (cuts46529.take 1).map (fun c => (6102581249-1+2*2^10*c.k,110760051993779+c.lower,110760438603189+c.upper)) = pointBounds46529 := by
 decide +kernel
def cuts46530 : List PrefixCut := [⟨56,233887114,233887249⟩,
⟨64,267371680,267371833⟩]
theorem checked46530 : checkPrefixCuts (2^48) 6102712321 10 Manual.Count131072.C046530.packed 64 cuts46530 = true := by
 decide +kernel
def pointBounds46530 : List (Nat × Nat × Nat) := [(6102827008,110760549983545,110760936593249)]
theorem point_links_checked46530 : (cuts46530.take 1).map (fun c => (6102712321-1+2*2^10*c.k,110760316096431+c.lower,110760702706000+c.upper)) = pointBounds46530 := by
 decide +kernel
def cuts46531 : List PrefixCut := [⟨64,266674100,266674257⟩]
theorem checked46531 : checkPrefixCuts (2^48) 6102843393 10 Manual.Count131072.C046531.packed 64 cuts46531 = true := by
 decide +kernel
def cuts46532 : List PrefixCut := [⟨22,92195411,92195464⟩,
⟨64,265607639,265607790⟩]
theorem checked46532 : checkPrefixCuts (2^48) 6102974465 10 Manual.Count131072.C046532.packed 64 cuts46532 = true := by
 decide +kernel
def pointBounds46532 : List (Nat × Nat × Nat) := [(6103019520,110760942337622,110761328947554)]
theorem point_links_checked46532 : (cuts46532.take 1).map (fun c => (6102974465-1+2*2^10*c.k,110760850142211+c.lower,110761236752090+c.upper)) = pointBounds46532 := by
 decide +kernel
def cuts46533 : List PrefixCut := [⟨52,220682030,220682150⟩,
⟨64,271228505,271228655⟩]
theorem checked46533 : checkPrefixCuts (2^48) 6103105537 10 Manual.Count131072.C046533.packed 64 cuts46533 = true := by
 decide +kernel
def pointBounds46533 : List (Nat × Nat × Nat) := [(6103212032,110761336431880,110761723042030)]
theorem point_links_checked46533 : (cuts46533.take 1).map (fun c => (6103105537-1+2*2^10*c.k,110761115749850+c.lower,110761502359880+c.upper)) = pointBounds46533 := by
 decide +kernel
def cuts46534 : List PrefixCut := [⟨64,270945936,270946092⟩]
theorem checked46534 : checkPrefixCuts (2^48) 6103236609 10 Manual.Count131072.C046534.packed 64 cuts46534 = true := by
 decide +kernel
def cuts46535 : List PrefixCut := [⟨18,75125938,75125984⟩,
⟨64,267066269,267066423⟩]
theorem checked46535 : checkPrefixCuts (2^48) 6103367681 10 Manual.Count131072.C046535.packed 64 cuts46535 = true := by
 decide +kernel
def pointBounds46535 : List (Nat × Nat × Nat) := [(6103404544,110761733050229,110762119660611)]
theorem point_links_checked46535 : (cuts46535.take 1).map (fun c => (6103367681-1+2*2^10*c.k,110761657924291+c.lower,110762044534627+c.upper)) = pointBounds46535 := by
 decide +kernel
def cuts46536 : List PrefixCut := [⟨48,198485871,198485983⟩,
⟨64,263970742,263970892⟩]
theorem checked46536 : checkPrefixCuts (2^48) 6103498753 10 Manual.Count131072.C046536.packed 64 cuts46536 = true := by
 decide +kernel
def pointBounds46536 : List (Nat × Nat × Nat) := [(6103597056,110762123476431,110762510087033)]
theorem point_links_checked46536 : (cuts46536.take 1).map (fun c => (6103498753-1+2*2^10*c.k,110761924990560+c.lower,110762311601050+c.upper)) = pointBounds46536 := by
 decide +kernel
def cuts46537 : List PrefixCut := [⟨64,267977132,267977289⟩]
theorem checked46537 : checkPrefixCuts (2^48) 6103629825 10 Manual.Count131072.C046537.packed 64 cuts46537 = true := by
 decide +kernel
def cuts46538 : List PrefixCut := [⟨14,57459152,57459184⟩,
⟨64,267049069,267049220⟩]
theorem checked46538 : checkPrefixCuts (2^48) 6103760897 10 Manual.Count131072.C046538.packed 64 cuts46538 = true := by
 decide +kernel
def pointBounds46538 : List (Nat × Nat × Nat) := [(6103789568,110762514397586,110762901008415)]
theorem point_links_checked46538 : (cuts46538.take 1).map (fun c => (6103760897-1+2*2^10*c.k,110762456938434+c.lower,110762843549231+c.upper)) = pointBounds46538 := by
 decide +kernel
def cuts46539 : List PrefixCut := [⟨44,186806437,186806545⟩,
⟨64,272069681,272069838⟩]
theorem checked46539 : checkPrefixCuts (2^48) 6103891969 10 Manual.Count131072.C046539.packed 64 cuts46539 = true := by
 decide +kernel
def pointBounds46539 : List (Nat × Nat × Nat) := [(6103982080,110762910793940,110763297404996)]
theorem point_links_checked46539 : (cuts46539.take 1).map (fun c => (6103891969-1+2*2^10*c.k,110762723987503+c.lower,110763110598451+c.upper)) = pointBounds46539 := by
 decide +kernel
def cuts46540 : List PrefixCut := [⟨64,267268163,267268312⟩]
theorem checked46540 : checkPrefixCuts (2^48) 6104023041 10 Manual.Count131072.C046540.packed 64 cuts46540 = true := by
 decide +kernel
def cuts46541 : List PrefixCut := [⟨10,41961871,41961893⟩,
⟨64,269152988,269153132⟩]
theorem checked46541 : checkPrefixCuts (2^48) 6104154113 10 Manual.Count131072.C046541.packed 64 cuts46541 = true := by
 decide +kernel
def pointBounds46541 : List (Nat × Nat × Nat) := [(6104174592,110763305287218,110763691898494)]
theorem point_links_checked46541 : (cuts46541.take 1).map (fun c => (6104154113-1+2*2^10*c.k,110763263325347+c.lower,110763649936601+c.upper)) = pointBounds46541 := by
 decide +kernel
def cuts46542 : List PrefixCut := [⟨40,168488585,168488683⟩,
⟨64,270853296,270853451⟩]
theorem checked46542 : checkPrefixCuts (2^48) 6104285185 10 Manual.Count131072.C046542.packed 64 cuts46542 = true := by
 decide +kernel
def pointBounds46542 : List (Nat × Nat × Nat) := [(6104367104,110763700966920,110764087578416)]
theorem point_links_checked46542 : (cuts46542.take 1).map (fun c => (6104285185-1+2*2^10*c.k,110763532478335+c.lower,110763919089733+c.upper)) = pointBounds46542 := by
 decide +kernel
def cuts46543 : List PrefixCut := [⟨64,267758143,267758295⟩]
theorem checked46543 : checkPrefixCuts (2^48) 6104416257 10 Manual.Count131072.C046543.packed 64 cuts46543 = true := by
 decide +kernel
def cuts46544 : List PrefixCut := [⟨6,25406062,25406077⟩,
⟨64,268628462,268628618⟩]
theorem checked46544 : checkPrefixCuts (2^48) 6104547329 10 Manual.Count131072.C046544.packed 64 cuts46544 = true := by
 decide +kernel
def pointBounds46544 : List (Nat × Nat × Nat) := [(6104559616,110764096495836,110764483107556)]
theorem point_links_checked46544 : (cuts46544.take 1).map (fun c => (6104547329-1+2*2^10*c.k,110764071089774+c.lower,110764457701479+c.upper)) = pointBounds46544 := by
 decide +kernel
def cuts46545 : List PrefixCut := [⟨36,151879041,151879132⟩,
⟨64,268668800,268668957⟩]
theorem checked46545 : checkPrefixCuts (2^48) 6104678401 10 Manual.Count131072.C046545.packed 64 cuts46545 = true := by
 decide +kernel
def pointBounds46545 : List (Nat × Nat × Nat) := [(6104752128,110764491597277,110764878209229)]
theorem point_links_checked46545 : (cuts46545.take 1).map (fun c => (6104678401-1+2*2^10*c.k,110764339718236+c.lower,110764726330097+c.upper)) = pointBounds46545 := by
 decide +kernel
def cuts46546 : List PrefixCut := [⟨64,265527786,265527933⟩]
theorem checked46546 : checkPrefixCuts (2^48) 6104809473 10 Manual.Count131072.C046546.packed 64 cuts46546 = true := by
 decide +kernel
def cuts46547 : List PrefixCut := [⟨2,7699713,7699717⟩,
⟨64,268150111,268150263⟩]
theorem checked46547 : checkPrefixCuts (2^48) 6104940545 10 Manual.Count131072.C046547.packed 64 cuts46547 = true := by
 decide +kernel
def pointBounds46547 : List (Nat × Nat × Nat) := [(6104944640,110764881614535,110765268226704)]
theorem point_links_checked46547 : (cuts46547.take 1).map (fun c => (6104940545-1+2*2^10*c.k,110764873914822+c.lower,110765260526987+c.upper)) = pointBounds46547 := by
 decide +kernel
def cuts46548 : List PrefixCut := [⟨32,134072884,134072964⟩,
⟨64,269296944,269297103⟩]
theorem checked46548 : checkPrefixCuts (2^48) 6105071617 10 Manual.Count131072.C046548.packed 64 cuts46548 = true := by
 decide +kernel
def pointBounds46548 : List (Nat × Nat × Nat) := [(6105137152,110765276137817,110765662750214)]
theorem point_links_checked46548 : (cuts46548.take 1).map (fun c => (6105071617-1+2*2^10*c.k,110765142064933+c.lower,110765528677250+c.upper)) = pointBounds46548 := by
 decide +kernel
def cuts46549 : List PrefixCut := [⟨62,259655590,259655740⟩,
⟨64,268184669,268184824⟩]
theorem checked46549 : checkPrefixCuts (2^48) 6105202689 10 Manual.Count131072.C046549.packed 64 cuts46549 = true := by
 decide +kernel
def pointBounds46549 : List (Nat × Nat × Nat) := [(6105329664,110765671017467,110766057630093)]
theorem point_links_checked46549 : (cuts46549.take 1).map (fun c => (6105202689-1+2*2^10*c.k,110765411361877+c.lower,110765797974353+c.upper)) = pointBounds46549 := by
 decide +kernel
def cuts46550 : List PrefixCut := [⟨64,270668481,270668643⟩]
theorem checked46550 : checkPrefixCuts (2^48) 6105333761 10 Manual.Count131072.C046550.packed 64 cuts46550 = true := by
 decide +kernel
def cuts46551 : List PrefixCut := [⟨28,118528005,118528076⟩,
⟨64,270800978,270801136⟩]
theorem checked46551 : checkPrefixCuts (2^48) 6105464833 10 Manual.Count131072.C046551.packed 64 cuts46551 = true := by
 decide +kernel
def pointBounds46551 : List (Nat × Nat × Nat) := [(6105522176,110766068743032,110766455355896)]
theorem point_links_checked46551 : (cuts46551.take 1).map (fun c => (6105464833-1+2*2^10*c.k,110765950215027+c.lower,110766336827820+c.upper)) = pointBounds46551 := by
 decide +kernel
def cuts46552 : List PrefixCut := [⟨58,242489628,242489768⟩,
⟨64,268720637,268720792⟩]
theorem checked46552 : checkPrefixCuts (2^48) 6105595905 10 Manual.Count131072.C046552.packed 64 cuts46552 = true := by
 decide +kernel
def pointBounds46552 : List (Nat × Nat × Nat) := [(6105714688,110766463505633,110766850118724)]
theorem point_links_checked46552 : (cuts46552.take 1).map (fun c => (6105595905-1+2*2^10*c.k,110766221016005+c.lower,110766607628956+c.upper)) = pointBounds46552 := by
 decide +kernel
def cuts46553 : List PrefixCut := [⟨64,269867339,269867494⟩]
theorem checked46553 : checkPrefixCuts (2^48) 6105726977 10 Manual.Count131072.C046553.packed 64 cuts46553 = true := by
 decide +kernel
def cuts46554 : List PrefixCut := [⟨24,102985099,102985157⟩,
⟨64,273042364,273042522⟩]
theorem checked46554 : checkPrefixCuts (2^48) 6105858049 10 Manual.Count131072.C046554.packed 64 cuts46554 = true := by
 decide +kernel
def pointBounds46554 : List (Nat × Nat × Nat) := [(6105907200,110766862589080,110767249202399)]
theorem point_links_checked46554 : (cuts46554.take 1).map (fun c => (6105858049-1+2*2^10*c.k,110766759603981+c.lower,110767146217242+c.upper)) = pointBounds46554 := by
 decide +kernel
def cuts46555 : List PrefixCut := [⟨54,223896761,223896895⟩,
⟨64,265799166,265799323⟩]
theorem checked46555 : checkPrefixCuts (2^48) 6105989121 10 Manual.Count131072.C046555.packed 64 cuts46555 = true := by
 decide +kernel
def pointBounds46555 : List (Nat × Nat × Nat) := [(6106099712,110767256543106,110767643156659)]
theorem point_links_checked46555 : (cuts46555.take 1).map (fun c => (6105989121-1+2*2^10*c.k,110767032646345+c.lower,110767419259764+c.upper)) = pointBounds46555 := by
 decide +kernel
def cuts46556 : List PrefixCut := [⟨64,264318378,264318536⟩]
theorem checked46556 : checkPrefixCuts (2^48) 6106120193 10 Manual.Count131072.C046556.packed 64 cuts46556 = true := by
 decide +kernel
def cuts46557 : List PrefixCut := [⟨20,83940874,83940923⟩,
⟨64,267769868,267770027⟩]
theorem checked46557 : checkPrefixCuts (2^48) 6106251265 10 Manual.Count131072.C046557.packed 64 cuts46557 = true := by
 decide +kernel
def pointBounds46557 : List (Nat × Nat × Nat) := [(6106292224,110767646704763,110768033318546)]
theorem point_links_checked46557 : (cuts46557.take 1).map (fun c => (6106251265-1+2*2^10*c.k,110767562763889+c.lower,110767949377623+c.upper)) = pointBounds46557 := by
 decide +kernel
def cuts46558 : List PrefixCut := [⟨50,207979773,207979889⟩,
⟨64,265689856,265690005⟩]
theorem checked46558 : checkPrefixCuts (2^48) 6106382337 10 Manual.Count131072.C046558.packed 64 cuts46558 = true := by
 decide +kernel
def pointBounds46558 : List (Nat × Nat × Nat) := [(6106484736,110768038513530,110768425127539)]
theorem point_links_checked46558 : (cuts46558.take 1).map (fun c => (6106382337-1+2*2^10*c.k,110767830533757+c.lower,110768217147650+c.upper)) = pointBounds46558 := by
 decide +kernel
def cuts46559 : List PrefixCut := [⟨64,264992770,264992924⟩]
theorem checked46559 : checkPrefixCuts (2^48) 6106513409 10 Manual.Count131072.C046559.packed 64 cuts46559 = true := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S5.B000204
