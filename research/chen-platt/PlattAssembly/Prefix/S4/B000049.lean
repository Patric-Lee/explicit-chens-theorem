import PlattAssemblyKernel
import PlattCertificates.Count131072.C031568
import PlattCertificates.Count131072.C031569
import PlattCertificates.Count131072.C031570
import PlattCertificates.Count131072.C031571
import PlattCertificates.Count131072.C031572
import PlattCertificates.Count131072.C031573
import PlattCertificates.Count131072.C031574
import PlattCertificates.Count131072.C031575
import PlattCertificates.Count131072.C031576
import PlattCertificates.Count131072.C031577
import PlattCertificates.Count131072.C031578
import PlattCertificates.Count131072.C031579
import PlattCertificates.Count131072.C031580
import PlattCertificates.Count131072.C031581
import PlattCertificates.Count131072.C031582
import PlattCertificates.Count131072.C031583
import PlattCertificates.Count131072.C031584
import PlattCertificates.Count131072.C031585
import PlattCertificates.Count131072.C031586
import PlattCertificates.Count131072.C031587
import PlattCertificates.Count131072.C031588
import PlattCertificates.Count131072.C031589
import PlattCertificates.Count131072.C031590
import PlattCertificates.Count131072.C031591
import PlattCertificates.Count131072.C031592
import PlattCertificates.Count131072.C031593
import PlattCertificates.Count131072.C031594
import PlattCertificates.Count131072.C031595
import PlattCertificates.Count131072.C031596
import PlattCertificates.Count131072.C031597
import PlattCertificates.Count131072.C031598
import PlattCertificates.Count131072.C031599
namespace ChenEffective.PlattWindow.Assembly.Prefix.S4.B000049
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts31568 : List PrefixCut := [⟨1,3058318,3058320⟩,
⟨128,400633268,400633487⟩]
theorem checked31568 : checkPrefixCuts (2^48) 4141613057 9 Manual.Count131072.C031568.packed 128 cuts31568 = true := by
 decide +kernel
def pointBounds31568 : List (Nat × Nat × Nat) := [(4141614080,105875631693702,105876015379716),(4141744128,105876029268652,105876412954883)]
theorem point_links_checked31568 : (cuts31568.take 2).map (fun c => (4141613057-1+2*2^9*c.k,105875628635384+c.lower,105876012321396+c.upper)) = pointBounds31568 := by
 decide +kernel
def cuts31569 : List PrefixCut := [⟨127,404222529,404222767⟩,
⟨128,407212696,407212935⟩]
theorem checked31569 : checkPrefixCuts (2^48) 4141744129 9 Manual.Count131072.C031569.packed 128 cuts31569 = true := by
 decide +kernel
def pointBounds31569 : List (Nat × Nat × Nat) := [(4141874176,105876433491181,105876817177650)]
theorem point_links_checked31569 : (cuts31569.take 1).map (fun c => (4141744129-1+2*2^9*c.k,105876029268652+c.lower,105876412954883+c.upper)) = pointBounds31569 := by
 decide +kernel
def cuts31570 : List PrefixCut := [⟨126,395103568,395103790⟩,
⟨128,402442837,402443062⟩]
theorem checked31570 : checkPrefixCuts (2^48) 4141875201 9 Manual.Count131072.C031570.packed 128 cuts31570 = true := by
 decide +kernel
def pointBounds31570 : List (Nat × Nat × Nat) := [(4142004224,105876831584916,105877215271608)]
theorem point_links_checked31570 : (cuts31570.take 1).map (fun c => (4141875201-1+2*2^9*c.k,105876436481348+c.lower,105876820167818+c.upper)) = pointBounds31570 := by
 decide +kernel
def cuts31571 : List PrefixCut := [⟨125,392576746,392576957⟩,
⟨128,400323507,400323722⟩]
theorem checked31571 : checkPrefixCuts (2^48) 4142006273 9 Manual.Count131072.C031571.packed 128 cuts31571 = true := by
 decide +kernel
def pointBounds31571 : List (Nat × Nat × Nat) := [(4142134272,105877231500931,105877615187837)]
theorem point_links_checked31571 : (cuts31571.take 1).map (fun c => (4142006273-1+2*2^9*c.k,105876838924185+c.lower,105877222610880+c.upper)) = pointBounds31571 := by
 decide +kernel
def cuts31572 : List PrefixCut := [⟨124,386584542,386584762⟩,
⟨128,398815885,398816112⟩]
theorem checked31572 : checkPrefixCuts (2^48) 4142137345 9 Manual.Count131072.C031572.packed 128 cuts31572 = true := by
 decide +kernel
def pointBounds31572 : List (Nat × Nat × Nat) := [(4142264320,105877625832234,105878009519364)]
theorem point_links_checked31572 : (cuts31572.take 1).map (fun c => (4142137345-1+2*2^9*c.k,105877239247692+c.lower,105877622934602+c.upper)) = pointBounds31572 := by
 decide +kernel
def cuts31573 : List PrefixCut := [⟨123,384329978,384330193⟩,
⟨128,400162273,400162497⟩]
theorem checked31573 : checkPrefixCuts (2^48) 4142268417 9 Manual.Count131072.C031573.packed 128 cuts31573 = true := by
 decide +kernel
def pointBounds31573 : List (Nat × Nat × Nat) := [(4142394368,105878022393555,105878406080907)]
theorem point_links_checked31573 : (cuts31573.take 1).map (fun c => (4142268417-1+2*2^9*c.k,105877638063577+c.lower,105878021750714+c.upper)) = pointBounds31573 := by
 decide +kernel
def cuts31574 : List PrefixCut := [⟨122,390025573,390025789⟩,
⟨128,410613702,410613930⟩]
theorem checked31574 : checkPrefixCuts (2^48) 4142399489 9 Manual.Count131072.C031574.packed 128 cuts31574 = true := by
 decide +kernel
def pointBounds31574 : List (Nat × Nat × Nat) := [(4142524416,105878428251423,105878811939000)]
theorem point_links_checked31574 : (cuts31574.take 1).map (fun c => (4142399489-1+2*2^9*c.k,105878038225850+c.lower,105878421913211+c.upper)) = pointBounds31574 := by
 decide +kernel
def cuts31575 : List PrefixCut := [⟨121,375472666,375472869⟩,
⟨128,397011383,397011597⟩]
theorem checked31575 : checkPrefixCuts (2^48) 4142530561 9 Manual.Count131072.C031575.packed 128 cuts31575 = true := by
 decide +kernel
def pointBounds31575 : List (Nat × Nat × Nat) := [(4142654464,105878824312218,105879208000010)]
theorem point_links_checked31575 : (cuts31575.take 1).map (fun c => (4142530561-1+2*2^9*c.k,105878448839552+c.lower,105878832527141+c.upper)) = pointBounds31575 := by
 decide +kernel
def cuts31576 : List PrefixCut := [⟨120,377295330,377295547⟩,
⟨128,403589404,403589635⟩]
theorem checked31576 : checkPrefixCuts (2^48) 4142661633 9 Manual.Count131072.C031576.packed 128 cuts31576 = true := by
 decide +kernel
def pointBounds31576 : List (Nat × Nat × Nat) := [(4142784512,105879223146265,105879606834285)]
theorem point_links_checked31576 : (cuts31576.take 1).map (fun c => (4142661633-1+2*2^9*c.k,105878845850935+c.lower,105879229538738+c.upper)) = pointBounds31576 := by
 decide +kernel
def cuts31577 : List PrefixCut := [⟨119,371780131,371780345⟩,
⟨128,400111611,400111842⟩]
theorem checked31577 : checkPrefixCuts (2^48) 4142792705 9 Manual.Count131072.C031577.packed 128 cuts31577 = true := by
 decide +kernel
def pointBounds31577 : List (Nat × Nat × Nat) := [(4142914560,105879621220470,105880004908718)]
theorem point_links_checked31577 : (cuts31577.take 1).map (fun c => (4142792705-1+2*2^9*c.k,105879249440339+c.lower,105879633128373+c.upper)) = pointBounds31577 := by
 decide +kernel
def cuts31578 : List PrefixCut := [⟨118,369118730,369118940⟩,
⟨128,400098941,400099169⟩]
theorem checked31578 : checkPrefixCuts (2^48) 4142923777 9 Manual.Count131072.C031578.packed 128 cuts31578 = true := by
 decide +kernel
def pointBounds31578 : List (Nat × Nat × Nat) := [(4143044608,105880018670680,105880402359155)]
theorem point_links_checked31578 : (cuts31578.take 1).map (fun c => (4142923777-1+2*2^9*c.k,105879649551950+c.lower,105880033240215+c.upper)) = pointBounds31578 := by
 decide +kernel
def cuts31579 : List PrefixCut := [⟨117,364351475,364351682⟩,
⟨128,399067240,399067466⟩]
theorem checked31579 : checkPrefixCuts (2^48) 4143054849 9 Manual.Count131072.C031579.packed 128 cuts31579 = true := by
 decide +kernel
def pointBounds31579 : List (Nat × Nat × Nat) := [(4143174656,105880414002366,105880797691066)]
theorem point_links_checked31579 : (cuts31579.take 1).map (fun c => (4143054849-1+2*2^9*c.k,105880049650891+c.lower,105880433339384+c.upper)) = pointBounds31579 := by
 decide +kernel
def cuts31580 : List PrefixCut := [⟨116,369163383,369163592⟩,
⟨128,406935120,406935350⟩]
theorem checked31580 : checkPrefixCuts (2^48) 4143185921 9 Manual.Count131072.C031580.packed 128 cuts31580 = true := by
 decide +kernel
def pointBounds31580 : List (Nat × Nat × Nat) := [(4143304704,105880817881514,105881201570442)]
theorem point_links_checked31580 : (cuts31580.take 1).map (fun c => (4143185921-1+2*2^9*c.k,105880448718131+c.lower,105880832406850+c.upper)) = pointBounds31580 := by
 decide +kernel
def cuts31581 : List PrefixCut := [⟨115,360252446,360252656⟩,
⟨128,400876163,400876396⟩]
theorem checked31581 : checkPrefixCuts (2^48) 4143316993 9 Manual.Count131072.C031581.packed 128 cuts31581 = true := by
 decide +kernel
def pointBounds31581 : List (Nat × Nat × Nat) := [(4143434752,105881215905697,105881599594856)]
theorem point_links_checked31581 : (cuts31581.take 1).map (fun c => (4143316993-1+2*2^9*c.k,105880855653251+c.lower,105881239342200+c.upper)) = pointBounds31581 := by
 decide +kernel
def cuts31582 : List PrefixCut := [⟨114,359493862,359494062⟩,
⟨128,403376960,403377186⟩]
theorem checked31582 : checkPrefixCuts (2^48) 4143448065 9 Manual.Count131072.C031582.packed 128 cuts31582 = true := by
 decide +kernel
def pointBounds31582 : List (Nat × Nat × Nat) := [(4143564800,105881616023276,105881999712658)]
theorem point_links_checked31582 : (cuts31582.take 1).map (fun c => (4143448065-1+2*2^9*c.k,105881256529414+c.lower,105881640218596+c.upper)) = pointBounds31582 := by
 decide +kernel
def cuts31583 : List PrefixCut := [⟨113,353097158,353097358⟩,
⟨128,400647009,400647233⟩]
theorem checked31583 : checkPrefixCuts (2^48) 4143579137 9 Manual.Count131072.C031583.packed 128 cuts31583 = true := by
 decide +kernel
def pointBounds31583 : List (Nat × Nat × Nat) := [(4143694848,105882013003532,105882396693140)]
theorem point_links_checked31583 : (cuts31583.take 1).map (fun c => (4143579137-1+2*2^9*c.k,105881659906374+c.lower,105882043595782+c.upper)) = pointBounds31583 := by
 decide +kernel
def cuts31584 : List PrefixCut := [⟨112,347312212,347312406⟩,
⟨128,396287010,396287234⟩]
theorem checked31584 : checkPrefixCuts (2^48) 4143710209 9 Manual.Count131072.C031584.packed 128 cuts31584 = true := by
 decide +kernel
def pointBounds31584 : List (Nat × Nat × Nat) := [(4143824896,105882407865595,105882791555421)]
theorem point_links_checked31584 : (cuts31584.take 1).map (fun c => (4143710209-1+2*2^9*c.k,105882060553383+c.lower,105882444243015+c.upper)) = pointBounds31584 := by
 decide +kernel
def cuts31585 : List PrefixCut := [⟨111,351240938,351241135⟩,
⟨128,403678325,403678550⟩]
theorem checked31585 : checkPrefixCuts (2^48) 4143841281 9 Manual.Count131072.C031585.packed 128 cuts31585 = true := by
 decide +kernel
def pointBounds31585 : List (Nat × Nat × Nat) := [(4143954944,105882808081331,105883191771384)]
theorem point_links_checked31585 : (cuts31585.take 1).map (fun c => (4143841281-1+2*2^9*c.k,105882456840393+c.lower,105882840530249+c.upper)) = pointBounds31585 := by
 decide +kernel
def cuts31586 : List PrefixCut := [⟨110,353471370,353471560⟩,
⟨128,410186182,410186403⟩]
theorem checked31586 : checkPrefixCuts (2^48) 4143972353 9 Manual.Count131072.C031586.packed 128 cuts31586 = true := by
 decide +kernel
def pointBounds31586 : List (Nat × Nat × Nat) := [(4144084992,105883213990088,105883597680359)]
theorem point_links_checked31586 : (cuts31586.take 1).map (fun c => (4143972353-1+2*2^9*c.k,105882860518718+c.lower,105883244208799+c.upper)) = pointBounds31586 := by
 decide +kernel
def cuts31587 : List PrefixCut := [⟨109,340894839,340895031⟩,
⟨128,399917141,399917367⟩]
theorem checked31587 : checkPrefixCuts (2^48) 4144103425 9 Manual.Count131072.C031587.packed 128 cuts31587 = true := by
 decide +kernel
def pointBounds31587 : List (Nat × Nat × Nat) := [(4144215040,105883611599739,105883995290233)]
theorem point_links_checked31587 : (cuts31587.take 1).map (fun c => (4144103425-1+2*2^9*c.k,105883270704900+c.lower,105883654395202+c.upper)) = pointBounds31587 := by
 decide +kernel
def cuts31588 : List PrefixCut := [⟨108,344483790,344483985⟩,
⟨128,408258467,408258700⟩]
theorem checked31588 : checkPrefixCuts (2^48) 4144234497 9 Manual.Count131072.C031588.packed 128 cuts31588 = true := by
 decide +kernel
def pointBounds31588 : List (Nat × Nat × Nat) := [(4144345088,105884015105831,105884398796554)]
theorem point_links_checked31588 : (cuts31588.take 1).map (fun c => (4144234497-1+2*2^9*c.k,105883670622041+c.lower,105884054312569+c.upper)) = pointBounds31588 := by
 decide +kernel
def cuts31589 : List PrefixCut := [⟨107,337885006,337885201⟩,
⟨128,402268913,402269145⟩]
theorem checked31589 : checkPrefixCuts (2^48) 4144365569 9 Manual.Count131072.C031589.packed 128 cuts31589 = true := by
 decide +kernel
def pointBounds31589 : List (Nat × Nat × Nat) := [(4144475136,105884416765514,105884800456470)]
theorem point_links_checked31589 : (cuts31589.take 1).map (fun c => (4144365569-1+2*2^9*c.k,105884078880508+c.lower,105884462571269+c.upper)) = pointBounds31589 := by
 decide +kernel
def cuts31590 : List PrefixCut := [⟨106,332169571,332169765⟩,
⟨128,403206963,403207195⟩]
theorem checked31590 : checkPrefixCuts (2^48) 4144496641 9 Manual.Count131072.C031590.packed 128 cuts31590 = true := by
 decide +kernel
def pointBounds31590 : List (Nat × Nat × Nat) := [(4144605184,105884813318992,105885197010179)]
theorem point_links_checked31590 : (cuts31590.take 1).map (fun c => (4144496641-1+2*2^9*c.k,105884481149421+c.lower,105884864840414+c.upper)) = pointBounds31590 := by
 decide +kernel
def cuts31591 : List PrefixCut := [⟨105,331547905,331548088⟩,
⟨128,402990530,402990751⟩]
theorem checked31591 : checkPrefixCuts (2^48) 4144627713 9 Manual.Count131072.C031591.packed 128 cuts31591 = true := by
 decide +kernel
def pointBounds31591 : List (Nat × Nat × Nat) := [(4144735232,105885215904289,105885599595697)]
theorem point_links_checked31591 : (cuts31591.take 1).map (fun c => (4144627713-1+2*2^9*c.k,105884884356384+c.lower,105885268047609+c.upper)) = pointBounds31591 := by
 decide +kernel
def cuts31592 : List PrefixCut := [⟨104,331401676,331401860⟩,
⟨128,406441224,406441452⟩]
theorem checked31592 : checkPrefixCuts (2^48) 4144758785 9 Manual.Count131072.C031592.packed 128 cuts31592 = true := by
 decide +kernel
def pointBounds31592 : List (Nat × Nat × Nat) := [(4144865280,105885618748590,105886002440220)]
theorem point_links_checked31592 : (cuts31592.take 1).map (fun c => (4144758785-1+2*2^9*c.k,105885287346914+c.lower,105885671038360+c.upper)) = pointBounds31592 := by
 decide +kernel
def cuts31593 : List PrefixCut := [⟨103,322223589,322223772⟩,
⟨128,402625428,402625656⟩]
theorem checked31593 : checkPrefixCuts (2^48) 4144889857 9 Manual.Count131072.C031593.packed 128 cuts31593 = true := by
 decide +kernel
def pointBounds31593 : List (Nat × Nat × Nat) := [(4144995328,105886016011727,105886399703584)]
theorem point_links_checked31593 : (cuts31593.take 1).map (fun c => (4144889857-1+2*2^9*c.k,105885693788138+c.lower,105886077479812+c.upper)) = pointBounds31593 := by
 decide +kernel
def cuts31594 : List PrefixCut := [⟨102,319157674,319157845⟩,
⟨128,398198882,398199101⟩]
theorem checked31594 : checkPrefixCuts (2^48) 4145020929 9 Manual.Count131072.C031594.packed 128 cuts31594 = true := by
 decide +kernel
def pointBounds31594 : List (Nat × Nat × Nat) := [(4145125376,105886415571240,105886799263313)]
theorem point_links_checked31594 : (cuts31594.take 1).map (fun c => (4145020929-1+2*2^9*c.k,105886096413566+c.lower,105886480105468+c.upper)) = pointBounds31594 := by
 decide +kernel
def cuts31595 : List PrefixCut := [⟨101,314598088,314598264⟩,
⟨128,401717233,401717458⟩]
theorem checked31595 : checkPrefixCuts (2^48) 4145152001 9 Manual.Count131072.C031595.packed 128 cuts31595 = true := by
 decide +kernel
def pointBounds31595 : List (Nat × Nat × Nat) := [(4145255424,105886809210536,105887192902833)]
theorem point_links_checked31595 : (cuts31595.take 1).map (fun c => (4145152001-1+2*2^9*c.k,105886494612448+c.lower,105886878304569+c.upper)) = pointBounds31595 := by
 decide +kernel
def cuts31596 : List PrefixCut := [⟨100,316285712,316285889⟩,
⟨128,404556417,404556642⟩]
theorem checked31596 : checkPrefixCuts (2^48) 4145283073 9 Manual.Count131072.C031596.packed 128 cuts31596 = true := by
 decide +kernel
def pointBounds31596 : List (Nat × Nat × Nat) := [(4145385472,105887212615393,105887596307916)]
theorem point_links_checked31596 : (cuts31596.take 1).map (fun c => (4145283073-1+2*2^9*c.k,105886896329681+c.lower,105887280022027+c.upper)) = pointBounds31596 := by
 decide +kernel
def cuts31597 : List PrefixCut := [⟨99,314578249,314578424⟩,
⟨128,405562113,405562337⟩]
theorem checked31597 : checkPrefixCuts (2^48) 4145414145 9 Manual.Count131072.C031597.packed 128 cuts31597 = true := by
 decide +kernel
def pointBounds31597 : List (Nat × Nat × Nat) := [(4145515520,105887615464347,105887999157093)]
theorem point_links_checked31597 : (cuts31597.take 1).map (fun c => (4145414145-1+2*2^9*c.k,105887300886098+c.lower,105887684578669+c.upper)) = pointBounds31597 := by
 decide +kernel
def cuts31598 : List PrefixCut := [⟨98,305673816,305673989⟩,
⟨128,396994290,396994516⟩]
theorem checked31598 : checkPrefixCuts (2^48) 4145545217 9 Manual.Count131072.C031598.packed 128 cuts31598 = true := by
 decide +kernel
def pointBounds31598 : List (Nat × Nat × Nat) := [(4145645568,105888012122027,105888395814995)]
theorem point_links_checked31598 : (cuts31598.take 1).map (fun c => (4145545217-1+2*2^9*c.k,105887706448211+c.lower,105888090141006+c.upper)) = pointBounds31598 := by
 decide +kernel
def cuts31599 : List PrefixCut := [⟨97,305664224,305664399⟩,
⟨128,402752827,402753056⟩]
theorem checked31599 : checkPrefixCuts (2^48) 4145676289 9 Manual.Count131072.C031599.packed 128 cuts31599 = true := by
 decide +kernel
def pointBounds31599 : List (Nat × Nat × Nat) := [(4145775616,105888409106725,105888792799921)]
theorem point_links_checked31599 : (cuts31599.take 1).map (fun c => (4145676289-1+2*2^9*c.k,105888103442501+c.lower,105888487135522+c.upper)) = pointBounds31599 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S4.B000049
