import PlattAssemblyKernel
import PlattCertificates.Count131072.C072624
import PlattCertificates.Count131072.C072625
import PlattCertificates.Count131072.C072626
import PlattCertificates.Count131072.C072627
import PlattCertificates.Count131072.C072628
import PlattCertificates.Count131072.C072629
import PlattCertificates.Count131072.C072630
import PlattCertificates.Count131072.C072631
import PlattCertificates.Count131072.C072632
import PlattCertificates.Count131072.C072633
import PlattCertificates.Count131072.C072634
import PlattCertificates.Count131072.C072635
import PlattCertificates.Count131072.C072636
import PlattCertificates.Count131072.C072637
import PlattCertificates.Count131072.C072638
import PlattCertificates.Count131072.C072639
import PlattCertificates.Count131072.C072640
import PlattCertificates.Count131072.C072641
import PlattCertificates.Count131072.C072642
import PlattCertificates.Count131072.C072643
import PlattCertificates.Count131072.C072644
import PlattCertificates.Count131072.C072645
import PlattCertificates.Count131072.C072646
import PlattCertificates.Count131072.C072647
import PlattCertificates.Count131072.C072648
import PlattCertificates.Count131072.C072649
import PlattCertificates.Count131072.C072650
import PlattCertificates.Count131072.C072651
import PlattCertificates.Count131072.C072652
import PlattCertificates.Count131072.C072653
import PlattCertificates.Count131072.C072654
import PlattCertificates.Count131072.C072655
namespace ChenEffective.PlattWindow.Assembly.Prefix.S8.B000082
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts72624 : List PrefixCut := [⟨64,168684456,168684560⟩]
theorem checked72624 : checkPrefixCuts (2^48) 9522905089 10 Manual.Count131072.C072624.packed 64 cuts72624 = true := by
 decide +kernel
def cuts72625 : List PrefixCut := [⟨64,169214165,169214266⟩]
theorem checked72625 : checkPrefixCuts (2^48) 9523036161 10 Manual.Count131072.C072625.packed 64 cuts72625 = true := by
 decide +kernel
def cuts72626 : List PrefixCut := [⟨2,4876880,4876883⟩,
⟨64,165901507,165901613⟩]
theorem checked72626 : checkPrefixCuts (2^48) 9523167233 10 Manual.Count131072.C072626.packed 64 cuts72626 = true := by
 decide +kernel
def pointBounds72626 : List (Nat × Nat × Nat) := [(9523171328,116265076001312,116265465773466)]
theorem point_links_checked72626 : (cuts72626.take 1).map (fun c => (9523167233-1+2*2^10*c.k,116265071124432+c.lower,116265460896583+c.upper)) = pointBounds72626 := by
 decide +kernel
def cuts72627 : List PrefixCut := [⟨64,167672590,167672691⟩]
theorem checked72627 : checkPrefixCuts (2^48) 9523298305 10 Manual.Count131072.C072627.packed 64 cuts72627 = true := by
 decide +kernel
def cuts72628 : List PrefixCut := [⟨20,52432311,52432340⟩,
⟨64,170891864,170891960⟩]
theorem checked72628 : checkPrefixCuts (2^48) 9523429377 10 Manual.Count131072.C072628.packed 64 cuts72628 = true := by
 decide +kernel
def pointBounds72628 : List (Nat × Nat × Nat) := [(9523470336,116265457130840,116265846903227)]
theorem point_links_checked72628 : (cuts72628.take 1).map (fun c => (9523429377-1+2*2^10*c.k,116265404698529+c.lower,116265794470887+c.upper)) = pointBounds72628 := by
 decide +kernel
def cuts72629 : List PrefixCut := [⟨64,167638429,167638530⟩]
theorem checked72629 : checkPrefixCuts (2^48) 9523560449 10 Manual.Count131072.C072629.packed 64 cuts72629 = true := by
 decide +kernel
def cuts72630 : List PrefixCut := [⟨38,99334721,99334783⟩,
⟨64,167251895,167251999⟩]
theorem checked72630 : checkPrefixCuts (2^48) 9523691521 10 Manual.Count131072.C072630.packed 64 cuts72630 = true := by
 decide +kernel
def pointBounds72630 : List (Nat × Nat × Nat) := [(9523769344,116265842563543,116266232336160)]
theorem point_links_checked72630 : (cuts72630.take 1).map (fun c => (9523691521-1+2*2^10*c.k,116265743228822+c.lower,116266133001377+c.upper)) = pointBounds72630 := by
 decide +kernel
def cuts72631 : List PrefixCut := [⟨64,167781570,167781673⟩]
theorem checked72631 : checkPrefixCuts (2^48) 9523822593 10 Manual.Count131072.C072631.packed 64 cuts72631 = true := by
 decide +kernel
def cuts72632 : List PrefixCut := [⟨56,148510038,148510126⟩,
⟨64,168547673,168547774⟩]
theorem checked72632 : checkPrefixCuts (2^48) 9523953665 10 Manual.Count131072.C072632.packed 64 cuts72632 = true := by
 decide +kernel
def pointBounds72632 : List (Nat × Nat × Nat) := [(9524068352,116266226772325,116266616545175)]
theorem point_links_checked72632 : (cuts72632.take 1).map (fun c => (9523953665-1+2*2^10*c.k,116266078262287+c.lower,116266468035049+c.upper)) = pointBounds72632 := by
 decide +kernel
def cuts72633 : List PrefixCut := [⟨64,170495907,170496011⟩]
theorem checked72633 : checkPrefixCuts (2^48) 9524084737 10 Manual.Count131072.C072633.packed 64 cuts72633 = true := by
 decide +kernel
def cuts72634 : List PrefixCut := [⟨64,167419999,167420101⟩]
theorem checked72634 : checkPrefixCuts (2^48) 9524215809 10 Manual.Count131072.C072634.packed 64 cuts72634 = true := by
 decide +kernel
def cuts72635 : List PrefixCut := [⟨10,26302317,26302332⟩,
⟨64,167801898,167801997⟩]
theorem checked72635 : checkPrefixCuts (2^48) 9524346881 10 Manual.Count131072.C072635.packed 64 cuts72635 = true := by
 decide +kernel
def pointBounds72635 : List (Nat × Nat × Nat) := [(9524367360,116266611028183,116267000801267)]
theorem point_links_checked72635 : (cuts72635.take 1).map (fun c => (9524346881-1+2*2^10*c.k,116266584725866+c.lower,116266974498935+c.upper)) = pointBounds72635 := by
 decide +kernel
def cuts72636 : List PrefixCut := [⟨64,167976897,167976998⟩]
theorem checked72636 : checkPrefixCuts (2^48) 9524477953 10 Manual.Count131072.C072636.packed 64 cuts72636 = true := by
 decide +kernel
def cuts72637 : List PrefixCut := [⟨28,74619543,74619591⟩,
⟨64,169570409,169570516⟩]
theorem checked72637 : checkPrefixCuts (2^48) 9524609025 10 Manual.Count131072.C072637.packed 64 cuts72637 = true := by
 decide +kernel
def pointBounds72637 : List (Nat × Nat × Nat) := [(9524666368,116266995124204,116267384897521)]
theorem point_links_checked72637 : (cuts72637.take 1).map (fun c => (9524609025-1+2*2^10*c.k,116266920504661+c.lower,116267310277930+c.upper)) = pointBounds72637 := by
 decide +kernel
def cuts72638 : List PrefixCut := [⟨64,169627175,169627268⟩]
theorem checked72638 : checkPrefixCuts (2^48) 9524740097 10 Manual.Count131072.C072638.packed 64 cuts72638 = true := by
 decide +kernel
def cuts72639 : List PrefixCut := [⟨46,117998835,117998904⟩,
⟨64,166078668,166078767⟩]
theorem checked72639 : checkPrefixCuts (2^48) 9524871169 10 Manual.Count131072.C072639.packed 64 cuts72639 = true := by
 decide +kernel
def pointBounds72639 : List (Nat × Nat × Nat) := [(9524965376,116267377701080,116267767474618)]
theorem point_links_checked72639 : (cuts72639.take 1).map (fun c => (9524871169-1+2*2^10*c.k,116267259702245+c.lower,116267649475714+c.upper)) = pointBounds72639 := by
 decide +kernel
def cuts72640 : List PrefixCut := [⟨64,168085857,168085954⟩]
theorem checked72640 : checkPrefixCuts (2^48) 9525002241 10 Manual.Count131072.C072640.packed 64 cuts72640 = true := by
 decide +kernel
def cuts72641 : List PrefixCut := [⟨64,168851857,168851962⟩]
theorem checked72641 : checkPrefixCuts (2^48) 9525133313 10 Manual.Count131072.C072641.packed 64 cuts72641 = true := by
 decide +kernel
def pointBounds72641 : List (Nat × Nat × Nat) := [(9525264384,116267762718627,116268152492397)]
theorem point_links_checked72641 : (cuts72641.take 1).map (fun c => (9525133313-1+2*2^10*c.k,116267593866770+c.lower,116267983640435+c.upper)) = pointBounds72641 := by
 decide +kernel
def cuts72642 : List PrefixCut := [⟨64,168169888,168169990⟩]
theorem checked72642 : checkPrefixCuts (2^48) 9525264385 10 Manual.Count131072.C072642.packed 64 cuts72642 = true := by
 decide +kernel
def cuts72643 : List PrefixCut := [⟨64,170383802,170383902⟩]
theorem checked72643 : checkPrefixCuts (2^48) 9525395457 10 Manual.Count131072.C072643.packed 64 cuts72643 = true := by
 decide +kernel
def cuts72644 : List PrefixCut := [⟨18,48106553,48106582⟩,
⟨64,170085964,170086067⟩]
theorem checked72644 : checkPrefixCuts (2^48) 9525526529 10 Manual.Count131072.C072644.packed 64 cuts72644 = true := by
 decide +kernel
def pointBounds72644 : List (Nat × Nat × Nat) := [(9525563392,116268149378870,116268539152871)]
theorem point_links_checked72644 : (cuts72644.take 1).map (fun c => (9525526529-1+2*2^10*c.k,116268101272317+c.lower,116268491046289+c.upper)) = pointBounds72644 := by
 decide +kernel
def cuts72645 : List PrefixCut := [⟨64,166921891,166921998⟩]
theorem checked72645 : checkPrefixCuts (2^48) 9525657601 10 Manual.Count131072.C072645.packed 64 cuts72645 = true := by
 decide +kernel
def cuts72646 : List PrefixCut := [⟨36,95235169,95235225⟩,
⟨64,169401666,169401772⟩]
theorem checked72646 : checkPrefixCuts (2^48) 9525788673 10 Manual.Count131072.C072646.packed 64 cuts72646 = true := by
 decide +kernel
def pointBounds72646 : List (Nat × Nat × Nat) := [(9525862400,116268533515341,116268923289579)]
theorem point_links_checked72646 : (cuts72646.take 1).map (fun c => (9525788673-1+2*2^10*c.k,116268438280172+c.lower,116268828054354+c.upper)) = pointBounds72646 := by
 decide +kernel
def cuts72647 : List PrefixCut := [⟨64,168128763,168128866⟩]
theorem checked72647 : checkPrefixCuts (2^48) 9525919745 10 Manual.Count131072.C072647.packed 64 cuts72647 = true := by
 decide +kernel
def cuts72648 : List PrefixCut := [⟨54,142449643,142449727⟩,
⟨64,168894688,168894788⟩]
theorem checked72648 : checkPrefixCuts (2^48) 9526050817 10 Manual.Count131072.C072648.packed 64 cuts72648 = true := by
 decide +kernel
def pointBounds72648 : List (Nat × Nat × Nat) := [(9526161408,116268918260244,116269308034719)]
theorem point_links_checked72648 : (cuts72648.take 1).map (fun c => (9526050817-1+2*2^10*c.k,116268775810601+c.lower,116269165584992+c.upper)) = pointBounds72648 := by
 decide +kernel
def cuts72649 : List PrefixCut := [⟨64,169099193,169099300⟩]
theorem checked72649 : checkPrefixCuts (2^48) 9526181889 10 Manual.Count131072.C072649.packed 64 cuts72649 = true := by
 decide +kernel
def cuts72650 : List PrefixCut := [⟨64,168358196,168358295⟩]
theorem checked72650 : checkPrefixCuts (2^48) 9526312961 10 Manual.Count131072.C072650.packed 64 cuts72650 = true := by
 decide +kernel
def cuts72651 : List PrefixCut := [⟨8,21805439,21805451⟩,
⟨64,170985532,170985633⟩]
theorem checked72651 : checkPrefixCuts (2^48) 9526444033 10 Manual.Count131072.C072651.packed 64 cuts72651 = true := by
 decide +kernel
def pointBounds72651 : List (Nat × Nat × Nat) := [(9526460416,116269303968117,116269693742826)]
theorem point_links_checked72651 : (cuts72651.take 1).map (fun c => (9526444033-1+2*2^10*c.k,116269282162678+c.lower,116269671937375+c.upper)) = pointBounds72651 := by
 decide +kernel
def cuts72652 : List PrefixCut := [⟨64,167171730,167171835⟩]
theorem checked72652 : checkPrefixCuts (2^48) 9526575105 10 Manual.Count131072.C072652.packed 64 cuts72652 = true := by
 decide +kernel
def cuts72653 : List PrefixCut := [⟨26,69196252,69196294⟩,
⟨64,169828538,169828642⟩]
theorem checked72653 : checkPrefixCuts (2^48) 9526706177 10 Manual.Count131072.C072653.packed 64 cuts72653 = true := by
 decide +kernel
def pointBounds72653 : List (Nat × Nat × Nat) := [(9526759424,116269689516192,116270079291137)]
theorem point_links_checked72653 : (cuts72653.take 1).map (fun c => (9526706177-1+2*2^10*c.k,116269620319940+c.lower,116270010094843+c.upper)) = pointBounds72653 := by
 decide +kernel
def cuts72654 : List PrefixCut := [⟨64,168526208,168526311⟩]
theorem checked72654 : checkPrefixCuts (2^48) 9526837249 10 Manual.Count131072.C072654.packed 64 cuts72654 = true := by
 decide +kernel
def cuts72655 : List PrefixCut := [⟨44,115963832,115963905⟩,
⟨64,168671612,168671718⟩]
theorem checked72655 : checkPrefixCuts (2^48) 9526968321 10 Manual.Count131072.C072655.packed 64 cuts72655 = true := by
 decide +kernel
def pointBounds72655 : List (Nat × Nat × Nat) := [(9527058432,116270074638518,116270464413701)]
theorem point_links_checked72655 : (cuts72655.take 1).map (fun c => (9526968321-1+2*2^10*c.k,116269958674686+c.lower,116270348449796+c.upper)) = pointBounds72655 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S8.B000082
