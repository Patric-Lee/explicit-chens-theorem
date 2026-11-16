import PlattAssemblyKernel
import PlattCertificates.Count131072.C050640
import PlattCertificates.Count131072.C050641
import PlattCertificates.Count131072.C050642
import PlattCertificates.Count131072.C050643
import PlattCertificates.Count131072.C050644
import PlattCertificates.Count131072.C050645
import PlattCertificates.Count131072.C050646
import PlattCertificates.Count131072.C050647
import PlattCertificates.Count131072.C050648
import PlattCertificates.Count131072.C050649
import PlattCertificates.Count131072.C050650
import PlattCertificates.Count131072.C050651
import PlattCertificates.Count131072.C050652
import PlattCertificates.Count131072.C050653
import PlattCertificates.Count131072.C050654
import PlattCertificates.Count131072.C050655
import PlattCertificates.Count131072.C050656
import PlattCertificates.Count131072.C050657
import PlattCertificates.Count131072.C050658
import PlattCertificates.Count131072.C050659
import PlattCertificates.Count131072.C050660
import PlattCertificates.Count131072.C050661
import PlattCertificates.Count131072.C050662
import PlattCertificates.Count131072.C050663
import PlattCertificates.Count131072.C050664
import PlattCertificates.Count131072.C050665
import PlattCertificates.Count131072.C050666
import PlattCertificates.Count131072.C050667
import PlattCertificates.Count131072.C050668
import PlattCertificates.Count131072.C050669
import PlattCertificates.Count131072.C050670
import PlattCertificates.Count131072.C050671
namespace ChenEffective.PlattWindow.Assembly.Prefix.S6.B000020
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts50640 : List PrefixCut := [⟨64,245048841,245048982⟩]
theorem checked50640 : checkPrefixCuts (2^48) 6641418241 10 Manual.Count131072.C050640.packed 64 cuts50640 = true := by
 decide +kernel
def pointBounds50640 : List (Nat × Nat × Nat) := [(6641549312,111815372715119,111815759927346)]
theorem point_links_checked50640 : (cuts50640.take 1).map (fun c => (6641418241-1+2*2^10*c.k,111815127666278+c.lower,111815514878364+c.upper)) = pointBounds50640 := by
 decide +kernel
def cuts50641 : List PrefixCut := [⟨64,247078255,247078391⟩]
theorem checked50641 : checkPrefixCuts (2^48) 6641549313 10 Manual.Count131072.C050641.packed 64 cuts50641 = true := by
 decide +kernel
def cuts50642 : List PrefixCut := [⟨38,144303296,144303382⟩,
⟨64,245505316,245505460⟩]
theorem checked50642 : checkPrefixCuts (2^48) 6641680385 10 Manual.Count131072.C050642.packed 64 cuts50642 = true := by
 decide +kernel
def pointBounds50642 : List (Nat × Nat × Nat) := [(6641758208,111815764096670,111816151309119)]
theorem point_links_checked50642 : (cuts50642.take 1).map (fun c => (6641680385-1+2*2^10*c.k,111815619793374+c.lower,111816007005737+c.upper)) = pointBounds50642 := by
 decide +kernel
def cuts50643 : List PrefixCut := [⟨64,245966660,245966800⟩]
theorem checked50643 : checkPrefixCuts (2^48) 6641811457 10 Manual.Count131072.C050643.packed 64 cuts50643 = true := by
 decide +kernel
def cuts50644 : List PrefixCut := [⟨12,47717990,47718016⟩,
⟨64,248377358,248377500⟩]
theorem checked50644 : checkPrefixCuts (2^48) 6641942529 10 Manual.Count131072.C050644.packed 64 cuts50644 = true := by
 decide +kernel
def pointBounds50644 : List (Nat × Nat × Nat) := [(6641967104,111816158983340,111816546196013)]
theorem point_links_checked50644 : (cuts50644.take 1).map (fun c => (6641942529-1+2*2^10*c.k,111816111265350+c.lower,111816498477997+c.upper)) = pointBounds50644 := by
 decide +kernel
def cuts50645 : List PrefixCut := [⟨50,193367303,193367415⟩,
⟨64,247948645,247948790⟩]
theorem checked50645 : checkPrefixCuts (2^48) 6642073601 10 Manual.Count131072.C050645.packed 64 cuts50645 = true := by
 decide +kernel
def pointBounds50645 : List (Nat × Nat × Nat) := [(6642176000,111816553010011,111816940222912)]
theorem point_links_checked50645 : (cuts50645.take 1).map (fun c => (6642073601-1+2*2^10*c.k,111816359642708+c.lower,111816746855497+c.upper)) = pointBounds50645 := by
 decide +kernel
def cuts50646 : List PrefixCut := [⟨64,248664187,248664332⟩]
theorem checked50646 : checkPrefixCuts (2^48) 6642204673 10 Manual.Count131072.C050646.packed 64 cuts50646 = true := by
 decide +kernel
def cuts50647 : List PrefixCut := [⟨24,90260312,90260365⟩,
⟨64,243574209,243574352⟩]
theorem checked50647 : checkPrefixCuts (2^48) 6642335745 10 Manual.Count131072.C050647.packed 64 cuts50647 = true := by
 decide +kernel
def pointBounds50647 : List (Nat × Nat × Nat) := [(6642384896,111816946515852,111817333728984)]
theorem point_links_checked50647 : (cuts50647.take 1).map (fun c => (6642335745-1+2*2^10*c.k,111816856255540+c.lower,111817243468619+c.upper)) = pointBounds50647 := by
 decide +kernel
def cuts50648 : List PrefixCut := [⟨62,239035400,239035541⟩,
⟨64,246747510,246747656⟩]
theorem checked50648 : checkPrefixCuts (2^48) 6642466817 10 Manual.Count131072.C050648.packed 64 cuts50648 = true := by
 decide +kernel
def pointBounds50648 : List (Nat × Nat × Nat) := [(6642593792,111817338865149,111817726078512)]
theorem point_links_checked50648 : (cuts50648.take 1).map (fun c => (6642466817-1+2*2^10*c.k,111817099829749+c.lower,111817487042971+c.upper)) = pointBounds50648 := by
 decide +kernel
def cuts50649 : List PrefixCut := [⟨64,243522248,243522386⟩]
theorem checked50649 : checkPrefixCuts (2^48) 6642597889 10 Manual.Count131072.C050649.packed 64 cuts50649 = true := by
 decide +kernel
def cuts50650 : List PrefixCut := [⟨36,136695773,136695850⟩,
⟨64,244110641,244110777⟩]
theorem checked50650 : checkPrefixCuts (2^48) 6642728961 10 Manual.Count131072.C050650.packed 64 cuts50650 = true := by
 decide +kernel
def pointBounds50650 : List (Nat × Nat × Nat) := [(6642802688,111817726795280,111818114008863)]
theorem point_links_checked50650 : (cuts50650.take 1).map (fun c => (6642728961-1+2*2^10*c.k,111817590099507+c.lower,111817977313013+c.upper)) = pointBounds50650 := by
 decide +kernel
def cuts50651 : List PrefixCut := [⟨64,243512602,243512744⟩]
theorem checked50651 : checkPrefixCuts (2^48) 6642860033 10 Manual.Count131072.C050651.packed 64 cuts50651 = true := by
 decide +kernel
def cuts50652 : List PrefixCut := [⟨10,38600570,38600593⟩,
⟨64,243084126,243084265⟩]
theorem checked50652 : checkPrefixCuts (2^48) 6642991105 10 Manual.Count131072.C050652.packed 64 cuts50652 = true := by
 decide +kernel
def pointBounds50652 : List (Nat × Nat × Nat) := [(6643011584,111818116323320,111818503537127)]
theorem point_links_checked50652 : (cuts50652.take 1).map (fun c => (6642991105-1+2*2^10*c.k,111818077722750+c.lower,111818464936534+c.upper)) = pointBounds50652 := by
 decide +kernel
def cuts50653 : List PrefixCut := [⟨48,183634021,183634121⟩,
⟨64,243503034,243503170⟩]
theorem checked50653 : checkPrefixCuts (2^48) 6643122177 10 Manual.Count131072.C050653.packed 64 cuts50653 = true := by
 decide +kernel
def pointBounds50653 : List (Nat × Nat × Nat) := [(6643220480,111818504440897,111818891654920)]
theorem point_links_checked50653 : (cuts50653.take 1).map (fun c => (6643122177-1+2*2^10*c.k,111818320806876+c.lower,111818708020799+c.upper)) = pointBounds50653 := by
 decide +kernel
def cuts50654 : List PrefixCut := [⟨64,244811689,244811825⟩]
theorem checked50654 : checkPrefixCuts (2^48) 6643253249 10 Manual.Count131072.C050654.packed 64 cuts50654 = true := by
 decide +kernel
def cuts50655 : List PrefixCut := [⟨22,84272058,84272108⟩,
⟨64,242137619,242137763⟩]
theorem checked50655 : checkPrefixCuts (2^48) 6643384321 10 Manual.Count131072.C050655.packed 64 cuts50655 = true := by
 decide +kernel
def pointBounds50655 : List (Nat × Nat × Nat) := [(6643429376,111818893393657,111819280607902)]
theorem point_links_checked50655 : (cuts50655.take 1).map (fun c => (6643384321-1+2*2^10*c.k,111818809121599+c.lower,111819196335794+c.upper)) = pointBounds50655 := by
 decide +kernel
def cuts50656 : List PrefixCut := [⟨60,231329143,231329275⟩,
⟨64,246369625,246369766⟩]
theorem checked50656 : checkPrefixCuts (2^48) 6643515393 10 Manual.Count131072.C050656.packed 64 cuts50656 = true := by
 decide +kernel
def pointBounds50656 : List (Nat × Nat × Nat) := [(6643638272,111819282588361,111819669802832)]
theorem point_links_checked50656 : (cuts50656.take 1).map (fun c => (6643515393-1+2*2^10*c.k,111819051259218+c.lower,111819438473557+c.upper)) = pointBounds50656 := by
 decide +kernel
def cuts50657 : List PrefixCut := [⟨64,244246402,244246541⟩]
theorem checked50657 : checkPrefixCuts (2^48) 6643646465 10 Manual.Count131072.C050657.packed 64 cuts50657 = true := by
 decide +kernel
def cuts50658 : List PrefixCut := [⟨34,129641415,129641493⟩,
⟨64,246614087,246614229⟩]
theorem checked50658 : checkPrefixCuts (2^48) 6643777537 10 Manual.Count131072.C050658.packed 64 cuts50658 = true := by
 decide +kernel
def pointBounds50658 : List (Nat × Nat × Nat) := [(6643847168,111819671516660,111820058731357)]
theorem point_links_checked50658 : (cuts50658.take 1).map (fun c => (6643777537-1+2*2^10*c.k,111819541875245+c.lower,111819929089864+c.upper)) = pointBounds50658 := by
 decide +kernel
def cuts50659 : List PrefixCut := [⟨64,246016111,246016253⟩]
theorem checked50659 : checkPrefixCuts (2^48) 6643908609 10 Manual.Count131072.C050659.packed 64 cuts50659 = true := by
 decide +kernel
def cuts50660 : List PrefixCut := [⟨8,31307716,31307733⟩,
⟨64,248722622,248722759⟩]
theorem checked50660 : checkPrefixCuts (2^48) 6644039681 10 Manual.Count131072.C050660.packed 64 cuts50660 = true := by
 decide +kernel
def pointBounds50660 : List (Nat × Nat × Nat) := [(6644056064,111820065813159,111820453028079)]
theorem point_links_checked50660 : (cuts50660.take 1).map (fun c => (6644039681-1+2*2^10*c.k,111820034505443+c.lower,111820421720346+c.upper)) = pointBounds50660 := by
 decide +kernel
def cuts50661 : List PrefixCut := [⟨46,175047595,175047694⟩,
⟨64,244650773,244650914⟩]
theorem checked50661 : checkPrefixCuts (2^48) 6644170753 10 Manual.Count131072.C050661.packed 64 cuts50661 = true := by
 decide +kernel
def pointBounds50661 : List (Nat × Nat × Nat) := [(6644264960,111820458275660,111820845490799)]
theorem point_links_checked50661 : (cuts50661.take 1).map (fun c => (6644170753-1+2*2^10*c.k,111820283228065+c.lower,111820670443105+c.upper)) = pointBounds50661 := by
 decide +kernel
def cuts50662 : List PrefixCut := [⟨64,244984845,244984987⟩]
theorem checked50662 : checkPrefixCuts (2^48) 6644301825 10 Manual.Count131072.C050662.packed 64 cuts50662 = true := by
 decide +kernel
def cuts50663 : List PrefixCut := [⟨20,76209927,76209971⟩,
⟨64,245700169,245700311⟩]
theorem checked50663 : checkPrefixCuts (2^48) 6644432897 10 Manual.Count131072.C050663.packed 64 cuts50663 = true := by
 decide +kernel
def pointBounds50663 : List (Nat × Nat × Nat) := [(6644473856,111820849073610,111821236288977)]
theorem point_links_checked50663 : (cuts50663.take 1).map (fun c => (6644432897-1+2*2^10*c.k,111820772863683+c.lower,111821160079006+c.upper)) = pointBounds50663 := by
 decide +kernel
def cuts50664 : List PrefixCut := [⟨58,221973213,221973343⟩,
⟨64,245652948,245653092⟩]
theorem checked50664 : checkPrefixCuts (2^48) 6644563969 10 Manual.Count131072.C050664.packed 64 cuts50664 = true := by
 decide +kernel
def pointBounds50664 : List (Nat × Nat × Nat) := [(6644682752,111821240537065,111821627752660)]
theorem point_links_checked50664 : (cuts50664.take 1).map (fun c => (6644563969-1+2*2^10*c.k,111821018563852+c.lower,111821405779317+c.upper)) = pointBounds50664 := by
 decide +kernel
def cuts50665 : List PrefixCut := [⟨64,245351575,245351713⟩]
theorem checked50665 : checkPrefixCuts (2^48) 6644695041 10 Manual.Count131072.C050665.packed 64 cuts50665 = true := by
 decide +kernel
def cuts50666 : List PrefixCut := [⟨32,122080941,122081010⟩,
⟨64,244499558,244499698⟩]
theorem checked50666 : checkPrefixCuts (2^48) 6644826113 10 Manual.Count131072.C050666.packed 64 cuts50666 = true := by
 decide +kernel
def pointBounds50666 : List (Nat × Nat × Nat) := [(6644891648,111821631649316,111822018865132)]
theorem point_links_checked50666 : (cuts50666.take 1).map (fun c => (6644826113-1+2*2^10*c.k,111821509568375+c.lower,111821896784122+c.upper)) = pointBounds50666 := by
 decide +kernel
def cuts50667 : List PrefixCut := [⟨64,242630947,242631089⟩]
theorem checked50667 : checkPrefixCuts (2^48) 6644957185 10 Manual.Count131072.C050667.packed 64 cuts50667 = true := by
 decide +kernel
def cuts50668 : List PrefixCut := [⟨6,23085274,23085287⟩,
⟨64,249234001,249234142⟩]
theorem checked50668 : checkPrefixCuts (2^48) 6645088257 10 Manual.Count131072.C050668.packed 64 cuts50668 = true := by
 decide +kernel
def pointBounds50668 : List (Nat × Nat × Nat) := [(6645100544,111822019784154,111822407000196)]
theorem point_links_checked50668 : (cuts50668.take 1).map (fun c => (6645088257-1+2*2^10*c.k,111821996698880+c.lower,111822383914909+c.upper)) = pointBounds50668 := by
 decide +kernel
def cuts50669 : List PrefixCut := [⟨44,168581718,168581816⟩,
⟨64,245586379,245586518⟩]
theorem checked50669 : checkPrefixCuts (2^48) 6645219329 10 Manual.Count131072.C050669.packed 64 cuts50669 = true := by
 decide +kernel
def pointBounds50669 : List (Nat × Nat × Nat) := [(6645309440,111822414514599,111822801730867)]
theorem point_links_checked50669 : (cuts50669.take 1).map (fun c => (6645219329-1+2*2^10*c.k,111822245932881+c.lower,111822633149051+c.upper)) = pointBounds50669 := by
 decide +kernel
def cuts50670 : List PrefixCut := [⟨64,242828380,242828514⟩]
theorem checked50670 : checkPrefixCuts (2^48) 6645350401 10 Manual.Count131072.C050670.packed 64 cuts50670 = true := by
 decide +kernel
def cuts50671 : List PrefixCut := [⟨18,68955103,68955142⟩,
⟨64,245195474,245195616⟩]
theorem checked50671 : checkPrefixCuts (2^48) 6645481473 10 Manual.Count131072.C050671.packed 64 cuts50671 = true := by
 decide +kernel
def pointBounds50671 : List (Nat × Nat × Nat) := [(6645518336,111822803302743,111823190519225)]
theorem point_links_checked50671 : (cuts50671.take 1).map (fun c => (6645481473-1+2*2^10*c.k,111822734347640+c.lower,111823121564083+c.upper)) = pointBounds50671 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S6.B000020
