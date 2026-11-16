import PlattAssemblyKernel
import PlattCertificates.Count131072.C050608
import PlattCertificates.Count131072.C050609
import PlattCertificates.Count131072.C050610
import PlattCertificates.Count131072.C050611
import PlattCertificates.Count131072.C050612
import PlattCertificates.Count131072.C050613
import PlattCertificates.Count131072.C050614
import PlattCertificates.Count131072.C050615
import PlattCertificates.Count131072.C050616
import PlattCertificates.Count131072.C050617
import PlattCertificates.Count131072.C050618
import PlattCertificates.Count131072.C050619
import PlattCertificates.Count131072.C050620
import PlattCertificates.Count131072.C050621
import PlattCertificates.Count131072.C050622
import PlattCertificates.Count131072.C050623
import PlattCertificates.Count131072.C050624
import PlattCertificates.Count131072.C050625
import PlattCertificates.Count131072.C050626
import PlattCertificates.Count131072.C050627
import PlattCertificates.Count131072.C050628
import PlattCertificates.Count131072.C050629
import PlattCertificates.Count131072.C050630
import PlattCertificates.Count131072.C050631
import PlattCertificates.Count131072.C050632
import PlattCertificates.Count131072.C050633
import PlattCertificates.Count131072.C050634
import PlattCertificates.Count131072.C050635
import PlattCertificates.Count131072.C050636
import PlattCertificates.Count131072.C050637
import PlattCertificates.Count131072.C050638
import PlattCertificates.Count131072.C050639
namespace ChenEffective.PlattWindow.Assembly.Prefix.S6.B000019
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts50608 : List PrefixCut := [⟨64,246942414,246942547⟩]
theorem checked50608 : checkPrefixCuts (2^48) 6637223937 10 Manual.Count131072.C050608.packed 64 cuts50608 = true := by
 decide +kernel
def cuts50609 : List PrefixCut := [⟨8,31254428,31254445⟩,
⟨64,246810317,246810452⟩]
theorem checked50609 : checkPrefixCuts (2^48) 6637355009 10 Manual.Count131072.C050609.packed 64 cuts50609 = true := by
 decide +kernel
def pointBounds50609 : List (Nat × Nat × Nat) := [(6637371392,111807538512295,111807925720043)]
theorem point_links_checked50609 : (cuts50609.take 1).map (fun c => (6637355009-1+2*2^10*c.k,111807507257867+c.lower,111807894465598+c.upper)) = pointBounds50609 := by
 decide +kernel
def cuts50610 : List PrefixCut := [⟨46,177641047,177641147⟩,
⟨64,245448457,245448594⟩]
theorem checked50610 : checkPrefixCuts (2^48) 6637486081 10 Manual.Count131072.C050610.packed 64 cuts50610 = true := by
 decide +kernel
def pointBounds50610 : List (Nat × Nat × Nat) := [(6637580288,111807931709231,111808318917197)]
theorem point_links_checked50610 : (cuts50610.take 1).map (fun c => (6637486081-1+2*2^10*c.k,111807754068184+c.lower,111808141276050+c.upper)) = pointBounds50610 := by
 decide +kernel
def cuts50611 : List PrefixCut := [⟨64,245570826,245570966⟩]
theorem checked50611 : checkPrefixCuts (2^48) 6637617153 10 Manual.Count131072.C050611.packed 64 cuts50611 = true := by
 decide +kernel
def cuts50612 : List PrefixCut := [⟨20,77431620,77431662⟩,
⟨64,247940624,247940762⟩]
theorem checked50612 : checkPrefixCuts (2^48) 6637748225 10 Manual.Count131072.C050612.packed 64 cuts50612 = true := by
 decide +kernel
def pointBounds50612 : List (Nat × Nat × Nat) := [(6637789184,111808322519087,111808709727272)]
theorem point_links_checked50612 : (cuts50612.take 1).map (fun c => (6637748225-1+2*2^10*c.k,111808245087467+c.lower,111808632295610+c.upper)) = pointBounds50612 := by
 decide +kernel
def cuts50613 : List PrefixCut := [⟨58,222875230,222875353⟩,
⟨64,244967476,244967611⟩]
theorem checked50613 : checkPrefixCuts (2^48) 6637879297 10 Manual.Count131072.C050613.packed 64 cuts50613 = true := by
 decide +kernel
def pointBounds50613 : List (Nat × Nat × Nat) := [(6637998080,111808715903321,111809103111725)]
theorem point_links_checked50613 : (cuts50613.take 1).map (fun c => (6637879297-1+2*2^10*c.k,111808493028091+c.lower,111808880236372+c.upper)) = pointBounds50613 := by
 decide +kernel
def cuts50614 : List PrefixCut := [⟨64,245301816,245301955⟩]
theorem checked50614 : checkPrefixCuts (2^48) 6638010369 10 Manual.Count131072.C050614.packed 64 cuts50614 = true := by
 decide +kernel
def cuts50615 : List PrefixCut := [⟨32,119914149,119914218⟩,
⟨64,242413643,242413783⟩]
theorem checked50615 : checkPrefixCuts (2^48) 6638141441 10 Manual.Count131072.C050615.packed 64 cuts50615 = true := by
 decide +kernel
def pointBounds50615 : List (Nat × Nat × Nat) := [(6638206976,111809103211532,111809490420156)]
theorem point_links_checked50615 : (cuts50615.take 1).map (fun c => (6638141441-1+2*2^10*c.k,111808983297383+c.lower,111809370505938+c.upper)) = pointBounds50615 := by
 decide +kernel
def cuts50616 : List PrefixCut := [⟨64,245928175,245928313⟩]
theorem checked50616 : checkPrefixCuts (2^48) 6638272513 10 Manual.Count131072.C050616.packed 64 cuts50616 = true := by
 decide +kernel
def cuts50617 : List PrefixCut := [⟨6,22642108,22642123⟩,
⟨64,245287316,245287459⟩]
theorem checked50617 : checkPrefixCuts (2^48) 6638403585 10 Manual.Count131072.C050617.packed 64 cuts50617 = true := by
 decide +kernel
def pointBounds50617 : List (Nat × Nat × Nat) := [(6638415872,111809494281309,111809881490157)]
theorem point_links_checked50617 : (cuts50617.take 1).map (fun c => (6638403585-1+2*2^10*c.k,111809471639201+c.lower,111809858848034+c.upper)) = pointBounds50617 := by
 decide +kernel
def cuts50618 : List PrefixCut := [⟨44,169557068,169557168⟩,
⟨64,247656853,247656998⟩]
theorem checked50618 : checkPrefixCuts (2^48) 6638534657 10 Manual.Count131072.C050618.packed 64 cuts50618 = true := by
 decide +kernel
def pointBounds50618 : List (Nat × Nat × Nat) := [(6638624768,111809886483585,111810273692661)]
theorem point_links_checked50618 : (cuts50618.take 1).map (fun c => (6638534657-1+2*2^10*c.k,111809716926517+c.lower,111810104135493+c.upper)) = pointBounds50618 := by
 decide +kernel
def cuts50619 : List PrefixCut := [⟨64,246380009,246380153⟩]
theorem checked50619 : checkPrefixCuts (2^48) 6638665729 10 Manual.Count131072.C050619.packed 64 cuts50619 = true := by
 decide +kernel
def cuts50620 : List PrefixCut := [⟨18,69236524,69236564⟩,
⟨64,246926313,246926458⟩]
theorem checked50620 : checkPrefixCuts (2^48) 6638796801 10 Manual.Count131072.C050620.packed 64 cuts50620 = true := by
 decide +kernel
def pointBounds50620 : List (Nat × Nat × Nat) := [(6638833664,111810280199903,111810667409208)]
theorem point_links_checked50620 : (cuts50620.take 1).map (fun c => (6638796801-1+2*2^10*c.k,111810210963379+c.lower,111810598172644+c.upper)) = pointBounds50620 := by
 decide +kernel
def cuts50621 : List PrefixCut := [⟨56,214911803,214911924⟩,
⟨64,246327875,246328013⟩]
theorem checked50621 : checkPrefixCuts (2^48) 6638927873 10 Manual.Count131072.C050621.packed 64 cuts50621 = true := by
 decide +kernel
def pointBounds50621 : List (Nat × Nat × Nat) := [(6639042560,111810672801495,111811060011026)]
theorem point_links_checked50621 : (cuts50621.take 1).map (fun c => (6638927873-1+2*2^10*c.k,111810457889692+c.lower,111810845099102+c.upper)) = pointBounds50621 := by
 decide +kernel
def cuts50622 : List PrefixCut := [⟨64,248612416,248612559⟩]
theorem checked50622 : checkPrefixCuts (2^48) 6639058945 10 Manual.Count131072.C050622.packed 64 cuts50622 = true := by
 decide +kernel
def cuts50623 : List PrefixCut := [⟨30,117648266,117648332⟩,
⟨64,245597451,245597592⟩]
theorem checked50623 : checkPrefixCuts (2^48) 6639190017 10 Manual.Count131072.C050623.packed 64 cuts50623 = true := by
 decide +kernel
def pointBounds50623 : List (Nat × Nat × Nat) := [(6639251456,111811070478249,111811457688006)]
theorem point_links_checked50623 : (cuts50623.take 1).map (fun c => (6639190017-1+2*2^10*c.k,111810952829983+c.lower,111811340039674+c.upper)) = pointBounds50623 := by
 decide +kernel
def cuts50624 : List PrefixCut := [⟨64,246440463,246440599⟩]
theorem checked50624 : checkPrefixCuts (2^48) 6639321089 10 Manual.Count131072.C050624.packed 64 cuts50624 = true := by
 decide +kernel
def cuts50625 : List PrefixCut := [⟨4,15177148,15177157⟩,
⟨64,246689961,246690098⟩]
theorem checked50625 : checkPrefixCuts (2^48) 6639452161 10 Manual.Count131072.C050625.packed 64 cuts50625 = true := by
 decide +kernel
def pointBounds50625 : List (Nat × Nat × Nat) := [(6639460352,111811460045045,111811847255022)]
theorem point_links_checked50625 : (cuts50625.take 1).map (fun c => (6639452161-1+2*2^10*c.k,111811444867897+c.lower,111811832077865+c.upper)) = pointBounds50625 := by
 decide +kernel
def cuts50626 : List PrefixCut := [⟨42,160924530,160924619⟩,
⟨64,245243738,245243875⟩]
theorem checked50626 : checkPrefixCuts (2^48) 6639583233 10 Manual.Count131072.C050626.packed 64 cuts50626 = true := by
 decide +kernel
def pointBounds50626 : List (Nat × Nat × Nat) := [(6639669248,111811852482388,111812239692582)]
theorem point_links_checked50626 : (cuts50626.take 1).map (fun c => (6639583233-1+2*2^10*c.k,111811691557858+c.lower,111812078767963+c.upper)) = pointBounds50626 := by
 decide +kernel
def cuts50627 : List PrefixCut := [⟨64,245747602,245747743⟩]
theorem checked50627 : checkPrefixCuts (2^48) 6639714305 10 Manual.Count131072.C050627.packed 64 cuts50627 = true := by
 decide +kernel
def cuts50628 : List PrefixCut := [⟨16,60832059,60832093⟩,
⟨64,243284052,243284193⟩]
theorem checked50628 : checkPrefixCuts (2^48) 6639845377 10 Manual.Count131072.C050628.packed 64 cuts50628 = true := by
 decide +kernel
def pointBounds50628 : List (Nat × Nat × Nat) := [(6639878144,111812243381257,111812630591674)]
theorem point_links_checked50628 : (cuts50628.take 1).map (fun c => (6639845377-1+2*2^10*c.k,111812182549198+c.lower,111812569759581+c.upper)) = pointBounds50628 := by
 decide +kernel
def cuts50629 : List PrefixCut := [⟨54,209282367,209282487⟩,
⟨64,248493281,248493423⟩]
theorem checked50629 : checkPrefixCuts (2^48) 6639976449 10 Manual.Count131072.C050629.packed 64 cuts50629 = true := by
 decide +kernel
def pointBounds50629 : List (Nat × Nat × Nat) := [(6640087040,111812635115617,111813022326261)]
theorem point_links_checked50629 : (cuts50629.take 1).map (fun c => (6639976449-1+2*2^10*c.k,111812425833250+c.lower,111812813043774+c.upper)) = pointBounds50629 := by
 decide +kernel
def cuts50630 : List PrefixCut := [⟨64,247640594,247640740⟩]
theorem checked50630 : checkPrefixCuts (2^48) 6640107521 10 Manual.Count131072.C050630.packed 64 cuts50630 = true := by
 decide +kernel
def cuts50631 : List PrefixCut := [⟨28,106990062,106990126⟩,
⟨64,242760977,242761119⟩]
theorem checked50631 : checkPrefixCuts (2^48) 6640238593 10 Manual.Count131072.C050631.packed 64 cuts50631 = true := by
 decide +kernel
def pointBounds50631 : List (Nat × Nat × Nat) := [(6640295936,111813028957187,111813416168063)]
theorem point_links_checked50631 : (cuts50631.take 1).map (fun c => (6640238593-1+2*2^10*c.k,111812921967125+c.lower,111813309177937+c.upper)) = pointBounds50631 := by
 decide +kernel
def cuts50632 : List PrefixCut := [⟨64,245469023,245469167⟩]
theorem checked50632 : checkPrefixCuts (2^48) 6640369665 10 Manual.Count131072.C050632.packed 64 cuts50632 = true := by
 decide +kernel
def cuts50633 : List PrefixCut := [⟨2,7248278,7248282⟩,
⟨64,243048089,243048226⟩]
theorem checked50633 : checkPrefixCuts (2^48) 6640500737 10 Manual.Count131072.C050633.packed 64 cuts50633 = true := by
 decide +kernel
def pointBounds50633 : List (Nat × Nat × Nat) := [(6640504832,111813417445403,111813804656505)]
theorem point_links_checked50633 : (cuts50633.take 1).map (fun c => (6640500737-1+2*2^10*c.k,111813410197125+c.lower,111813797408223+c.upper)) = pointBounds50633 := by
 decide +kernel
def cuts50634 : List PrefixCut := [⟨40,152421869,152421960⟩,
⟨64,246137506,246137653⟩]
theorem checked50634 : checkPrefixCuts (2^48) 6640631809 10 Manual.Count131072.C050634.packed 64 cuts50634 = true := by
 decide +kernel
def pointBounds50634 : List (Nat × Nat × Nat) := [(6640713728,111813805667083,111814192878409)]
theorem point_links_checked50634 : (cuts50634.take 1).map (fun c => (6640631809-1+2*2^10*c.k,111813653245214+c.lower,111814040456449+c.upper)) = pointBounds50634 := by
 decide +kernel
def cuts50635 : List PrefixCut := [⟨64,244649154,244649291⟩]
theorem checked50635 : checkPrefixCuts (2^48) 6640762881 10 Manual.Count131072.C050635.packed 64 cuts50635 = true := by
 decide +kernel
def cuts50636 : List PrefixCut := [⟨14,53913714,53913746⟩,
⟨64,246721166,246721311⟩]
theorem checked50636 : checkPrefixCuts (2^48) 6640893953 10 Manual.Count131072.C050636.packed 64 cuts50636 = true := by
 decide +kernel
def pointBounds50636 : List (Nat × Nat × Nat) := [(6640922624,111814197945588,111814585157139)]
theorem point_links_checked50636 : (cuts50636.take 1).map (fun c => (6640893953-1+2*2^10*c.k,111814144031874+c.lower,111814531243393+c.upper)) = pointBounds50636 := by
 decide +kernel
def cuts50637 : List PrefixCut := [⟨52,201154073,201154187⟩,
⟨64,247436850,247436992⟩]
theorem checked50637 : checkPrefixCuts (2^48) 6641025025 10 Manual.Count131072.C050637.packed 64 cuts50637 = true := by
 decide +kernel
def pointBounds50637 : List (Nat × Nat × Nat) := [(6641131520,111814591907113,111814979118891)]
theorem point_links_checked50637 : (cuts50637.take 1).map (fun c => (6641025025-1+2*2^10*c.k,111814390753040+c.lower,111814777964704+c.upper)) = pointBounds50637 := by
 decide +kernel
def cuts50638 : List PrefixCut := [⟨64,242685057,242685197⟩]
theorem checked50638 : checkPrefixCuts (2^48) 6641156097 10 Manual.Count131072.C050638.packed 64 cuts50638 = true := by
 decide +kernel
def cuts50639 : List PrefixCut := [⟨26,99132456,99132514⟩,
⟨64,246791331,246791471⟩]
theorem checked50639 : checkPrefixCuts (2^48) 6641287169 10 Manual.Count131072.C050639.packed 64 cuts50639 = true := by
 decide +kernel
def pointBounds50639 : List (Nat × Nat × Nat) := [(6641340416,111814980007403,111815367219407)]
theorem point_links_checked50639 : (cuts50639.take 1).map (fun c => (6641287169-1+2*2^10*c.k,111814880874947+c.lower,111815268086893+c.upper)) = pointBounds50639 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S6.B000019
