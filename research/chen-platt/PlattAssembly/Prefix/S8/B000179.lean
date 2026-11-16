import PlattAssemblyKernel
import PlattCertificates.Count131072.C075728
import PlattCertificates.Count131072.C075729
import PlattCertificates.Count131072.C075730
import PlattCertificates.Count131072.C075731
import PlattCertificates.Count131072.C075732
import PlattCertificates.Count131072.C075733
import PlattCertificates.Count131072.C075734
import PlattCertificates.Count131072.C075735
import PlattCertificates.Count131072.C075736
import PlattCertificates.Count131072.C075737
import PlattCertificates.Count131072.C075738
import PlattCertificates.Count131072.C075739
import PlattCertificates.Count131072.C075740
import PlattCertificates.Count131072.C075741
import PlattCertificates.Count131072.C075742
import PlattCertificates.Count131072.C075743
import PlattCertificates.Count131072.C075744
import PlattCertificates.Count131072.C075745
import PlattCertificates.Count131072.C075746
import PlattCertificates.Count131072.C075747
import PlattCertificates.Count131072.C075748
import PlattCertificates.Count131072.C075749
import PlattCertificates.Count131072.C075750
import PlattCertificates.Count131072.C075751
import PlattCertificates.Count131072.C075752
import PlattCertificates.Count131072.C075753
import PlattCertificates.Count131072.C075754
import PlattCertificates.Count131072.C075755
import PlattCertificates.Count131072.C075756
import PlattCertificates.Count131072.C075757
import PlattCertificates.Count131072.C075758
import PlattCertificates.Count131072.C075759
namespace ChenEffective.PlattWindow.Assembly.Prefix.S8.B000179
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts75728 : List PrefixCut := [⟨64,163417177,163417273⟩]
theorem checked75728 : checkPrefixCuts (2^48) 9929752577 10 Manual.Count131072.C075728.packed 64 cuts75728 = true := by
 decide +kernel
def cuts75729 : List PrefixCut := [⟨35,89233652,89233703⟩,
⟨64,159446576,159446673⟩]
theorem checked75729 : checkPrefixCuts (2^48) 9929883649 10 Manual.Count131072.C075729.packed 64 cuts75729 = true := by
 decide +kernel
def pointBounds75729 : List (Nat × Nat × Nat) := [(9929955328,116777072531566,116777462610066)]
theorem point_links_checked75729 : (cuts75729.take 1).map (fun c => (9929883649-1+2*2^10*c.k,116776983297914+c.lower,116777373376363+c.upper)) = pointBounds75729 := by
 decide +kernel
def cuts75730 : List PrefixCut := [⟨64,162647529,162647629⟩]
theorem checked75730 : checkPrefixCuts (2^48) 9930014721 10 Manual.Count131072.C075730.packed 64 cuts75730 = true := by
 decide +kernel
def cuts75731 : List PrefixCut := [⟨59,149464880,149464971⟩,
⟨64,161795014,161795111⟩]
theorem checked75731 : checkPrefixCuts (2^48) 9930145793 10 Manual.Count131072.C075731.packed 64 cuts75731 = true := by
 decide +kernel
def pointBounds75731 : List (Nat × Nat × Nat) := [(9930266624,116777454856899,116777844935636)]
theorem point_links_checked75731 : (cuts75731.take 1).map (fun c => (9930145793-1+2*2^10*c.k,116777305392019+c.lower,116777695470665+c.upper)) = pointBounds75731 := by
 decide +kernel
def cuts75732 : List PrefixCut := [⟨64,161424393,161424488⟩]
theorem checked75732 : checkPrefixCuts (2^48) 9930276865 10 Manual.Count131072.C075732.packed 64 cuts75732 = true := by
 decide +kernel
def cuts75733 : List PrefixCut := [⟨64,161138824,161138922⟩]
theorem checked75733 : checkPrefixCuts (2^48) 9930407937 10 Manual.Count131072.C075733.packed 64 cuts75733 = true := by
 decide +kernel
def cuts75734 : List PrefixCut := [⟨19,48497128,48497155⟩,
⟨64,162780662,162780758⟩]
theorem checked75734 : checkPrefixCuts (2^48) 9930539009 10 Manual.Count131072.C075734.packed 64 cuts75734 = true := by
 decide +kernel
def pointBounds75734 : List (Nat × Nat × Nat) := [(9930577920,116777838247378,116778228326341)]
theorem point_links_checked75734 : (cuts75734.take 1).map (fun c => (9930539009-1+2*2^10*c.k,116777789750250+c.lower,116778179829186+c.upper)) = pointBounds75734 := by
 decide +kernel
def cuts75735 : List PrefixCut := [⟨64,161786469,161786570⟩]
theorem checked75735 : checkPrefixCuts (2^48) 9930670081 10 Manual.Count131072.C075735.packed 64 cuts75735 = true := by
 decide +kernel
def cuts75736 : List PrefixCut := [⟨43,107733636,107733699⟩,
⟨64,161670961,161671052⟩]
theorem checked75736 : checkPrefixCuts (2^48) 9930801153 10 Manual.Count131072.C075736.packed 64 cuts75736 = true := by
 decide +kernel
def pointBounds75736 : List (Nat × Nat × Nat) := [(9930889216,116778222051017,116778612130213)]
theorem point_links_checked75736 : (cuts75736.take 1).map (fun c => (9930801153-1+2*2^10*c.k,116778114317381+c.lower,116778504396514+c.upper)) = pointBounds75736 := by
 decide +kernel
def cuts75737 : List PrefixCut := [⟨64,160875223,160875318⟩]
theorem checked75737 : checkPrefixCuts (2^48) 9930932225 10 Manual.Count131072.C075737.packed 64 cuts75737 = true := by
 decide +kernel
def cuts75738 : List PrefixCut := [⟨64,159767743,159767841⟩]
theorem checked75738 : checkPrefixCuts (2^48) 9931063297 10 Manual.Count131072.C075738.packed 64 cuts75738 = true := by
 decide +kernel
def cuts75739 : List PrefixCut := [⟨3,7340706,7340709⟩,
⟨64,162033013,162033109⟩]
theorem checked75739 : checkPrefixCuts (2^48) 9931194369 10 Manual.Count131072.C075739.packed 64 cuts75739 = true := by
 decide +kernel
def pointBounds75739 : List (Nat × Nat × Nat) := [(9931200512,116778603972014,116778994051434)]
theorem point_links_checked75739 : (cuts75739.take 1).map (fun c => (9931194369-1+2*2^10*c.k,116778596631308+c.lower,116778986710725+c.upper)) = pointBounds75739 := by
 decide +kernel
def cuts75740 : List PrefixCut := [⟨64,162257613,162257707⟩]
theorem checked75740 : checkPrefixCuts (2^48) 9931325441 10 Manual.Count131072.C075740.packed 64 cuts75740 = true := by
 decide +kernel
def cuts75741 : List PrefixCut := [⟨27,69068662,69068706⟩,
⟨64,160356586,160356687⟩]
theorem checked75741 : checkPrefixCuts (2^48) 9931456513 10 Manual.Count131072.C075741.packed 64 cuts75741 = true := by
 decide +kernel
def pointBounds75741 : List (Nat × Nat × Nat) := [(9931511808,116778989990596,116779380070247)]
theorem point_links_checked75741 : (cuts75741.take 1).map (fun c => (9931456513-1+2*2^10*c.k,116778920921934+c.lower,116779311001541+c.upper)) = pointBounds75741 := by
 decide +kernel
def cuts75742 : List PrefixCut := [⟨64,160637880,160637983⟩]
theorem checked75742 : checkPrefixCuts (2^48) 9931587585 10 Manual.Count131072.C075742.packed 64 cuts75742 = true := by
 decide +kernel
def cuts75743 : List PrefixCut := [⟨51,125635008,125635086⟩,
⟨64,158708568,158708667⟩]
theorem checked75743 : checkPrefixCuts (2^48) 9931718657 10 Manual.Count131072.C075743.packed 64 cuts75743 = true := by
 decide +kernel
def pointBounds75743 : List (Nat × Nat × Nat) := [(9931823104,116779367551408,116779757631297)]
theorem point_links_checked75743 : (cuts75743.take 1).map (fun c => (9931718657-1+2*2^10*c.k,116779241916400+c.lower,116779631996211+c.upper)) = pointBounds75743 := by
 decide +kernel
def cuts75744 : List PrefixCut := [⟨64,160860358,160860460⟩]
theorem checked75744 : checkPrefixCuts (2^48) 9931849729 10 Manual.Count131072.C075744.packed 64 cuts75744 = true := by
 decide +kernel
def cuts75745 : List PrefixCut := [⟨64,162672016,162672115⟩]
theorem checked75745 : checkPrefixCuts (2^48) 9931980801 10 Manual.Count131072.C075745.packed 64 cuts75745 = true := by
 decide +kernel
def cuts75746 : List PrefixCut := [⟨11,27829733,27829751⟩,
⟨64,161422915,161423016⟩]
theorem checked75746 : checkPrefixCuts (2^48) 9932111873 10 Manual.Count131072.C075746.packed 64 cuts75746 = true := by
 decide +kernel
def pointBounds75746 : List (Nat × Nat × Nat) := [(9932134400,116779751987075,116780142067204)]
theorem point_links_checked75746 : (cuts75746.take 1).map (fun c => (9932111873-1+2*2^10*c.k,116779724157342+c.lower,116780114237453+c.upper)) = pointBounds75746 := by
 decide +kernel
def cuts75747 : List PrefixCut := [⟨64,163092802,163092904⟩]
theorem checked75747 : checkPrefixCuts (2^48) 9932242945 10 Manual.Count131072.C075747.packed 64 cuts75747 = true := by
 decide +kernel
def cuts75748 : List PrefixCut := [⟨35,86972488,86972540⟩,
⟨64,159151532,159151624⟩]
theorem checked75748 : checkPrefixCuts (2^48) 9932374017 10 Manual.Count131072.C075748.packed 64 cuts75748 = true := by
 decide +kernel
def pointBounds75748 : List (Nat × Nat × Nat) := [(9932445696,116780135645547,116780525725913)]
theorem point_links_checked75748 : (cuts75748.take 1).map (fun c => (9932374017-1+2*2^10*c.k,116780048673059+c.lower,116780438753373+c.upper)) = pointBounds75748 := by
 decide +kernel
def cuts75749 : List PrefixCut := [⟨64,162918455,162918557⟩]
theorem checked75749 : checkPrefixCuts (2^48) 9932505089 10 Manual.Count131072.C075749.packed 64 cuts75749 = true := by
 decide +kernel
def cuts75750 : List PrefixCut := [⟨59,148067172,148067257⟩,
⟨64,160705933,160706025⟩]
theorem checked75750 : checkPrefixCuts (2^48) 9932636161 10 Manual.Count131072.C075750.packed 64 cuts75750 = true := by
 decide +kernel
def pointBounds75750 : List (Nat × Nat × Nat) := [(9932756992,116780518810218,116780908890811)]
theorem point_links_checked75750 : (cuts75750.take 1).map (fun c => (9932636161-1+2*2^10*c.k,116780370743046+c.lower,116780760823554+c.upper)) = pointBounds75750 := by
 decide +kernel
def cuts75751 : List PrefixCut := [⟨64,162347404,162347499⟩]
theorem checked75751 : checkPrefixCuts (2^48) 9932767233 10 Manual.Count131072.C075751.packed 64 cuts75751 = true := by
 decide +kernel
def cuts75752 : List PrefixCut := [⟨64,159936588,159936681⟩]
theorem checked75752 : checkPrefixCuts (2^48) 9932898305 10 Manual.Count131072.C075752.packed 64 cuts75752 = true := by
 decide +kernel
def cuts75753 : List PrefixCut := [⟨19,48881686,48881716⟩,
⟨64,160784592,160784686⟩]
theorem checked75753 : checkPrefixCuts (2^48) 9933029377 10 Manual.Count131072.C075753.packed 64 cuts75753 = true := by
 decide +kernel
def pointBounds75753 : List (Nat × Nat × Nat) := [(9933068288,116780902614657,116781292695475)]
theorem point_links_checked75753 : (cuts75753.take 1).map (fun c => (9933029377-1+2*2^10*c.k,116780853732971+c.lower,116781243813759+c.upper)) = pointBounds75753 := by
 decide +kernel
def cuts75754 : List PrefixCut := [⟨64,161547554,161547648⟩]
theorem checked75754 : checkPrefixCuts (2^48) 9933160449 10 Manual.Count131072.C075754.packed 64 cuts75754 = true := by
 decide +kernel
def cuts75755 : List PrefixCut := [⟨43,108471710,108471782⟩,
⟨64,161177051,161177155⟩]
theorem checked75755 : checkPrefixCuts (2^48) 9933291521 10 Manual.Count131072.C075755.packed 64 cuts75755 = true := by
 decide +kernel
def pointBounds75755 : List (Nat × Nat × Nat) := [(9933379584,116781284536827,116781674617875)]
theorem point_links_checked75755 : (cuts75755.take 1).map (fun c => (9933291521-1+2*2^10*c.k,116781176065117+c.lower,116781566146093+c.upper)) = pointBounds75755 := by
 decide +kernel
def cuts75756 : List PrefixCut := [⟨64,162535049,162535147⟩]
theorem checked75756 : checkPrefixCuts (2^48) 9933422593 10 Manual.Count131072.C075756.packed 64 cuts75756 = true := by
 decide +kernel
def cuts75757 : List PrefixCut := [⟨64,162447911,162448008⟩]
theorem checked75757 : checkPrefixCuts (2^48) 9933553665 10 Manual.Count131072.C075757.packed 64 cuts75757 = true := by
 decide +kernel
def cuts75758 : List PrefixCut := [⟨3,7083847,7083851⟩,
⟨64,161340679,161340770⟩]
theorem checked75758 : checkPrefixCuts (2^48) 9933684737 10 Manual.Count131072.C075758.packed 64 cuts75758 = true := by
 decide +kernel
def pointBounds75758 : List (Nat × Nat × Nat) := [(9933690880,116781669308975,116782059390254)]
theorem point_links_checked75758 : (cuts75758.take 1).map (fun c => (9933684737-1+2*2^10*c.k,116781662225128+c.lower,116782052306403+c.upper)) = pointBounds75758 := by
 decide +kernel
def cuts75759 : List PrefixCut := [⟨64,159525115,159525212⟩]
theorem checked75759 : checkPrefixCuts (2^48) 9933815809 10 Manual.Count131072.C075759.packed 64 cuts75759 = true := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S8.B000179
