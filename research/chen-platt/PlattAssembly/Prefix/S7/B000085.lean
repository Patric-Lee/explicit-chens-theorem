import PlattAssemblyKernel
import PlattCertificates.Count131072.C062720
import PlattCertificates.Count131072.C062721
import PlattCertificates.Count131072.C062722
import PlattCertificates.Count131072.C062723
import PlattCertificates.Count131072.C062724
import PlattCertificates.Count131072.C062725
import PlattCertificates.Count131072.C062726
import PlattCertificates.Count131072.C062727
import PlattCertificates.Count131072.C062728
import PlattCertificates.Count131072.C062729
import PlattCertificates.Count131072.C062730
import PlattCertificates.Count131072.C062731
import PlattCertificates.Count131072.C062732
import PlattCertificates.Count131072.C062733
import PlattCertificates.Count131072.C062734
import PlattCertificates.Count131072.C062735
import PlattCertificates.Count131072.C062736
import PlattCertificates.Count131072.C062737
import PlattCertificates.Count131072.C062738
import PlattCertificates.Count131072.C062739
import PlattCertificates.Count131072.C062740
import PlattCertificates.Count131072.C062741
import PlattCertificates.Count131072.C062742
import PlattCertificates.Count131072.C062743
import PlattCertificates.Count131072.C062744
import PlattCertificates.Count131072.C062745
import PlattCertificates.Count131072.C062746
import PlattCertificates.Count131072.C062747
import PlattCertificates.Count131072.C062748
import PlattCertificates.Count131072.C062749
import PlattCertificates.Count131072.C062750
import PlattCertificates.Count131072.C062751
namespace ChenEffective.PlattWindow.Assembly.Prefix.S7.B000085
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts62720 : List PrefixCut := [⟨42,128574521,128574595⟩,
⟨64,196095286,196095399⟩]
theorem checked62720 : checkPrefixCuts (2^48) 8224768001 10 Manual.Count131072.C062720.packed 64 cuts62720 = true := by
 decide +kernel
def pointBounds62720 : List (Nat × Nat × Nat) := [(8224854016,114463859478508,114464248199164)]
theorem point_links_checked62720 : (cuts62720.take 1).map (fun c => (8224768001-1+2*2^10*c.k,114463730903987+c.lower,114464119624569+c.upper)) = pointBounds62720 := by
 decide +kernel
def cuts62721 : List PrefixCut := [⟨64,193525521,193525636⟩]
theorem checked62721 : checkPrefixCuts (2^48) 8224899073 10 Manual.Count131072.C062721.packed 64 cuts62721 = true := by
 decide +kernel
def cuts62722 : List PrefixCut := [⟨40,125250961,125251031⟩,
⟨64,198655654,198655769⟩]
theorem checked62722 : checkPrefixCuts (2^48) 8225030145 10 Manual.Count131072.C062722.packed 64 cuts62722 = true := by
 decide +kernel
def pointBounds62722 : List (Nat × Nat × Nat) := [(8225112064,114464245775755,114464634496635)]
theorem point_links_checked62722 : (cuts62722.take 1).map (fun c => (8225030145-1+2*2^10*c.k,114464120524794+c.lower,114464509245604+c.upper)) = pointBounds62722 := by
 decide +kernel
def cuts62723 : List PrefixCut := [⟨64,191705636,191705745⟩]
theorem checked62723 : checkPrefixCuts (2^48) 8225161217 10 Manual.Count131072.C062723.packed 64 cuts62723 = true := by
 decide +kernel
def cuts62724 : List PrefixCut := [⟨38,116897206,116897271⟩,
⟨64,195056189,195056301⟩]
theorem checked62724 : checkPrefixCuts (2^48) 8225292289 10 Manual.Count131072.C062724.packed 64 cuts62724 = true := by
 decide +kernel
def pointBounds62724 : List (Nat × Nat × Nat) := [(8225370112,114464627783290,114465016504389)]
theorem point_links_checked62724 : (cuts62724.take 1).map (fun c => (8225292289-1+2*2^10*c.k,114464510886084+c.lower,114464899607118+c.upper)) = pointBounds62724 := by
 decide +kernel
def cuts62725 : List PrefixCut := [⟨64,195224182,195224296⟩]
theorem checked62725 : checkPrefixCuts (2^48) 8225423361 10 Manual.Count131072.C062725.packed 64 cuts62725 = true := by
 decide +kernel
def cuts62726 : List PrefixCut := [⟨36,110254940,110255004⟩,
⟨64,197684839,197684953⟩]
theorem checked62726 : checkPrefixCuts (2^48) 8225554433 10 Manual.Count131072.C062726.packed 64 cuts62726 = true := by
 decide +kernel
def pointBounds62726 : List (Nat × Nat × Nat) := [(8225628160,114465011421395,114465400142719)]
theorem point_links_checked62726 : (cuts62726.take 1).map (fun c => (8225554433-1+2*2^10*c.k,114464901166455+c.lower,114465289887715+c.upper)) = pointBounds62726 := by
 decide +kernel
def cuts62727 : List PrefixCut := [⟨64,198331862,198331981⟩]
theorem checked62727 : checkPrefixCuts (2^48) 8225685505 10 Manual.Count131072.C062727.packed 64 cuts62727 = true := by
 decide +kernel
def cuts62728 : List PrefixCut := [⟨34,102791856,102791918⟩,
⟨64,196275587,196275704⟩]
theorem checked62728 : checkPrefixCuts (2^48) 8225816577 10 Manual.Count131072.C062728.packed 64 cuts62728 = true := by
 decide +kernel
def pointBounds62728 : List (Nat × Nat × Nat) := [(8225886208,114465399975012,114465788696567)]
theorem point_links_checked62728 : (cuts62728.take 1).map (fun c => (8225816577-1+2*2^10*c.k,114465297183156+c.lower,114465685904649+c.upper)) = pointBounds62728 := by
 decide +kernel
def cuts62729 : List PrefixCut := [⟨64,194801115,194801222⟩]
theorem checked62729 : checkPrefixCuts (2^48) 8225947649 10 Manual.Count131072.C062729.packed 64 cuts62729 = true := by
 decide +kernel
def cuts62730 : List PrefixCut := [⟨32,96355770,96355829⟩,
⟨64,194763790,194763905⟩]
theorem checked62730 : checkPrefixCuts (2^48) 8226078721 10 Manual.Count131072.C062730.packed 64 cuts62730 = true := by
 decide +kernel
def pointBounds62730 : List (Nat × Nat × Nat) := [(8226144256,114465784615628,114466173337404)]
theorem point_links_checked62730 : (cuts62730.take 1).map (fun c => (8226078721-1+2*2^10*c.k,114465688259858+c.lower,114466076981575+c.upper)) = pointBounds62730 := by
 decide +kernel
def cuts62731 : List PrefixCut := [⟨64,197737534,197737647⟩]
theorem checked62731 : checkPrefixCuts (2^48) 8226209793 10 Manual.Count131072.C062731.packed 64 cuts62731 = true := by
 decide +kernel
def cuts62732 : List PrefixCut := [⟨30,92109915,92109966⟩,
⟨64,195476135,195476248⟩]
theorem checked62732 : checkPrefixCuts (2^48) 8226340865 10 Manual.Count131072.C062732.packed 64 cuts62732 = true := by
 decide +kernel
def pointBounds62732 : List (Nat × Nat × Nat) := [(8226402304,114466172871097,114466561593093)]
theorem point_links_checked62732 : (cuts62732.take 1).map (fun c => (8226340865-1+2*2^10*c.k,114466080761182+c.lower,114466469483127+c.upper)) = pointBounds62732 := by
 decide +kernel
def cuts62733 : List PrefixCut := [⟨64,194583425,194583538⟩]
theorem checked62733 : checkPrefixCuts (2^48) 8226471937 10 Manual.Count131072.C062733.packed 64 cuts62733 = true := by
 decide +kernel
def cuts62734 : List PrefixCut := [⟨28,86085153,86085202⟩,
⟨64,196633208,196633323⟩]
theorem checked62734 : checkPrefixCuts (2^48) 8226603009 10 Manual.Count131072.C062734.packed 64 cuts62734 = true := by
 decide +kernel
def pointBounds62734 : List (Nat × Nat × Nat) := [(8226660352,114466556905895,114466945628115)]
theorem point_links_checked62734 : (cuts62734.take 1).map (fun c => (8226603009-1+2*2^10*c.k,114466470820742+c.lower,114466859542913+c.upper)) = pointBounds62734 := by
 decide +kernel
def cuts62735 : List PrefixCut := [⟨64,192592782,192592893⟩]
theorem checked62735 : checkPrefixCuts (2^48) 8226734081 10 Manual.Count131072.C062735.packed 64 cuts62735 = true := by
 decide +kernel
def cuts62736 : List PrefixCut := [⟨26,80505551,80505598⟩,
⟨64,197550719,197550833⟩]
theorem checked62736 : checkPrefixCuts (2^48) 8226865153 10 Manual.Count131072.C062736.packed 64 cuts62736 = true := by
 decide +kernel
def pointBounds62736 : List (Nat × Nat × Nat) := [(8226918400,114466940552283,114467329274727)]
theorem point_links_checked62736 : (cuts62736.take 1).map (fun c => (8226865153-1+2*2^10*c.k,114466860046732+c.lower,114467248769129+c.upper)) = pointBounds62736 := by
 decide +kernel
def cuts62737 : List PrefixCut := [⟨64,196350111,196350219⟩]
theorem checked62737 : checkPrefixCuts (2^48) 8226996225 10 Manual.Count131072.C062737.packed 64 cuts62737 = true := by
 decide +kernel
def cuts62738 : List PrefixCut := [⟨24,74002549,74002592⟩,
⟨64,198365530,198365646⟩]
theorem checked62738 : checkPrefixCuts (2^48) 8227127297 10 Manual.Count131072.C062738.packed 64 cuts62738 = true := by
 decide +kernel
def pointBounds62738 : List (Nat × Nat × Nat) := [(8227176448,114467327950111,114467716672773)]
theorem point_links_checked62738 : (cuts62738.take 1).map (fun c => (8227127297-1+2*2^10*c.k,114467253947562+c.lower,114467642670181+c.upper)) = pointBounds62738 := by
 decide +kernel
def cuts62739 : List PrefixCut := [⟨64,197814976,197815088⟩]
theorem checked62739 : checkPrefixCuts (2^48) 8227258369 10 Manual.Count131072.C062739.packed 64 cuts62739 = true := by
 decide +kernel
def cuts62740 : List PrefixCut := [⟨22,67636804,67636845⟩,
⟨64,195109096,195109210⟩]
theorem checked62740 : checkPrefixCuts (2^48) 8227389441 10 Manual.Count131072.C062740.packed 64 cuts62740 = true := by
 decide +kernel
def pointBounds62740 : List (Nat × Nat × Nat) := [(8227434496,114467717764872,114468106487760)]
theorem point_links_checked62740 : (cuts62740.take 1).map (fun c => (8227389441-1+2*2^10*c.k,114467650128068+c.lower,114468038850915+c.upper)) = pointBounds62740 := by
 decide +kernel
def cuts62741 : List PrefixCut := [⟨64,197808682,197808791⟩]
theorem checked62741 : checkPrefixCuts (2^48) 8227520513 10 Manual.Count131072.C062741.packed 64 cuts62741 = true := by
 decide +kernel
def cuts62742 : List PrefixCut := [⟨20,62024108,62024141⟩,
⟨64,195923949,195924058⟩]
theorem checked62742 : checkPrefixCuts (2^48) 8227651585 10 Manual.Count131072.C062742.packed 64 cuts62742 = true := by
 decide +kernel
def pointBounds62742 : List (Nat × Nat × Nat) := [(8227692544,114468105069954,114468493793057)]
theorem point_links_checked62742 : (cuts62742.take 1).map (fun c => (8227651585-1+2*2^10*c.k,114468043045846+c.lower,114468431768916+c.upper)) = pointBounds62742 := by
 decide +kernel
def cuts62743 : List PrefixCut := [⟨64,195681343,195681456⟩]
theorem checked62743 : checkPrefixCuts (2^48) 8227782657 10 Manual.Count131072.C062743.packed 64 cuts62743 = true := by
 decide +kernel
def cuts62744 : List PrefixCut := [⟨18,55761773,55761804⟩,
⟨64,196978195,196978305⟩]
theorem checked62744 : checkPrefixCuts (2^48) 8227913729 10 Manual.Count131072.C062744.packed 64 cuts62744 = true := by
 decide +kernel
def pointBounds62744 : List (Nat × Nat × Nat) := [(8227950592,114468490412911,114468879136234)]
theorem point_links_checked62744 : (cuts62744.take 1).map (fun c => (8227913729-1+2*2^10*c.k,114468434651138+c.lower,114468823374430+c.upper)) = pointBounds62744 := by
 decide +kernel
def cuts62745 : List PrefixCut := [⟨64,196290868,196290984⟩]
theorem checked62745 : checkPrefixCuts (2^48) 8228044801 10 Manual.Count131072.C062745.packed 64 cuts62745 = true := by
 decide +kernel
def cuts62746 : List PrefixCut := [⟨16,48131492,48131520⟩,
⟨64,193311609,193311730⟩]
theorem checked62746 : checkPrefixCuts (2^48) 8228175873 10 Manual.Count131072.C062746.packed 64 cuts62746 = true := by
 decide +kernel
def pointBounds62746 : List (Nat × Nat × Nat) := [(8228208640,114468876051693,114469264775239)]
theorem point_links_checked62746 : (cuts62746.take 1).map (fun c => (8228175873-1+2*2^10*c.k,114468827920201+c.lower,114469216643719+c.upper)) = pointBounds62746 := by
 decide +kernel
def cuts62747 : List PrefixCut := [⟨64,195463630,195463739⟩]
theorem checked62747 : checkPrefixCuts (2^48) 8228306945 10 Manual.Count131072.C062747.packed 64 cuts62747 = true := by
 decide +kernel
def cuts62748 : List PrefixCut := [⟨14,44196107,44196133⟩,
⟨64,194434302,194434420⟩]
theorem checked62748 : checkPrefixCuts (2^48) 8228438017 10 Manual.Count131072.C062748.packed 64 cuts62748 = true := by
 decide +kernel
def pointBounds62748 : List (Nat × Nat × Nat) := [(8228466688,114469260891547,114469649615321)]
theorem point_links_checked62748 : (cuts62748.take 1).map (fun c => (8228438017-1+2*2^10*c.k,114469216695440+c.lower,114469605419188+c.upper)) = pointBounds62748 := by
 decide +kernel
def cuts62749 : List PrefixCut := [⟨64,194568017,194568132⟩]
theorem checked62749 : checkPrefixCuts (2^48) 8228569089 10 Manual.Count131072.C062749.packed 64 cuts62749 = true := by
 decide +kernel
def cuts62750 : List PrefixCut := [⟨12,38413822,38413845⟩,
⟨64,197746113,197746228⟩]
theorem checked62750 : checkPrefixCuts (2^48) 8228700161 10 Manual.Count131072.C062750.packed 64 cuts62750 = true := by
 decide +kernel
def pointBounds62750 : List (Nat × Nat × Nat) := [(8228724736,114469644111581,114470032835585)]
theorem point_links_checked62750 : (cuts62750.take 1).map (fun c => (8228700161-1+2*2^10*c.k,114469605697759+c.lower,114469994421740+c.upper)) = pointBounds62750 := by
 decide +kernel
def cuts62751 : List PrefixCut := [⟨64,193296215,193296321⟩]
theorem checked62751 : checkPrefixCuts (2^48) 8228831233 10 Manual.Count131072.C062751.packed 64 cuts62751 = true := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S7.B000085
