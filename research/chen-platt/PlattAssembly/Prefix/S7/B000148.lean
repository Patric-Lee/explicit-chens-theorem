import PlattAssemblyKernel
import PlattCertificates.Count131072.C064736
import PlattCertificates.Count131072.C064737
import PlattCertificates.Count131072.C064738
import PlattCertificates.Count131072.C064739
import PlattCertificates.Count131072.C064740
import PlattCertificates.Count131072.C064741
import PlattCertificates.Count131072.C064742
import PlattCertificates.Count131072.C064743
import PlattCertificates.Count131072.C064744
import PlattCertificates.Count131072.C064745
import PlattCertificates.Count131072.C064746
import PlattCertificates.Count131072.C064747
import PlattCertificates.Count131072.C064748
import PlattCertificates.Count131072.C064749
import PlattCertificates.Count131072.C064750
import PlattCertificates.Count131072.C064751
import PlattCertificates.Count131072.C064752
import PlattCertificates.Count131072.C064753
import PlattCertificates.Count131072.C064754
import PlattCertificates.Count131072.C064755
import PlattCertificates.Count131072.C064756
import PlattCertificates.Count131072.C064757
import PlattCertificates.Count131072.C064758
import PlattCertificates.Count131072.C064759
import PlattCertificates.Count131072.C064760
import PlattCertificates.Count131072.C064761
import PlattCertificates.Count131072.C064762
import PlattCertificates.Count131072.C064763
import PlattCertificates.Count131072.C064764
import PlattCertificates.Count131072.C064765
import PlattCertificates.Count131072.C064766
import PlattCertificates.Count131072.C064767
namespace ChenEffective.PlattWindow.Assembly.Prefix.S7.B000148
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts64736 : List PrefixCut := [⟨46,135514223,135514299⟩,
⟨64,188234058,188234164⟩]
theorem checked64736 : checkPrefixCuts (2^48) 8489009153 10 Manual.Count131072.C064736.packed 64 cuts64736 = true := by
 decide +kernel
def pointBounds64736 : List (Nat × Nat × Nat) := [(8489103360,114853455191948,114853844137076)]
theorem point_links_checked64736 : (cuts64736.take 1).map (fun c => (8489009153-1+2*2^10*c.k,114853319677725+c.lower,114853708622777+c.upper)) = pointBounds64736 := by
 decide +kernel
def cuts64737 : List PrefixCut := [⟨64,194033585,194033699⟩]
theorem checked64737 : checkPrefixCuts (2^48) 8489140225 10 Manual.Count131072.C064737.packed 64 cuts64737 = true := by
 decide +kernel
def cuts64738 : List PrefixCut := [⟨48,143036503,143036584⟩,
⟨64,192173837,192173947⟩]
theorem checked64738 : checkPrefixCuts (2^48) 8489271297 10 Manual.Count131072.C064738.packed 64 cuts64738 = true := by
 decide +kernel
def pointBounds64738 : List (Nat × Nat × Nat) := [(8489369600,114853844981871,114854233927224)]
theorem point_links_checked64738 : (cuts64738.take 1).map (fun c => (8489271297-1+2*2^10*c.k,114853701945368+c.lower,114854090890640+c.upper)) = pointBounds64738 := by
 decide +kernel
def cuts64739 : List PrefixCut := [⟨64,190977276,190977382⟩]
theorem checked64739 : checkPrefixCuts (2^48) 8489402369 10 Manual.Count131072.C064739.packed 64 cuts64739 = true := by
 decide +kernel
def cuts64740 : List PrefixCut := [⟨50,148568991,148569077⟩,
⟨64,191239559,191239670⟩]
theorem checked64740 : checkPrefixCuts (2^48) 8489533441 10 Manual.Count131072.C064740.packed 64 cuts64740 = true := by
 decide +kernel
def pointBounds64740 : List (Nat × Nat × Nat) := [(8489635840,114854233665472,114854622611046)]
theorem point_links_checked64740 : (cuts64740.take 1).map (fun c => (8489533441-1+2*2^10*c.k,114854085096481+c.lower,114854474041969+c.upper)) = pointBounds64740 := by
 decide +kernel
def cuts64741 : List PrefixCut := [⟨64,191601320,191601430⟩]
theorem checked64741 : checkPrefixCuts (2^48) 8489664513 10 Manual.Count131072.C064741.packed 64 cuts64741 = true := by
 decide +kernel
def cuts64742 : List PrefixCut := [⟨52,154731072,154731158⟩,
⟨64,190802660,190802766⟩]
theorem checked64742 : checkPrefixCuts (2^48) 8489795585 10 Manual.Count131072.C064742.packed 64 cuts64742 = true := by
 decide +kernel
def pointBounds64742 : List (Nat × Nat × Nat) := [(8489902080,114854622668432,114855011614227)]
theorem point_links_checked64742 : (cuts64742.take 1).map (fun c => (8489795585-1+2*2^10*c.k,114854467937360+c.lower,114854856883069+c.upper)) = pointBounds64742 := by
 decide +kernel
def cuts64743 : List PrefixCut := [⟨64,188611571,188611678⟩]
theorem checked64743 : checkPrefixCuts (2^48) 8489926657 10 Manual.Count131072.C064743.packed 64 cuts64743 = true := by
 decide +kernel
def cuts64744 : List PrefixCut := [⟨54,160528068,160528160⟩,
⟨64,190332615,190332725⟩]
theorem checked64744 : checkPrefixCuts (2^48) 8490057729 10 Manual.Count131072.C064744.packed 64 cuts64744 = true := by
 decide +kernel
def pointBounds64744 : List (Nat × Nat × Nat) := [(8490168320,114855007879659,114855396825673)]
theorem point_links_checked64744 : (cuts64744.take 1).map (fun c => (8490057729-1+2*2^10*c.k,114854847351591+c.lower,114855236297513+c.upper)) = pointBounds64744 := by
 decide +kernel
def cuts64745 : List PrefixCut := [⟨64,189666616,189666725⟩]
theorem checked64745 : checkPrefixCuts (2^48) 8490188801 10 Manual.Count131072.C064745.packed 64 cuts64745 = true := by
 decide +kernel
def cuts64746 : List PrefixCut := [⟨56,166888301,166888398⟩,
⟨64,190989783,190989893⟩]
theorem checked64746 : checkPrefixCuts (2^48) 8490319873 10 Manual.Count131072.C064746.packed 64 cuts64746 = true := by
 decide +kernel
def pointBounds64746 : List (Nat × Nat × Nat) := [(8490434560,114855394239123,114855783185361)]
theorem point_links_checked64746 : (cuts64746.take 1).map (fun c => (8490319873-1+2*2^10*c.k,114855227350822+c.lower,114855616296963+c.upper)) = pointBounds64746 := by
 decide +kernel
def cuts64747 : List PrefixCut := [⟨64,190356950,190357055⟩]
theorem checked64747 : checkPrefixCuts (2^48) 8490450945 10 Manual.Count131072.C064747.packed 64 cuts64747 = true := by
 decide +kernel
def cuts64748 : List PrefixCut := [⟨58,172883474,172883576⟩,
⟨64,191182792,191182904⟩]
theorem checked64748 : checkPrefixCuts (2^48) 8490582017 10 Manual.Count131072.C064748.packed 64 cuts64748 = true := by
 decide +kernel
def pointBounds64748 : List (Nat × Nat × Nat) := [(8490700800,114855781581029,114856170527487)]
theorem point_links_checked64748 : (cuts64748.take 1).map (fun c => (8490582017-1+2*2^10*c.k,114855608697555+c.lower,114855997643911+c.upper)) = pointBounds64748 := by
 decide +kernel
def cuts64749 : List PrefixCut := [⟨64,189389708,189389819⟩]
theorem checked64749 : checkPrefixCuts (2^48) 8490713089 10 Manual.Count131072.C064749.packed 64 cuts64749 = true := by
 decide +kernel
def cuts64750 : List PrefixCut := [⟨60,175795311,175795416⟩,
⟨64,188027626,188027739⟩]
theorem checked64750 : checkPrefixCuts (2^48) 8490844161 10 Manual.Count131072.C064750.packed 64 cuts64750 = true := by
 decide +kernel
def pointBounds64750 : List (Nat × Nat × Nat) := [(8490967040,114856165065366,114856554012050)]
theorem point_links_checked64750 : (cuts64750.take 1).map (fun c => (8490844161-1+2*2^10*c.k,114855989270055+c.lower,114856378216634+c.upper)) = pointBounds64750 := by
 decide +kernel
def cuts64751 : List PrefixCut := [⟨64,188124163,188124274⟩]
theorem checked64751 : checkPrefixCuts (2^48) 8490975233 10 Manual.Count131072.C064751.packed 64 cuts64751 = true := by
 decide +kernel
def cuts64752 : List PrefixCut := [⟨62,185171052,185171155⟩,
⟨64,191535636,191535743⟩]
theorem checked64752 : checkPrefixCuts (2^48) 8491106305 10 Manual.Count131072.C064752.packed 64 cuts64752 = true := by
 decide +kernel
def pointBounds64752 : List (Nat × Nat × Nat) := [(8491233280,114856550592896,114856939539802)]
theorem point_links_checked64752 : (cuts64752.take 1).map (fun c => (8491106305-1+2*2^10*c.k,114856365421844+c.lower,114856754368647+c.upper)) = pointBounds64752 := by
 decide +kernel
def cuts64753 : List PrefixCut := [⟨64,186427792,186427902⟩]
theorem checked64753 : checkPrefixCuts (2^48) 8491237377 10 Manual.Count131072.C064753.packed 64 cuts64753 = true := by
 decide +kernel
def cuts64754 : List PrefixCut := [⟨64,188513246,188513353⟩]
theorem checked64754 : checkPrefixCuts (2^48) 8491368449 10 Manual.Count131072.C064754.packed 64 cuts64754 = true := by
 decide +kernel
def pointBounds64754 : List (Nat × Nat × Nat) := [(8491499520,114856931898518,114857320845645)]
theorem point_links_checked64754 : (cuts64754.take 1).map (fun c => (8491368449-1+2*2^10*c.k,114856743385272+c.lower,114857132332292+c.upper)) = pointBounds64754 := by
 decide +kernel
def cuts64755 : List PrefixCut := [⟨64,190565477,190565586⟩]
theorem checked64755 : checkPrefixCuts (2^48) 8491499521 10 Manual.Count131072.C064755.packed 64 cuts64755 = true := by
 decide +kernel
def cuts64756 : List PrefixCut := [⟨64,192253047,192253159⟩]
theorem checked64756 : checkPrefixCuts (2^48) 8491630593 10 Manual.Count131072.C064756.packed 64 cuts64756 = true := by
 decide +kernel
def cuts64757 : List PrefixCut := [⟨2,5701252,5701255⟩,
⟨64,188438225,188438339⟩]
theorem checked64757 : checkPrefixCuts (2^48) 8491761665 10 Manual.Count131072.C064757.packed 64 cuts64757 = true := by
 decide +kernel
def pointBounds64757 : List (Nat × Nat × Nat) := [(8491765760,114857320418294,114857709365645)]
theorem point_links_checked64757 : (cuts64757.take 1).map (fun c => (8491761665-1+2*2^10*c.k,114857314717042+c.lower,114857703664390+c.upper)) = pointBounds64757 := by
 decide +kernel
def cuts64758 : List PrefixCut := [⟨64,191285878,191285990⟩]
theorem checked64758 : checkPrefixCuts (2^48) 8491892737 10 Manual.Count131072.C064758.packed 64 cuts64758 = true := by
 decide +kernel
def cuts64759 : List PrefixCut := [⟨4,11534731,11534739⟩,
⟨64,190918305,190918420⟩]
theorem checked64759 : checkPrefixCuts (2^48) 8492023809 10 Manual.Count131072.C064759.packed 64 cuts64759 = true := by
 decide +kernel
def pointBounds64759 : List (Nat × Nat × Nat) := [(8492032000,114857705975876,114858094923458)]
theorem point_links_checked64759 : (cuts64759.take 1).map (fun c => (8492023809-1+2*2^10*c.k,114857694441145+c.lower,114858083388719+c.upper)) = pointBounds64759 := by
 decide +kernel
def cuts64760 : List PrefixCut := [⟨64,192473190,192473299⟩]
theorem checked64760 : checkPrefixCuts (2^48) 8492154881 10 Manual.Count131072.C064760.packed 64 cuts64760 = true := by
 decide +kernel
def cuts64761 : List PrefixCut := [⟨6,18163323,18163332⟩,
⟨64,191674750,191674857⟩]
theorem checked64761 : checkPrefixCuts (2^48) 8492285953 10 Manual.Count131072.C064761.packed 64 cuts64761 = true := by
 decide +kernel
def pointBounds64761 : List (Nat × Nat × Nat) := [(8492298240,114858095995963,114858484943770)]
theorem point_links_checked64761 : (cuts64761.take 1).map (fun c => (8492285953-1+2*2^10*c.k,114858077832640+c.lower,114858466780438+c.upper)) = pointBounds64761 := by
 decide +kernel
def cuts64762 : List PrefixCut := [⟨64,190014588,190014695⟩]
theorem checked64762 : checkPrefixCuts (2^48) 8492417025 10 Manual.Count131072.C064762.packed 64 cuts64762 = true := by
 decide +kernel
def cuts64763 : List PrefixCut := [⟨8,24128627,24128640⟩,
⟨64,190541952,190542060⟩]
theorem checked64763 : checkPrefixCuts (2^48) 8492548097 10 Manual.Count131072.C064763.packed 64 cuts64763 = true := by
 decide +kernel
def pointBounds64763 : List (Nat × Nat × Nat) := [(8492564480,114858483650605,114858872598630)]
theorem point_links_checked64763 : (cuts64763.take 1).map (fun c => (8492548097-1+2*2^10*c.k,114858459521978+c.lower,114858848469990+c.upper)) = pointBounds64763 := by
 decide +kernel
def cuts64764 : List PrefixCut := [⟨64,191235020,191235133⟩]
theorem checked64764 : checkPrefixCuts (2^48) 8492679169 10 Manual.Count131072.C064764.packed 64 cuts64764 = true := by
 decide +kernel
def cuts64765 : List PrefixCut := [⟨10,29132424,29132440⟩,
⟨64,191132633,191132745⟩]
theorem checked64765 : checkPrefixCuts (2^48) 8492810241 10 Manual.Count131072.C064765.packed 64 cuts64765 = true := by
 decide +kernel
def pointBounds64765 : List (Nat × Nat × Nat) := [(8492830720,114858870431374,114859259379623)]
theorem point_links_checked64765 : (cuts64765.take 1).map (fun c => (8492810241-1+2*2^10*c.k,114858841298950+c.lower,114859230247183+c.upper)) = pointBounds64765 := by
 decide +kernel
def cuts64766 : List PrefixCut := [⟨64,186986933,186987039⟩]
theorem checked64766 : checkPrefixCuts (2^48) 8492941313 10 Manual.Count131072.C064766.packed 64 cuts64766 = true := by
 decide +kernel
def cuts64767 : List PrefixCut := [⟨12,34732454,34732477⟩,
⟨64,188707401,188707515⟩]
theorem checked64767 : checkPrefixCuts (2^48) 8493072385 10 Manual.Count131072.C064767.packed 64 cuts64767 = true := by
 decide +kernel
def pointBounds64767 : List (Nat × Nat × Nat) := [(8493096960,114859254150970,114859643099444)]
theorem point_links_checked64767 : (cuts64767.take 1).map (fun c => (8493072385-1+2*2^10*c.k,114859219418516+c.lower,114859608366967+c.upper)) = pointBounds64767 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S7.B000148
