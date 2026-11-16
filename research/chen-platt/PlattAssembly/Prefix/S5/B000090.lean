import PlattAssemblyKernel
import PlattCertificates.Count131072.C042880
import PlattCertificates.Count131072.C042881
import PlattCertificates.Count131072.C042882
import PlattCertificates.Count131072.C042883
import PlattCertificates.Count131072.C042884
import PlattCertificates.Count131072.C042885
import PlattCertificates.Count131072.C042886
import PlattCertificates.Count131072.C042887
import PlattCertificates.Count131072.C042888
import PlattCertificates.Count131072.C042889
import PlattCertificates.Count131072.C042890
import PlattCertificates.Count131072.C042891
import PlattCertificates.Count131072.C042892
import PlattCertificates.Count131072.C042893
import PlattCertificates.Count131072.C042894
import PlattCertificates.Count131072.C042895
import PlattCertificates.Count131072.C042896
import PlattCertificates.Count131072.C042897
import PlattCertificates.Count131072.C042898
import PlattCertificates.Count131072.C042899
import PlattCertificates.Count131072.C042900
import PlattCertificates.Count131072.C042901
import PlattCertificates.Count131072.C042902
import PlattCertificates.Count131072.C042903
import PlattCertificates.Count131072.C042904
import PlattCertificates.Count131072.C042905
import PlattCertificates.Count131072.C042906
import PlattCertificates.Count131072.C042907
import PlattCertificates.Count131072.C042908
import PlattCertificates.Count131072.C042909
import PlattCertificates.Count131072.C042910
import PlattCertificates.Count131072.C042911
namespace ChenEffective.PlattWindow.Assembly.Prefix.S5.B000090
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts42880 : List PrefixCut := [⟨52,240720032,240720175⟩,
⟨64,296670516,296670692⟩]
theorem checked42880 : checkPrefixCuts (2^48) 5624299521 10 Manual.Count131072.C042880.packed 64 cuts42880 = true := by
 decide +kernel
def pointBounds42880 : List (Nat × Nat × Nat) := [(5624406016,109738891177456,109739277196588)]
theorem point_links_checked42880 : (cuts42880.take 1).map (fun c => (5624299521-1+2*2^10*c.k,109738650457424+c.lower,109739036476413+c.upper)) = pointBounds42880 := by
 decide +kernel
def cuts42881 : List PrefixCut := [⟨64,291008550,291008719⟩]
theorem checked42881 : checkPrefixCuts (2^48) 5624430593 10 Manual.Count131072.C042881.packed 64 cuts42881 = true := by
 decide +kernel
def cuts42882 : List PrefixCut := [⟨10,44839235,44839264⟩,
⟨64,290601414,290601587⟩]
theorem checked42882 : checkPrefixCuts (2^48) 5624561665 10 Manual.Count131072.C042882.packed 64 cuts42882 = true := by
 decide +kernel
def pointBounds42882 : List (Nat × Nat × Nat) := [(5624582144,109739282975725,109739668995088)]
theorem point_links_checked42882 : (cuts42882.take 1).map (fun c => (5624561665-1+2*2^10*c.k,109739238136490+c.lower,109739624155824+c.upper)) = pointBounds42882 := by
 decide +kernel
def cuts42883 : List PrefixCut := [⟨32,147174768,147174855⟩,
⟨64,294648068,294648240⟩]
theorem checked42883 : checkPrefixCuts (2^48) 5624692737 10 Manual.Count131072.C042883.packed 64 cuts42883 = true := by
 decide +kernel
def pointBounds42883 : List (Nat × Nat × Nat) := [(5624758272,109739675912672,109740061932266)]
theorem point_links_checked42883 : (cuts42883.take 1).map (fun c => (5624692737-1+2*2^10*c.k,109739528737904+c.lower,109739914757411+c.upper)) = pointBounds42883 := by
 decide +kernel
def cuts42884 : List PrefixCut := [⟨54,244200358,244200507⟩,
⟨64,288686339,288686516⟩]
theorem checked42884 : checkPrefixCuts (2^48) 5624823809 10 Manual.Count131072.C042884.packed 64 cuts42884 = true := by
 decide +kernel
def pointBounds42884 : List (Nat × Nat × Nat) := [(5624934400,109740067586330,109740453606158)]
theorem point_links_checked42884 : (cuts42884.take 1).map (fun c => (5624823809-1+2*2^10*c.k,109739823385972+c.lower,109740209405651+c.upper)) = pointBounds42884 := by
 decide +kernel
def cuts42885 : List PrefixCut := [⟨64,292582688,292582861⟩]
theorem checked42885 : checkPrefixCuts (2^48) 5624954881 10 Manual.Count131072.C042885.packed 64 cuts42885 = true := by
 decide +kernel
def cuts42886 : List PrefixCut := [⟨12,54292430,54292462⟩,
⟨64,290974646,290974817⟩]
theorem checked42886 : checkPrefixCuts (2^48) 5625085953 10 Manual.Count131072.C042886.packed 64 cuts42886 = true := by
 decide +kernel
def pointBounds42886 : List (Nat × Nat × Nat) := [(5625110528,109740458947429,109740844967490)]
theorem point_links_checked42886 : (cuts42886.take 1).map (fun c => (5625085953-1+2*2^10*c.k,109740404654999+c.lower,109740790675028+c.upper)) = pointBounds42886 := by
 decide +kernel
def cuts42887 : List PrefixCut := [⟨34,156818279,156818371⟩,
⟨64,294820759,294820932⟩]
theorem checked42887 : checkPrefixCuts (2^48) 5625217025 10 Manual.Count131072.C042887.packed 64 cuts42887 = true := by
 decide +kernel
def pointBounds42887 : List (Nat × Nat × Nat) := [(5625286656,109740852447924,109741238468216)]
theorem point_links_checked42887 : (cuts42887.take 1).map (fun c => (5625217025-1+2*2^10*c.k,109740695629645+c.lower,109741081649845+c.upper)) = pointBounds42887 := by
 decide +kernel
def cuts42888 : List PrefixCut := [⟨56,250181875,250182026⟩,
⟨64,286407787,286407961⟩]
theorem checked42888 : checkPrefixCuts (2^48) 5625348097 10 Manual.Count131072.C042888.packed 64 cuts42888 = true := by
 decide +kernel
def pointBounds42888 : List (Nat × Nat × Nat) := [(5625462784,109741240632279,109741626652803)]
theorem point_links_checked42888 : (cuts42888.take 1).map (fun c => (5625348097-1+2*2^10*c.k,109740990450404+c.lower,109741376470777+c.upper)) = pointBounds42888 := by
 decide +kernel
def cuts42889 : List PrefixCut := [⟨64,291904967,291905138⟩]
theorem checked42889 : checkPrefixCuts (2^48) 5625479169 10 Manual.Count131072.C042889.packed 64 cuts42889 = true := by
 decide +kernel
def cuts42890 : List PrefixCut := [⟨14,64544410,64544449⟩,
⟨64,295700749,295700926⟩]
theorem checked42890 : checkPrefixCuts (2^48) 5625610241 10 Manual.Count131072.C042890.packed 64 cuts42890 = true := by
 decide +kernel
def pointBounds42890 : List (Nat × Nat × Nat) := [(5625638912,109741633307568,109742019328325)]
theorem point_links_checked42890 : (cuts42890.take 1).map (fun c => (5625610241-1+2*2^10*c.k,109741568763158+c.lower,109741954783876+c.upper)) = pointBounds42890 := by
 decide +kernel
def cuts42891 : List PrefixCut := [⟨36,164908950,164909044⟩,
⟨64,293592481,293592645⟩]
theorem checked42891 : checkPrefixCuts (2^48) 5625741313 10 Manual.Count131072.C042891.packed 64 cuts42891 = true := by
 decide +kernel
def pointBounds42891 : List (Nat × Nat × Nat) := [(5625815040,109742029372857,109742415393846)]
theorem point_links_checked42891 : (cuts42891.take 1).map (fun c => (5625741313-1+2*2^10*c.k,109741864463907+c.lower,109742250484802+c.upper)) = pointBounds42891 := by
 decide +kernel
def cuts42892 : List PrefixCut := [⟨58,261765822,261765973⟩,
⟨64,289232901,289233068⟩]
theorem checked42892 : checkPrefixCuts (2^48) 5625872385 10 Manual.Count131072.C042892.packed 64 cuts42892 = true := by
 decide +kernel
def pointBounds42892 : List (Nat × Nat × Nat) := [(5625991168,109742419822210,109742805843420)]
theorem point_links_checked42892 : (cuts42892.take 1).map (fun c => (5625872385-1+2*2^10*c.k,109742158056388+c.lower,109742544077447+c.upper)) = pointBounds42892 := by
 decide +kernel
def cuts42893 : List PrefixCut := [⟨64,292528144,292528318⟩]
theorem checked42893 : checkPrefixCuts (2^48) 5626003457 10 Manual.Count131072.C042893.packed 64 cuts42893 = true := by
 decide +kernel
def cuts42894 : List PrefixCut := [⟨16,75745032,75745076⟩,
⟨64,296423668,296423839⟩]
theorem checked42894 : checkPrefixCuts (2^48) 5626134529 10 Manual.Count131072.C042894.packed 64 cuts42894 = true := by
 decide +kernel
def pointBounds42894 : List (Nat × Nat × Nat) := [(5626167296,109742815562465,109743201583909)]
theorem point_links_checked42894 : (cuts42894.take 1).map (fun c => (5626134529-1+2*2^10*c.k,109742739817433+c.lower,109743125838833+c.upper)) = pointBounds42894 := by
 decide +kernel
def cuts42895 : List PrefixCut := [⟨38,175749690,175749793⟩,
⟨64,293264978,293265155⟩]
theorem checked42895 : checkPrefixCuts (2^48) 5626265601 10 Manual.Count131072.C042895.packed 64 cuts42895 = true := by
 decide +kernel
def pointBounds42895 : List (Nat × Nat × Nat) := [(5626343424,109743211990791,109743598012465)]
theorem point_links_checked42895 : (cuts42895.take 1).map (fun c => (5626265601-1+2*2^10*c.k,109743036241101+c.lower,109743422262672+c.upper)) = pointBounds42895 := by
 decide +kernel
def cuts42896 : List PrefixCut := [⟨60,272146955,272147111⟩,
⟨64,291557210,291557377⟩]
theorem checked42896 : checkPrefixCuts (2^48) 5626396673 10 Manual.Count131072.C042896.packed 64 cuts42896 = true := by
 decide +kernel
def pointBounds42896 : List (Nat × Nat × Nat) := [(5626519552,109743601653034,109743987674938)]
theorem point_links_checked42896 : (cuts42896.take 1).map (fun c => (5626396673-1+2*2^10*c.k,109743329506079+c.lower,109743715527827+c.upper)) = pointBounds42896 := by
 decide +kernel
def cuts42897 : List PrefixCut := [⟨64,292050693,292050864⟩]
theorem checked42897 : checkPrefixCuts (2^48) 5626527745 10 Manual.Count131072.C042897.packed 64 cuts42897 = true := by
 decide +kernel
def cuts42898 : List PrefixCut := [⟨18,83741957,83742005⟩,
⟨64,293894813,293894977⟩]
theorem checked42898 : checkPrefixCuts (2^48) 5626658817 10 Manual.Count131072.C042898.packed 64 cuts42898 = true := by
 decide +kernel
def pointBounds42898 : List (Nat × Nat × Nat) := [(5626695680,109743996855939,109744382878073)]
theorem point_links_checked42898 : (cuts42898.take 1).map (fun c => (5626658817-1+2*2^10*c.k,109743913113982+c.lower,109744299136068+c.upper)) = pointBounds42898 := by
 decide +kernel
def cuts42899 : List PrefixCut := [⟨40,180585557,180585668⟩,
⟨64,291086621,291086796⟩]
theorem checked42899 : checkPrefixCuts (2^48) 5626789889 10 Manual.Count131072.C042899.packed 64 cuts42899 = true := by
 decide +kernel
def pointBounds42899 : List (Nat × Nat × Nat) := [(5626871808,109744387594352,109744773616713)]
theorem point_links_checked42899 : (cuts42899.take 1).map (fun c => (5626789889-1+2*2^10*c.k,109744207008795+c.lower,109744593031045+c.upper)) = pointBounds42899 := by
 decide +kernel
def cuts42900 : List PrefixCut := [⟨62,284577077,284577247⟩,
⟨64,293781079,293781255⟩]
theorem checked42900 : checkPrefixCuts (2^48) 5626920961 10 Manual.Count131072.C042900.packed 64 cuts42900 = true := by
 decide +kernel
def pointBounds42900 : List (Nat × Nat × Nat) := [(5627047936,109744782672493,109745168695088)]
theorem point_links_checked42900 : (cuts42900.take 1).map (fun c => (5626920961-1+2*2^10*c.k,109744498095416+c.lower,109744884117841+c.upper)) = pointBounds42900 := by
 decide +kernel
def cuts42901 : List PrefixCut := [⟨64,290622889,290623061⟩]
theorem checked42901 : checkPrefixCuts (2^48) 5627052033 10 Manual.Count131072.C042901.packed 64 cuts42901 = true := by
 decide +kernel
def cuts42902 : List PrefixCut := [⟨20,90486882,90486939⟩,
⟨64,293167131,293167303⟩]
theorem checked42902 : checkPrefixCuts (2^48) 5627183105 10 Manual.Count131072.C042902.packed 64 cuts42902 = true := by
 decide +kernel
def pointBounds42902 : List (Nat × Nat × Nat) := [(5627224064,109745172986266,109745559009096)]
theorem point_links_checked42902 : (cuts42902.take 1).map (fun c => (5627183105-1+2*2^10*c.k,109745082499384+c.lower,109745468522157+c.upper)) = pointBounds42902 := by
 decide +kernel
def cuts42903 : List PrefixCut := [⟨42,189021884,189021997⟩,
⟨64,288008373,288008546⟩]
theorem checked42903 : checkPrefixCuts (2^48) 5627314177 10 Manual.Count131072.C042903.packed 64 cuts42903 = true := by
 decide +kernel
def pointBounds42903 : List (Nat × Nat × Nat) := [(5627400192,109745564688399,109745950711457)]
theorem point_links_checked42903 : (cuts42903.take 1).map (fun c => (5627314177-1+2*2^10*c.k,109745375666515+c.lower,109745761689460+c.upper)) = pointBounds42903 := by
 decide +kernel
def cuts42904 : List PrefixCut := [⟨64,293253542,293253711⟩]
theorem checked42904 : checkPrefixCuts (2^48) 5627445249 10 Manual.Count131072.C042904.packed 64 cuts42904 = true := by
 decide +kernel
def pointBounds42904 : List (Nat × Nat × Nat) := [(5627576320,109745956928430,109746342951717)]
theorem point_links_checked42904 : (cuts42904.take 1).map (fun c => (5627445249-1+2*2^10*c.k,109745663674888+c.lower,109746049698006+c.upper)) = pointBounds42904 := by
 decide +kernel
def cuts42905 : List PrefixCut := [⟨64,290395742,290395909⟩]
theorem checked42905 : checkPrefixCuts (2^48) 5627576321 10 Manual.Count131072.C042905.packed 64 cuts42905 = true := by
 decide +kernel
def cuts42906 : List PrefixCut := [⟨22,100681628,100681683⟩,
⟨64,295890674,295890845⟩]
theorem checked42906 : checkPrefixCuts (2^48) 5627707393 10 Manual.Count131072.C042906.packed 64 cuts42906 = true := by
 decide +kernel
def pointBounds42906 : List (Nat × Nat × Nat) := [(5627752448,109746348005800,109746734029309)]
theorem point_links_checked42906 : (cuts42906.take 1).map (fun c => (5627707393-1+2*2^10*c.k,109746247324172+c.lower,109746633347626+c.upper)) = pointBounds42906 := by
 decide +kernel
def cuts42907 : List PrefixCut := [⟨44,200857598,200857716⟩,
⟨64,289982122,289982291⟩]
theorem checked42907 : checkPrefixCuts (2^48) 5627838465 10 Manual.Count131072.C042907.packed 64 cuts42907 = true := by
 decide +kernel
def pointBounds42907 : List (Nat × Nat × Nat) := [(5627928576,109746744072444,109747130096187)]
theorem point_links_checked42907 : (cuts42907.take 1).map (fun c => (5627838465-1+2*2^10*c.k,109746543214846+c.lower,109746929238471+c.upper)) = pointBounds42907 := by
 decide +kernel
def cuts42908 : List PrefixCut := [⟨64,292626066,292626237⟩]
theorem checked42908 : checkPrefixCuts (2^48) 5627969537 10 Manual.Count131072.C042908.packed 64 cuts42908 = true := by
 decide +kernel
def cuts42909 : List PrefixCut := [⟨2,9752417,9752423⟩,
⟨64,292619232,292619405⟩]
theorem checked42909 : checkPrefixCuts (2^48) 5628100609 10 Manual.Count131072.C042909.packed 64 cuts42909 = true := by
 decide +kernel
def pointBounds42909 : List (Nat × Nat × Nat) := [(5628104704,109747135575451,109747521599422)]
theorem point_links_checked42909 : (cuts42909.take 1).map (fun c => (5628100609-1+2*2^10*c.k,109747125823034+c.lower,109747511846999+c.upper)) = pointBounds42909 := by
 decide +kernel
def cuts42910 : List PrefixCut := [⟨24,110124293,110124356⟩,
⟨64,288211498,288211668⟩]
theorem checked42910 : checkPrefixCuts (2^48) 5628231681 10 Manual.Count131072.C042910.packed 64 cuts42910 = true := by
 decide +kernel
def pointBounds42910 : List (Nat × Nat × Nat) := [(5628280832,109747528566559,109747914590760)]
theorem point_links_checked42910 : (cuts42910.take 1).map (fun c => (5628231681-1+2*2^10*c.k,109747418442266+c.lower,109747804466404+c.upper)) = pointBounds42910 := by
 decide +kernel
def cuts42911 : List PrefixCut := [⟨46,212040987,212041107⟩,
⟨64,293855848,293856018⟩]
theorem checked42911 : checkPrefixCuts (2^48) 5628362753 10 Manual.Count131072.C042911.packed 64 cuts42911 = true := by
 decide +kernel
def pointBounds42911 : List (Nat × Nat × Nat) := [(5628456960,109747918694751,109748304719179)]
theorem point_links_checked42911 : (cuts42911.take 1).map (fun c => (5628362753-1+2*2^10*c.k,109747706653764+c.lower,109748092678072+c.upper)) = pointBounds42911 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S5.B000090
