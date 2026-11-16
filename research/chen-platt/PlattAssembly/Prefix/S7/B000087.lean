import PlattAssemblyKernel
import PlattCertificates.Count131072.C062784
import PlattCertificates.Count131072.C062785
import PlattCertificates.Count131072.C062786
import PlattCertificates.Count131072.C062787
import PlattCertificates.Count131072.C062788
import PlattCertificates.Count131072.C062789
import PlattCertificates.Count131072.C062790
import PlattCertificates.Count131072.C062791
import PlattCertificates.Count131072.C062792
import PlattCertificates.Count131072.C062793
import PlattCertificates.Count131072.C062794
import PlattCertificates.Count131072.C062795
import PlattCertificates.Count131072.C062796
import PlattCertificates.Count131072.C062797
import PlattCertificates.Count131072.C062798
import PlattCertificates.Count131072.C062799
import PlattCertificates.Count131072.C062800
import PlattCertificates.Count131072.C062801
import PlattCertificates.Count131072.C062802
import PlattCertificates.Count131072.C062803
import PlattCertificates.Count131072.C062804
import PlattCertificates.Count131072.C062805
import PlattCertificates.Count131072.C062806
import PlattCertificates.Count131072.C062807
import PlattCertificates.Count131072.C062808
import PlattCertificates.Count131072.C062809
import PlattCertificates.Count131072.C062810
import PlattCertificates.Count131072.C062811
import PlattCertificates.Count131072.C062812
import PlattCertificates.Count131072.C062813
import PlattCertificates.Count131072.C062814
import PlattCertificates.Count131072.C062815
namespace ChenEffective.PlattWindow.Assembly.Prefix.S7.B000087
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts62784 : List PrefixCut := [⟨64,194220311,194220420⟩]
theorem checked62784 : checkPrefixCuts (2^48) 8233156609 10 Manual.Count131072.C062784.packed 64 cuts62784 = true := by
 decide +kernel
def cuts62785 : List PrefixCut := [⟨40,121740800,121740874⟩,
⟨64,195892362,195892481⟩]
theorem checked62785 : checkPrefixCuts (2^48) 8233287681 10 Manual.Count131072.C062785.packed 64 cuts62785 = true := by
 decide +kernel
def pointBounds62785 : List (Nat × Nat × Nat) := [(8233369600,114476605370896,114476994098896)]
theorem point_links_checked62785 : (cuts62785.take 1).map (fun c => (8233287681-1+2*2^10*c.k,114476483630096+c.lower,114476872358022+c.upper)) = pointBounds62785 := by
 decide +kernel
def cuts62786 : List PrefixCut := [⟨64,194932011,194932130⟩]
theorem checked62786 : checkPrefixCuts (2^48) 8233418753 10 Manual.Count131072.C062786.packed 64 cuts62786 = true := by
 decide +kernel
def cuts62787 : List PrefixCut := [⟨38,118591845,118591918⟩,
⟨64,198176626,198176746⟩]
theorem checked62787 : checkPrefixCuts (2^48) 8233549825 10 Manual.Count131072.C062787.packed 64 cuts62787 = true := by
 decide +kernel
def pointBounds62787 : List (Nat × Nat × Nat) := [(8233627648,114476993046314,114477381774551)]
theorem point_links_checked62787 : (cuts62787.take 1).map (fun c => (8233549825-1+2*2^10*c.k,114476874454469+c.lower,114477263182633+c.upper)) = pointBounds62787 := by
 decide +kernel
def cuts62788 : List PrefixCut := [⟨64,195541181,195541297⟩]
theorem checked62788 : checkPrefixCuts (2^48) 8233680897 10 Manual.Count131072.C062788.packed 64 cuts62788 = true := by
 decide +kernel
def cuts62789 : List PrefixCut := [⟨36,108947895,108947960⟩,
⟨64,195948268,195948381⟩]
theorem checked62789 : checkPrefixCuts (2^48) 8233811969 10 Manual.Count131072.C062789.packed 64 cuts62789 = true := by
 decide +kernel
def pointBounds62789 : List (Nat × Nat × Nat) := [(8233885696,114477377120171,114477765848636)]
theorem point_links_checked62789 : (cuts62789.take 1).map (fun c => (8233811969-1+2*2^10*c.k,114477268172276+c.lower,114477656900676+c.upper)) = pointBounds62789 := by
 decide +kernel
def cuts62790 : List PrefixCut := [⟨64,198406424,198406533⟩]
theorem checked62790 : checkPrefixCuts (2^48) 8233943041 10 Manual.Count131072.C062790.packed 64 cuts62790 = true := by
 decide +kernel
def cuts62791 : List PrefixCut := [⟨34,104568903,104568967⟩,
⟨64,197548681,197548798⟩]
theorem checked62791 : checkPrefixCuts (2^48) 8234074113 10 Manual.Count131072.C062791.packed 64 cuts62791 = true := by
 decide +kernel
def pointBounds62791 : List (Nat × Nat × Nat) := [(8234143744,114477767095871,114478155824557)]
theorem point_links_checked62791 : (cuts62791.take 1).map (fun c => (8234074113-1+2*2^10*c.k,114477662526968+c.lower,114478051255590+c.upper)) = pointBounds62791 := by
 decide +kernel
def cuts62792 : List PrefixCut := [⟨64,195494545,195494658⟩]
theorem checked62792 : checkPrefixCuts (2^48) 8234205185 10 Manual.Count131072.C062792.packed 64 cuts62792 = true := by
 decide +kernel
def cuts62793 : List PrefixCut := [⟨32,96976982,96977037⟩,
⟨64,196414348,196414459⟩]
theorem checked62793 : checkPrefixCuts (2^48) 8234336257 10 Manual.Count131072.C062793.packed 64 cuts62793 = true := by
 decide +kernel
def pointBounds62793 : List (Nat × Nat × Nat) := [(8234401792,114478152547176,114478541276083)]
theorem point_links_checked62793 : (cuts62793.take 1).map (fun c => (8234336257-1+2*2^10*c.k,114478055570194+c.lower,114478444299046+c.upper)) = pointBounds62793 := by
 decide +kernel
def cuts62794 : List PrefixCut := [⟨64,198769813,198769928⟩]
theorem checked62794 : checkPrefixCuts (2^48) 8234467329 10 Manual.Count131072.C062794.packed 64 cuts62794 = true := by
 decide +kernel
def cuts62795 : List PrefixCut := [⟨30,92427736,92427789⟩,
⟨64,196408108,196408222⟩]
theorem checked62795 : checkPrefixCuts (2^48) 8234598401 10 Manual.Count131072.C062795.packed 64 cuts62795 = true := by
 decide +kernel
def pointBounds62795 : List (Nat × Nat × Nat) := [(8234659840,114478543182091,114478931911222)]
theorem point_links_checked62795 : (cuts62795.take 1).map (fun c => (8234598401-1+2*2^10*c.k,114478450754355+c.lower,114478839483433+c.upper)) = pointBounds62795 := by
 decide +kernel
def cuts62796 : List PrefixCut := [⟨64,197806401,197806516⟩]
theorem checked62796 : checkPrefixCuts (2^48) 8234729473 10 Manual.Count131072.C062796.packed 64 cuts62796 = true := by
 decide +kernel
def cuts62797 : List PrefixCut := [⟨28,84289789,84289839⟩,
⟨64,193735759,193735874⟩]
theorem checked62797 : checkPrefixCuts (2^48) 8234860545 10 Manual.Count131072.C062797.packed 64 cuts62797 = true := by
 decide +kernel
def pointBounds62797 : List (Nat × Nat × Nat) := [(8234917888,114478929258653,114479317988010)]
theorem point_links_checked62797 : (cuts62797.take 1).map (fun c => (8234860545-1+2*2^10*c.k,114478844968864+c.lower,114479233698171+c.upper)) = pointBounds62797 := by
 decide +kernel
def cuts62798 : List PrefixCut := [⟨64,196808887,196808999⟩]
theorem checked62798 : checkPrefixCuts (2^48) 8234991617 10 Manual.Count131072.C062798.packed 64 cuts62798 = true := by
 decide +kernel
def cuts62799 : List PrefixCut := [⟨26,79775408,79775456⟩,
⟨64,196429775,196429890⟩]
theorem checked62799 : checkPrefixCuts (2^48) 8235122689 10 Manual.Count131072.C062799.packed 64 cuts62799 = true := by
 decide +kernel
def pointBounds62799 : List (Nat × Nat × Nat) := [(8235175936,114479315288918,114479704018500)]
theorem point_links_checked62799 : (cuts62799.take 1).map (fun c => (8235122689-1+2*2^10*c.k,114479235513510+c.lower,114479624243044+c.upper)) = pointBounds62799 := by
 decide +kernel
def cuts62800 : List PrefixCut := [⟨64,198409028,198409138⟩]
theorem checked62800 : checkPrefixCuts (2^48) 8235253761 10 Manual.Count131072.C062800.packed 64 cuts62800 = true := by
 decide +kernel
def cuts62801 : List PrefixCut := [⟨24,74475202,74475248⟩,
⟨64,194167759,194167877⟩]
theorem checked62801 : checkPrefixCuts (2^48) 8235384833 10 Manual.Count131072.C062801.packed 64 cuts62801 = true := by
 decide +kernel
def pointBounds62801 : List (Nat × Nat × Nat) := [(8235433984,114479704827515,114480093557320)]
theorem point_links_checked62801 : (cuts62801.take 1).map (fun c => (8235384833-1+2*2^10*c.k,114479630352313+c.lower,114480019082072+c.upper)) = pointBounds62801 := by
 decide +kernel
def cuts62802 : List PrefixCut := [⟨64,197240673,197240786⟩]
theorem checked62802 : checkPrefixCuts (2^48) 8235515905 10 Manual.Count131072.C062802.packed 64 cuts62802 = true := by
 decide +kernel
def cuts62803 : List PrefixCut := [⟨22,65518336,65518376⟩,
⟨64,195562825,195562936⟩]
theorem checked62803 : checkPrefixCuts (2^48) 8235646977 10 Manual.Count131072.C062803.packed 64 cuts62803 = true := by
 decide +kernel
def pointBounds62803 : List (Nat × Nat × Nat) := [(8235692032,114480087279081,114480476009111)]
theorem point_links_checked62803 : (cuts62803.take 1).map (fun c => (8235646977-1+2*2^10*c.k,114480021760745+c.lower,114480410490735+c.upper)) = pointBounds62803 := by
 decide +kernel
def cuts62804 : List PrefixCut := [⟨64,195628076,195628186⟩]
theorem checked62804 : checkPrefixCuts (2^48) 8235778049 10 Manual.Count131072.C062804.packed 64 cuts62804 = true := by
 decide +kernel
def cuts62805 : List PrefixCut := [⟨20,60970800,60970837⟩,
⟨64,195898374,195898490⟩]
theorem checked62805 : checkPrefixCuts (2^48) 8235909121 10 Manual.Count131072.C062805.packed 64 cuts62805 = true := by
 decide +kernel
def pointBounds62805 : List (Nat × Nat × Nat) := [(8235950080,114480473922446,114480862652694)]
theorem point_links_checked62805 : (cuts62805.take 1).map (fun c => (8235909121-1+2*2^10*c.k,114480412951646+c.lower,114480801681857+c.upper)) = pointBounds62805 := by
 decide +kernel
def cuts62806 : List PrefixCut := [⟨64,197672385,197672501⟩]
theorem checked62806 : checkPrefixCuts (2^48) 8236040193 10 Manual.Count131072.C062806.packed 64 cuts62806 = true := by
 decide +kernel
def cuts62807 : List PrefixCut := [⟨18,56321023,56321055⟩,
⟨64,198181883,198181997⟩]
theorem checked62807 : checkPrefixCuts (2^48) 8236171265 10 Manual.Count131072.C062807.packed 64 cuts62807 = true := by
 decide +kernel
def pointBounds62807 : List (Nat × Nat × Nat) := [(8236208128,114480862843428,114481251573903)]
theorem point_links_checked62807 : (cuts62807.take 1).map (fun c => (8236171265-1+2*2^10*c.k,114480806522405+c.lower,114481195252848+c.upper)) = pointBounds62807 := by
 decide +kernel
def cuts62808 : List PrefixCut := [⟨64,198349603,198349715⟩]
theorem checked62808 : checkPrefixCuts (2^48) 8236302337 10 Manual.Count131072.C062808.packed 64 cuts62808 = true := by
 decide +kernel
def cuts62809 : List PrefixCut := [⟨16,51193100,51193129⟩,
⟨64,197628803,197628914⟩]
theorem checked62809 : checkPrefixCuts (2^48) 8236433409 10 Manual.Count131072.C062809.packed 64 cuts62809 = true := by
 decide +kernel
def pointBounds62809 : List (Nat × Nat × Nat) := [(8236466176,114481254246991,114481642977689)]
theorem point_links_checked62809 : (cuts62809.take 1).map (fun c => (8236433409-1+2*2^10*c.k,114481203053891+c.lower,114481591784560+c.upper)) = pointBounds62809 := by
 decide +kernel
def cuts62810 : List PrefixCut := [⟨64,195985310,195985422⟩]
theorem checked62810 : checkPrefixCuts (2^48) 8236564481 10 Manual.Count131072.C062810.packed 64 cuts62810 = true := by
 decide +kernel
def cuts62811 : List PrefixCut := [⟨14,42750699,42750723⟩,
⟨64,193350877,193350986⟩]
theorem checked62811 : checkPrefixCuts (2^48) 8236695553 10 Manual.Count131072.C062811.packed 64 cuts62811 = true := by
 decide +kernel
def pointBounds62811 : List (Nat × Nat × Nat) := [(8236724224,114481639418703,114482028149619)]
theorem point_links_checked62811 : (cuts62811.take 1).map (fun c => (8236695553-1+2*2^10*c.k,114481596668004+c.lower,114481985398896+c.upper)) = pointBounds62811 := by
 decide +kernel
def cuts62812 : List PrefixCut := [⟨64,193792033,193792145⟩]
theorem checked62812 : checkPrefixCuts (2^48) 8236826625 10 Manual.Count131072.C062812.packed 64 cuts62812 = true := by
 decide +kernel
def cuts62813 : List PrefixCut := [⟨12,36495847,36495866⟩,
⟨64,193925635,193925747⟩]
theorem checked62813 : checkPrefixCuts (2^48) 8236957697 10 Manual.Count131072.C062813.packed 64 cuts62813 = true := by
 decide +kernel
def pointBounds62813 : List (Nat × Nat × Nat) := [(8236982272,114482020306761,114482409037893)]
theorem point_links_checked62813 : (cuts62813.take 1).map (fun c => (8236957697-1+2*2^10*c.k,114481983810914+c.lower,114482372542027+c.upper)) = pointBounds62813 := by
 decide +kernel
def cuts62814 : List PrefixCut := [⟨64,198467340,198467456⟩]
theorem checked62814 : checkPrefixCuts (2^48) 8237088769 10 Manual.Count131072.C062814.packed 64 cuts62814 = true := by
 decide +kernel
def cuts62815 : List PrefixCut := [⟨10,30685613,30685631⟩,
⟨64,198703378,198703495⟩]
theorem checked62815 : checkPrefixCuts (2^48) 8237219841 10 Manual.Count131072.C062815.packed 64 cuts62815 = true := by
 decide +kernel
def pointBounds62815 : List (Nat × Nat × Nat) := [(8237240320,114482406889502,114482795620861)]
theorem point_links_checked62815 : (cuts62815.take 1).map (fun c => (8237219841-1+2*2^10*c.k,114482376203889+c.lower,114482764935230+c.upper)) = pointBounds62815 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S7.B000087
