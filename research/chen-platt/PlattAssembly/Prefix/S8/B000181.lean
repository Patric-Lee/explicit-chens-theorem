import PlattAssemblyKernel
import PlattCertificates.Count131072.C075792
import PlattCertificates.Count131072.C075793
import PlattCertificates.Count131072.C075794
import PlattCertificates.Count131072.C075795
import PlattCertificates.Count131072.C075796
import PlattCertificates.Count131072.C075797
import PlattCertificates.Count131072.C075798
import PlattCertificates.Count131072.C075799
import PlattCertificates.Count131072.C075800
import PlattCertificates.Count131072.C075801
import PlattCertificates.Count131072.C075802
import PlattCertificates.Count131072.C075803
import PlattCertificates.Count131072.C075804
import PlattCertificates.Count131072.C075805
import PlattCertificates.Count131072.C075806
import PlattCertificates.Count131072.C075807
import PlattCertificates.Count131072.C075808
import PlattCertificates.Count131072.C075809
import PlattCertificates.Count131072.C075810
import PlattCertificates.Count131072.C075811
import PlattCertificates.Count131072.C075812
import PlattCertificates.Count131072.C075813
import PlattCertificates.Count131072.C075814
import PlattCertificates.Count131072.C075815
import PlattCertificates.Count131072.C075816
import PlattCertificates.Count131072.C075817
import PlattCertificates.Count131072.C075818
import PlattCertificates.Count131072.C075819
import PlattCertificates.Count131072.C075820
import PlattCertificates.Count131072.C075821
import PlattCertificates.Count131072.C075822
import PlattCertificates.Count131072.C075823
namespace ChenEffective.PlattWindow.Assembly.Prefix.S8.B000181
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts75792 : List PrefixCut := [⟨64,161183358,161183455⟩]
theorem checked75792 : checkPrefixCuts (2^48) 9938141185 10 Manual.Count131072.C075792.packed 64 cuts75792 = true := by
 decide +kernel
def cuts75793 : List PrefixCut := [⟨43,109012107,109012175⟩,
⟨64,161719358,161719456⟩]
theorem checked75793 : checkPrefixCuts (2^48) 9938272257 10 Manual.Count131072.C075793.packed 64 cuts75793 = true := by
 decide +kernel
def pointBounds75793 : List (Nat × Nat × Nat) := [(9938360320,116787414741446,116787804826194)]
theorem point_links_checked75793 : (cuts75793.take 1).map (fun c => (9938272257-1+2*2^10*c.k,116787305729339+c.lower,116787695814019+c.upper)) = pointBounds75793 := by
 decide +kernel
def cuts75794 : List PrefixCut := [⟨64,163020028,163020133⟩]
theorem checked75794 : checkPrefixCuts (2^48) 9938403329 10 Manual.Count131072.C075794.packed 64 cuts75794 = true := by
 decide +kernel
def cuts75795 : List PrefixCut := [⟨64,161856705,161856803⟩]
theorem checked75795 : checkPrefixCuts (2^48) 9938534401 10 Manual.Count131072.C075795.packed 64 cuts75795 = true := by
 decide +kernel
def cuts75796 : List PrefixCut := [⟨3,8156501,8156507⟩,
⟨64,162845802,162845903⟩]
theorem checked75796 : checkPrefixCuts (2^48) 9938665473 10 Manual.Count131072.C075796.packed 64 cuts75796 = true := by
 decide +kernel
def pointBounds75796 : List (Nat × Nat × Nat) := [(9938671616,116787800481931,116788190566918)]
theorem point_links_checked75796 : (cuts75796.take 1).map (fun c => (9938665473-1+2*2^10*c.k,116787792325430+c.lower,116788182410411+c.upper)) = pointBounds75796 := by
 decide +kernel
def cuts75797 : List PrefixCut := [⟨64,162673729,162673820⟩]
theorem checked75797 : checkPrefixCuts (2^48) 9938796545 10 Manual.Count131072.C075797.packed 64 cuts75797 = true := by
 decide +kernel
def cuts75798 : List PrefixCut := [⟨27,66807753,66807792⟩,
⟨64,158820029,158820122⟩]
theorem checked75798 : checkPrefixCuts (2^48) 9938927617 10 Manual.Count131072.C075798.packed 64 cuts75798 = true := by
 decide +kernel
def pointBounds75798 : List (Nat × Nat × Nat) := [(9938982912,116788184652714,116788574737926)]
theorem point_links_checked75798 : (cuts75798.take 1).map (fun c => (9938927617-1+2*2^10*c.k,116788117844961+c.lower,116788507930134+c.upper)) = pointBounds75798 := by
 decide +kernel
def cuts75799 : List PrefixCut := [⟨64,159979046,159979145⟩]
theorem checked75799 : checkPrefixCuts (2^48) 9939058689 10 Manual.Count131072.C075799.packed 64 cuts75799 = true := by
 decide +kernel
def cuts75800 : List PrefixCut := [⟨51,128004387,128004458⟩,
⟨64,161138044,161138136⟩]
theorem checked75800 : checkPrefixCuts (2^48) 9939189761 10 Manual.Count131072.C075800.packed 64 cuts75800 = true := by
 decide +kernel
def pointBounds75800 : List (Nat × Nat × Nat) := [(9939294208,116788564648423,116788954733859)]
theorem point_links_checked75800 : (cuts75800.take 1).map (fun c => (9939189761-1+2*2^10*c.k,116788436644036+c.lower,116788826729401+c.upper)) = pointBounds75800 := by
 decide +kernel
def cuts75801 : List PrefixCut := [⟨64,160966008,160966110⟩]
theorem checked75801 : checkPrefixCuts (2^48) 9939320833 10 Manual.Count131072.C075801.packed 64 cuts75801 = true := by
 decide +kernel
def cuts75802 : List PrefixCut := [⟨64,162266541,162266636⟩]
theorem checked75802 : checkPrefixCuts (2^48) 9939451905 10 Manual.Count131072.C075802.packed 64 cuts75802 = true := by
 decide +kernel
def cuts75803 : List PrefixCut := [⟨11,28346867,28346887⟩,
⟨64,164275008,164275110⟩]
theorem checked75803 : checkPrefixCuts (2^48) 9939582977 10 Manual.Count131072.C075803.packed 64 cuts75803 = true := by
 decide +kernel
def pointBounds75803 : List (Nat × Nat × Nat) := [(9939605504,116788949361496,116789339447170)]
theorem point_links_checked75803 : (cuts75803.take 1).map (fun c => (9939582977-1+2*2^10*c.k,116788921014629+c.lower,116789311100283+c.upper)) = pointBounds75803 := by
 decide +kernel
def cuts75804 : List PrefixCut := [⟨64,160818049,160818145⟩]
theorem checked75804 : checkPrefixCuts (2^48) 9939714049 10 Manual.Count131072.C075804.packed 64 cuts75804 = true := by
 decide +kernel
def cuts75805 : List PrefixCut := [⟨35,87275257,87275306⟩,
⟨64,159994716,159994808⟩]
theorem checked75805 : checkPrefixCuts (2^48) 9939845121 10 Manual.Count131072.C075805.packed 64 cuts75805 = true := by
 decide +kernel
def pointBounds75805 : List (Nat × Nat × Nat) := [(9939916800,116789333382943,116789723468844)]
theorem point_links_checked75805 : (cuts75805.take 1).map (fun c => (9939845121-1+2*2^10*c.k,116789246107686+c.lower,116789636193538+c.upper)) = pointBounds75805 := by
 decide +kernel
def cuts75806 : List PrefixCut := [⟨64,161776588,161776686⟩]
theorem checked75806 : checkPrefixCuts (2^48) 9939976193 10 Manual.Count131072.C075806.packed 64 cuts75806 = true := by
 decide +kernel
def cuts75807 : List PrefixCut := [⟨59,146398456,146398544⟩,
⟨64,158659599,158659695⟩]
theorem checked75807 : checkPrefixCuts (2^48) 9940107265 10 Manual.Count131072.C075807.packed 64 cuts75807 = true := by
 decide +kernel
def pointBounds75807 : List (Nat × Nat × Nat) := [(9940228096,116789714277446,116790104363576)]
theorem point_links_checked75807 : (cuts75807.take 1).map (fun c => (9940107265-1+2*2^10*c.k,116789567878990+c.lower,116789957965032+c.upper)) = pointBounds75807 := by
 decide +kernel
def cuts75808 : List PrefixCut := [⟨64,163188156,163188251⟩]
theorem checked75808 : checkPrefixCuts (2^48) 9940238337 10 Manual.Count131072.C075808.packed 64 cuts75808 = true := by
 decide +kernel
def cuts75809 : List PrefixCut := [⟨64,162364842,162364941⟩]
theorem checked75809 : checkPrefixCuts (2^48) 9940369409 10 Manual.Count131072.C075809.packed 64 cuts75809 = true := by
 decide +kernel
def cuts75810 : List PrefixCut := [⟨19,48448528,48448556⟩,
⟨64,164712894,164712996⟩]
theorem checked75810 : checkPrefixCuts (2^48) 9940500481 10 Manual.Count131072.C075810.packed 64 cuts75810 = true := by
 decide +kernel
def pointBounds75810 : List (Nat × Nat × Nat) := [(9940539392,116790100540115,116790490626475)]
theorem point_links_checked75810 : (cuts75810.take 1).map (fun c => (9940500481-1+2*2^10*c.k,116790052091587+c.lower,116790442177919+c.upper)) = pointBounds75810 := by
 decide +kernel
def cuts75811 : List PrefixCut := [⟨64,158311432,158311534⟩]
theorem checked75811 : checkPrefixCuts (2^48) 9940631553 10 Manual.Count131072.C075811.packed 64 cuts75811 = true := by
 decide +kernel
def cuts75812 : List PrefixCut := [⟨43,108305242,108305305⟩,
⟨64,160829396,160829491⟩]
theorem checked75812 : checkPrefixCuts (2^48) 9940762625 10 Manual.Count131072.C075812.packed 64 cuts75812 = true := by
 decide +kernel
def pointBounds75812 : List (Nat × Nat × Nat) := [(9940850688,116790483421155,116790873507754)]
theorem point_links_checked75812 : (cuts75812.take 1).map (fun c => (9940762625-1+2*2^10*c.k,116790375115913+c.lower,116790765202449+c.upper)) = pointBounds75812 := by
 decide +kernel
def cuts75813 : List PrefixCut := [⟨64,163375596,163375690⟩]
theorem checked75813 : checkPrefixCuts (2^48) 9940893697 10 Manual.Count131072.C075813.packed 64 cuts75813 = true := by
 decide +kernel
def cuts75814 : List PrefixCut := [⟨64,160711895,160711993⟩]
theorem checked75814 : checkPrefixCuts (2^48) 9941024769 10 Manual.Count131072.C075814.packed 64 cuts75814 = true := by
 decide +kernel
def cuts75815 : List PrefixCut := [⟨3,6965266,6965271⟩,
⟨64,160483257,160483345⟩]
theorem checked75815 : checkPrefixCuts (2^48) 9941155841 10 Manual.Count131072.C075815.packed 64 cuts75815 = true := by
 decide +kernel
def pointBounds75815 : List (Nat × Nat × Nat) := [(9941161984,116790866998066,116791257084894)]
theorem point_links_checked75815 : (cuts75815.take 1).map (fun c => (9941155841-1+2*2^10*c.k,116790860032800+c.lower,116791250119623+c.upper)) = pointBounds75815 := by
 decide +kernel
def cuts75816 : List PrefixCut := [⟨64,162349841,162349936⟩]
theorem checked75816 : checkPrefixCuts (2^48) 9941286913 10 Manual.Count131072.C075816.packed 64 cuts75816 = true := by
 decide +kernel
def cuts75817 : List PrefixCut := [⟨27,69678968,69679011⟩,
⟨64,161838071,161838169⟩]
theorem checked75817 : checkPrefixCuts (2^48) 9941417985 10 Manual.Count131072.C075817.packed 64 cuts75817 = true := by
 decide +kernel
def pointBounds75817 : List (Nat × Nat × Nat) := [(9941473280,116791252544866,116791642631915)]
theorem point_links_checked75817 : (cuts75817.take 1).map (fun c => (9941417985-1+2*2^10*c.k,116791182865898+c.lower,116791572952904+c.upper)) = pointBounds75817 := by
 decide +kernel
def cuts75818 : List PrefixCut := [⟨64,158268520,158268620⟩]
theorem checked75818 : checkPrefixCuts (2^48) 9941549057 10 Manual.Count131072.C075818.packed 64 cuts75818 = true := by
 decide +kernel
def cuts75819 : List PrefixCut := [⟨51,128198816,128198894⟩,
⟨64,161324174,161324274⟩]
theorem checked75819 : checkPrefixCuts (2^48) 9941680129 10 Manual.Count131072.C075819.packed 64 cuts75819 = true := by
 decide +kernel
def pointBounds75819 : List (Nat × Nat × Nat) := [(9941784576,116791631171305,116792021258587)]
theorem point_links_checked75819 : (cuts75819.take 1).map (fun c => (9941680129-1+2*2^10*c.k,116791502972489+c.lower,116791893059693+c.upper)) = pointBounds75819 := by
 decide +kernel
def cuts75820 : List PrefixCut := [⟨64,159708259,159708354⟩]
theorem checked75820 : checkPrefixCuts (2^48) 9941811201 10 Manual.Count131072.C075820.packed 64 cuts75820 = true := by
 decide +kernel
def cuts75821 : List PrefixCut := [⟨64,162593961,162594060⟩]
theorem checked75821 : checkPrefixCuts (2^48) 9941942273 10 Manual.Count131072.C075821.packed 64 cuts75821 = true := by
 decide +kernel
def cuts75822 : List PrefixCut := [⟨11,27716915,27716932⟩,
⟨64,160638324,160638423⟩]
theorem checked75822 : checkPrefixCuts (2^48) 9942073345 10 Manual.Count131072.C075822.packed 64 cuts75822 = true := by
 decide +kernel
def pointBounds75822 : List (Nat × Nat × Nat) := [(9942095872,116792014315798,116792404403313)]
theorem point_links_checked75822 : (cuts75822.take 1).map (fun c => (9942073345-1+2*2^10*c.k,116791986598883+c.lower,116792376686381+c.upper)) = pointBounds75822 := by
 decide +kernel
def cuts75823 : List PrefixCut := [⟨64,160919321,160919416⟩]
theorem checked75823 : checkPrefixCuts (2^48) 9942204417 10 Manual.Count131072.C075823.packed 64 cuts75823 = true := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S8.B000181
