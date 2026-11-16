import PlattAssemblyKernel
import PlattCertificates.Count131072.C073840
import PlattCertificates.Count131072.C073841
import PlattCertificates.Count131072.C073842
import PlattCertificates.Count131072.C073843
import PlattCertificates.Count131072.C073844
import PlattCertificates.Count131072.C073845
import PlattCertificates.Count131072.C073846
import PlattCertificates.Count131072.C073847
import PlattCertificates.Count131072.C073848
import PlattCertificates.Count131072.C073849
import PlattCertificates.Count131072.C073850
import PlattCertificates.Count131072.C073851
import PlattCertificates.Count131072.C073852
import PlattCertificates.Count131072.C073853
import PlattCertificates.Count131072.C073854
import PlattCertificates.Count131072.C073855
import PlattCertificates.Count131072.C073856
import PlattCertificates.Count131072.C073857
import PlattCertificates.Count131072.C073858
import PlattCertificates.Count131072.C073859
import PlattCertificates.Count131072.C073860
import PlattCertificates.Count131072.C073861
import PlattCertificates.Count131072.C073862
import PlattCertificates.Count131072.C073863
import PlattCertificates.Count131072.C073864
import PlattCertificates.Count131072.C073865
import PlattCertificates.Count131072.C073866
import PlattCertificates.Count131072.C073867
import PlattCertificates.Count131072.C073868
import PlattCertificates.Count131072.C073869
import PlattCertificates.Count131072.C073870
import PlattCertificates.Count131072.C073871
namespace ChenEffective.PlattWindow.Assembly.Prefix.S8.B000120
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts73840 : List PrefixCut := [⟨64,165006518,165006617⟩]
theorem checked73840 : checkPrefixCuts (2^48) 9682288641 10 Manual.Count131072.C073840.packed 64 cuts73840 = true := by
 decide +kernel
def cuts73841 : List PrefixCut := [⟨14,35727859,35727882⟩,
⟨64,164510078,164510176⟩]
theorem checked73841 : checkPrefixCuts (2^48) 9682419713 10 Manual.Count131072.C073841.packed 64 cuts73841 = true := by
 decide +kernel
def pointBounds73841 : List (Nat × Nat × Nat) := [(9682448384,116468237116926,116468627010382)]
theorem point_links_checked73841 : (cuts73841.take 1).map (fun c => (9682419713-1+2*2^10*c.k,116468201389067+c.lower,116468591282500+c.upper)) = pointBounds73841 := by
 decide +kernel
def cuts73842 : List PrefixCut := [⟨64,164943901,164944000⟩]
theorem checked73842 : checkPrefixCuts (2^48) 9682550785 10 Manual.Count131072.C073842.packed 64 cuts73842 = true := by
 decide +kernel
def cuts73843 : List PrefixCut := [⟨34,88459485,88459538⟩,
⟨64,164999820,164999918⟩]
theorem checked73843 : checkPrefixCuts (2^48) 9682681857 10 Manual.Count131072.C073843.packed 64 cuts73843 = true := by
 decide +kernel
def pointBounds73843 : List (Nat × Nat × Nat) := [(9682751488,116468619302531,116469009196214)]
theorem point_links_checked73843 : (cuts73843.take 1).map (fun c => (9682681857-1+2*2^10*c.k,116468530843046+c.lower,116468920736676+c.upper)) = pointBounds73843 := by
 decide +kernel
def cuts73844 : List PrefixCut := [⟨64,166567334,166567436⟩]
theorem checked73844 : checkPrefixCuts (2^48) 9682812929 10 Manual.Count131072.C073844.packed 64 cuts73844 = true := by
 decide +kernel
def cuts73845 : List PrefixCut := [⟨54,139502022,139502101⟩,
⟨64,164966275,164966366⟩]
theorem checked73845 : checkPrefixCuts (2^48) 9682944001 10 Manual.Count131072.C073845.packed 64 cuts73845 = true := by
 decide +kernel
def pointBounds73845 : List (Nat × Nat × Nat) := [(9683054592,116469001912222,116469391806131)]
theorem point_links_checked73845 : (cuts73845.take 1).map (fun c => (9682944001-1+2*2^10*c.k,116468862410200+c.lower,116469252304030+c.upper)) = pointBounds73845 := by
 decide +kernel
def cuts73846 : List PrefixCut := [⟨64,166243053,166243150⟩]
theorem checked73846 : checkPrefixCuts (2^48) 9683075073 10 Manual.Count131072.C073846.packed 64 cuts73846 = true := by
 decide +kernel
def cuts73847 : List PrefixCut := [⟨64,167345397,167345496⟩]
theorem checked73847 : checkPrefixCuts (2^48) 9683206145 10 Manual.Count131072.C073847.packed 64 cuts73847 = true := by
 decide +kernel
def cuts73848 : List PrefixCut := [⟨10,25376305,25376320⟩,
⟨64,164930500,164930597⟩]
theorem checked73848 : checkPrefixCuts (2^48) 9683337217 10 Manual.Count131072.C073848.packed 64 cuts73848 = true := by
 decide +kernel
def pointBounds73848 : List (Nat × Nat × Nat) := [(9683357696,116469386341230,116469776235362)]
theorem point_links_checked73848 : (cuts73848.take 1).map (fun c => (9683337217-1+2*2^10*c.k,116469360964925+c.lower,116469750859042+c.upper)) = pointBounds73848 := by
 decide +kernel
def cuts73849 : List PrefixCut := [⟨64,165567755,165567854⟩]
theorem checked73849 : checkPrefixCuts (2^48) 9683468289 10 Manual.Count131072.C073849.packed 64 cuts73849 = true := by
 decide +kernel
def cuts73850 : List PrefixCut := [⟨30,77725388,77725432⟩,
⟨64,164809787,164809877⟩]
theorem checked73850 : checkPrefixCuts (2^48) 9683599361 10 Manual.Count131072.C073850.packed 64 cuts73850 = true := by
 decide +kernel
def pointBounds73850 : List (Nat × Nat × Nat) := [(9683660800,116469769188568,116470159082925)]
theorem point_links_checked73850 : (cuts73850.take 1).map (fun c => (9683599361-1+2*2^10*c.k,116469691463180+c.lower,116470081357493+c.upper)) = pointBounds73850 := by
 decide +kernel
def cuts73851 : List PrefixCut := [⟨64,163121684,163121789⟩]
theorem checked73851 : checkPrefixCuts (2^48) 9683730433 10 Manual.Count131072.C073851.packed 64 cuts73851 = true := by
 decide +kernel
def cuts73852 : List PrefixCut := [⟨50,129170359,129170438⟩,
⟨64,164834390,164834490⟩]
theorem checked73852 : checkPrefixCuts (2^48) 9683861505 10 Manual.Count131072.C073852.packed 64 cuts73852 = true := by
 decide +kernel
def pointBounds73852 : List (Nat × Nat × Nat) := [(9683963904,116470148565010,116470538459597)]
theorem point_links_checked73852 : (cuts73852.take 1).map (fun c => (9683861505-1+2*2^10*c.k,116470019394651+c.lower,116470409289159+c.upper)) = pointBounds73852 := by
 decide +kernel
def cuts73853 : List PrefixCut := [⟨64,166866755,166866850⟩]
theorem checked73853 : checkPrefixCuts (2^48) 9683992577 10 Manual.Count131072.C073853.packed 64 cuts73853 = true := by
 decide +kernel
def cuts73854 : List PrefixCut := [⟨64,167823645,167823749⟩]
theorem checked73854 : checkPrefixCuts (2^48) 9684123649 10 Manual.Count131072.C073854.packed 64 cuts73854 = true := by
 decide +kernel
def cuts73855 : List PrefixCut := [⟨6,16014920,16014929⟩,
⟨64,164478895,164478994⟩]
theorem checked73855 : checkPrefixCuts (2^48) 9684254721 10 Manual.Count131072.C073855.packed 64 cuts73855 = true := by
 decide +kernel
def pointBounds73855 : List (Nat × Nat × Nat) := [(9684267008,116470534934361,116470924829177)]
theorem point_links_checked73855 : (cuts73855.take 1).map (fun c => (9684254721-1+2*2^10*c.k,116470518919441+c.lower,116470908814248+c.upper)) = pointBounds73855 := by
 decide +kernel
def cuts73856 : List PrefixCut := [⟨64,163982579,163982681⟩]
theorem checked73856 : checkPrefixCuts (2^48) 9684385793 10 Manual.Count131072.C073856.packed 64 cuts73856 = true := by
 decide +kernel
def cuts73857 : List PrefixCut := [⟨26,66499215,66499257⟩,
⟨64,164329129,164329233⟩]
theorem checked73857 : checkPrefixCuts (2^48) 9684516865 10 Manual.Count131072.C073857.packed 64 cuts73857 = true := by
 decide +kernel
def pointBounds73857 : List (Nat × Nat × Nat) := [(9684570112,116470913880130,116471303775180)]
theorem point_links_checked73857 : (cuts73857.take 1).map (fun c => (9684516865-1+2*2^10*c.k,116470847380915+c.lower,116471237275923+c.upper)) = pointBounds73857 := by
 decide +kernel
def cuts73858 : List PrefixCut := [⟨64,166012600,166012696⟩]
theorem checked73858 : checkPrefixCuts (2^48) 9684647937 10 Manual.Count131072.C073858.packed 64 cuts73858 = true := by
 decide +kernel
def cuts73859 : List PrefixCut := [⟨46,118288426,118288496⟩,
⟨64,165080337,165080436⟩]
theorem checked73859 : checkPrefixCuts (2^48) 9684779009 10 Manual.Count131072.C073859.packed 64 cuts73859 = true := by
 decide +kernel
def pointBounds73859 : List (Nat × Nat × Nat) := [(9684873216,116471296011070,116471685906348)]
theorem point_links_checked73859 : (cuts73859.take 1).map (fun c => (9684779009-1+2*2^10*c.k,116471177722644+c.lower,116471567617852+c.upper)) = pointBounds73859 := by
 decide +kernel
def cuts73860 : List PrefixCut := [⟨64,164903726,164903829⟩]
theorem checked73860 : checkPrefixCuts (2^48) 9684910081 10 Manual.Count131072.C073860.packed 64 cuts73860 = true := by
 decide +kernel
def cuts73861 : List PrefixCut := [⟨64,166383693,166383793⟩]
theorem checked73861 : checkPrefixCuts (2^48) 9685041153 10 Manual.Count131072.C073861.packed 64 cuts73861 = true := by
 decide +kernel
def cuts73862 : List PrefixCut := [⟨2,5027804,5027807⟩,
⟨64,167572993,167573087⟩]
theorem checked73862 : checkPrefixCuts (2^48) 9685172225 10 Manual.Count131072.C073862.packed 64 cuts73862 = true := by
 decide +kernel
def pointBounds73862 : List (Nat × Nat × Nat) := [(9685176320,116471679118204,116472069013717)]
theorem point_links_checked73862 : (cuts73862.take 1).map (fun c => (9685172225-1+2*2^10*c.k,116471674090400+c.lower,116472063985910+c.upper)) = pointBounds73862 := by
 decide +kernel
def cuts73863 : List PrefixCut := [⟨64,164926092,164926186⟩]
theorem checked73863 : checkPrefixCuts (2^48) 9685303297 10 Manual.Count131072.C073863.packed 64 cuts73863 = true := by
 decide +kernel
def cuts73864 : List PrefixCut := [⟨22,58210390,58210426⟩,
⟨64,168730912,168731015⟩]
theorem checked73864 : checkPrefixCuts (2^48) 9685434369 10 Manual.Count131072.C073864.packed 64 cuts73864 = true := by
 decide +kernel
def pointBounds73864 : List (Nat × Nat × Nat) := [(9685479424,116472064799875,116472454695609)]
theorem point_links_checked73864 : (cuts73864.take 1).map (fun c => (9685434369-1+2*2^10*c.k,116472006589485+c.lower,116472396485183+c.upper)) = pointBounds73864 := by
 decide +kernel
def cuts73865 : List PrefixCut := [⟨64,167856799,167856891⟩]
theorem checked73865 : checkPrefixCuts (2^48) 9685565441 10 Manual.Count131072.C073865.packed 64 cuts73865 = true := by
 decide +kernel
def cuts73866 : List PrefixCut := [⟨42,108193189,108193254⟩,
⟨64,166169002,166169101⟩]
theorem checked73866 : checkPrefixCuts (2^48) 9685696513 10 Manual.Count131072.C073866.packed 64 cuts73866 = true := by
 decide +kernel
def pointBounds73866 : List (Nat × Nat × Nat) := [(9685782528,116472451370385,116472841266343)]
theorem point_links_checked73866 : (cuts73866.take 1).map (fun c => (9685696513-1+2*2^10*c.k,116472343177196+c.lower,116472733073089+c.upper)) = pointBounds73866 := by
 decide +kernel
def cuts73867 : List PrefixCut := [⟨64,164917157,164917253⟩]
theorem checked73867 : checkPrefixCuts (2^48) 9685827585 10 Manual.Count131072.C073867.packed 64 cuts73867 = true := by
 decide +kernel
def cuts73868 : List PrefixCut := [⟨62,162532052,162532147⟩,
⟨64,167762800,167762897⟩]
theorem checked73868 : checkPrefixCuts (2^48) 9685958657 10 Manual.Count131072.C073868.packed 64 cuts73868 = true := by
 decide +kernel
def pointBounds73868 : List (Nat × Nat × Nat) := [(9686085632,116472836795407,116473226691590)]
theorem point_links_checked73868 : (cuts73868.take 1).map (fun c => (9685958657-1+2*2^10*c.k,116472674263355+c.lower,116473064159443+c.upper)) = pointBounds73868 := by
 decide +kernel
def cuts73869 : List PrefixCut := [⟨64,165522952,165523052⟩]
theorem checked73869 : checkPrefixCuts (2^48) 9686089729 10 Manual.Count131072.C073869.packed 64 cuts73869 = true := by
 decide +kernel
def cuts73870 : List PrefixCut := [⟨64,166624964,166625066⟩]
theorem checked73870 : checkPrefixCuts (2^48) 9686220801 10 Manual.Count131072.C073870.packed 64 cuts73870 = true := by
 decide +kernel
def cuts73871 : List PrefixCut := [⟨18,47976180,47976207⟩,
⟨64,165169780,165169878⟩]
theorem checked73871 : checkPrefixCuts (2^48) 9686351873 10 Manual.Count131072.C073871.packed 64 cuts73871 = true := by
 decide +kernel
def pointBounds73871 : List (Nat × Nat × Nat) := [(9686388736,116473222150251,116473612046665)]
theorem point_links_checked73871 : (cuts73871.take 1).map (fun c => (9686351873-1+2*2^10*c.k,116473174174071+c.lower,116473564070458+c.upper)) = pointBounds73871 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S8.B000120
