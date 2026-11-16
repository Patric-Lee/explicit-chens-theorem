import PlattAssemblyKernel
import PlattCertificates.Count131072.C069856
import PlattCertificates.Count131072.C069857
import PlattCertificates.Count131072.C069858
import PlattCertificates.Count131072.C069859
import PlattCertificates.Count131072.C069860
import PlattCertificates.Count131072.C069861
import PlattCertificates.Count131072.C069862
import PlattCertificates.Count131072.C069863
import PlattCertificates.Count131072.C069864
import PlattCertificates.Count131072.C069865
import PlattCertificates.Count131072.C069866
import PlattCertificates.Count131072.C069867
import PlattCertificates.Count131072.C069868
import PlattCertificates.Count131072.C069869
import PlattCertificates.Count131072.C069870
import PlattCertificates.Count131072.C069871
import PlattCertificates.Count131072.C069872
import PlattCertificates.Count131072.C069873
import PlattCertificates.Count131072.C069874
import PlattCertificates.Count131072.C069875
import PlattCertificates.Count131072.C069876
import PlattCertificates.Count131072.C069877
import PlattCertificates.Count131072.C069878
import PlattCertificates.Count131072.C069879
import PlattCertificates.Count131072.C069880
import PlattCertificates.Count131072.C069881
import PlattCertificates.Count131072.C069882
import PlattCertificates.Count131072.C069883
import PlattCertificates.Count131072.C069884
import PlattCertificates.Count131072.C069885
import PlattCertificates.Count131072.C069886
import PlattCertificates.Count131072.C069887
namespace ChenEffective.PlattWindow.Assembly.Prefix.S7.B000308
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts69856 : List PrefixCut := [⟨64,176717606,176717704⟩]
theorem checked69856 : checkPrefixCuts (2^48) 9160097793 10 Manual.Count131072.C069856.packed 64 cuts69856 = true := by
 decide +kernel
def cuts69857 : List PrefixCut := [⟨10,28146755,28146771⟩,
⟨64,173980309,173980410⟩]
theorem checked69857 : checkPrefixCuts (2^48) 9160228865 10 Manual.Count131072.C069857.packed 64 cuts69857 = true := by
 decide +kernel
def pointBounds69857 : List (Nat × Nat × Nat) := [(9160249344,115788686351238,115789075841736)]
theorem point_links_checked69857 : (cuts69857.take 1).map (fun c => (9160228865-1+2*2^10*c.k,115788658204483+c.lower,115789047694965+c.upper)) = pointBounds69857 := by
 decide +kernel
def cuts69858 : List PrefixCut := [⟨64,175944369,175944475⟩]
theorem checked69858 : checkPrefixCuts (2^48) 9160359937 10 Manual.Count131072.C069858.packed 64 cuts69858 = true := by
 decide +kernel
def cuts69859 : List PrefixCut := [⟨22,59886881,59886918⟩,
⟨64,172408268,172408368⟩]
theorem checked69859 : checkPrefixCuts (2^48) 9160491009 10 Manual.Count131072.C069859.packed 64 cuts69859 = true := by
 decide +kernel
def pointBounds69859 : List (Nat × Nat × Nat) := [(9160536064,115789068016042,115789457506768)]
theorem point_links_checked69859 : (cuts69859.take 1).map (fun c => (9160491009-1+2*2^10*c.k,115789008129161+c.lower,115789397619850+c.upper)) = pointBounds69859 := by
 decide +kernel
def cuts69860 : List PrefixCut := [⟨64,176123689,176123787⟩]
theorem checked69860 : checkPrefixCuts (2^48) 9160622081 10 Manual.Count131072.C069860.packed 64 cuts69860 = true := by
 decide +kernel
def cuts69861 : List PrefixCut := [⟨34,93560849,93560904⟩,
⟨64,177288757,177288865⟩]
theorem checked69861 : checkPrefixCuts (2^48) 9160753153 10 Manual.Count131072.C069861.packed 64 cuts69861 = true := by
 decide +kernel
def pointBounds69861 : List (Nat × Nat × Nat) := [(9160822784,115789450221967,115789839712909)]
theorem point_links_checked69861 : (cuts69861.take 1).map (fun c => (9160753153-1+2*2^10*c.k,115789356661118+c.lower,115789746152005+c.upper)) = pointBounds69861 := by
 decide +kernel
def cuts69862 : List PrefixCut := [⟨64,177931454,177931556⟩]
theorem checked69862 : checkPrefixCuts (2^48) 9160884225 10 Manual.Count131072.C069862.packed 64 cuts69862 = true := by
 decide +kernel
def cuts69863 : List PrefixCut := [⟨46,125788707,125788785⟩,
⟨64,175655248,175655355⟩]
theorem checked69863 : checkPrefixCuts (2^48) 9161015297 10 Manual.Count131072.C069863.packed 64 cuts69863 = true := by
 decide +kernel
def pointBounds69863 : List (Nat × Nat × Nat) := [(9161109504,115789837670036,115790227161211)]
theorem point_links_checked69863 : (cuts69863.take 1).map (fun c => (9161015297-1+2*2^10*c.k,115789711881329+c.lower,115790101372426+c.upper)) = pointBounds69863 := by
 decide +kernel
def cuts69864 : List PrefixCut := [⟨64,176513019,176513124⟩]
theorem checked69864 : checkPrefixCuts (2^48) 9161146369 10 Manual.Count131072.C069864.packed 64 cuts69864 = true := by
 decide +kernel
def cuts69865 : List PrefixCut := [⟨58,158321885,158321976⟩,
⟨64,174421259,174421360⟩]
theorem checked69865 : checkPrefixCuts (2^48) 9161277441 10 Manual.Count131072.C069865.packed 64 cuts69865 = true := by
 decide +kernel
def pointBounds69865 : List (Nat × Nat × Nat) := [(9161396224,115790222371481,115790611862881)]
theorem point_links_checked69865 : (cuts69865.take 1).map (fun c => (9161277441-1+2*2^10*c.k,115790064049596+c.lower,115790453540905+c.upper)) = pointBounds69865 := by
 decide +kernel
def cuts69866 : List PrefixCut := [⟨64,179457465,179457568⟩]
theorem checked69866 : checkPrefixCuts (2^48) 9161408513 10 Manual.Count131072.C069866.packed 64 cuts69866 = true := by
 decide +kernel
def cuts69867 : List PrefixCut := [⟨64,176659065,176659168⟩]
theorem checked69867 : checkPrefixCuts (2^48) 9161539585 10 Manual.Count131072.C069867.packed 64 cuts69867 = true := by
 decide +kernel
def cuts69868 : List PrefixCut := [⟨6,16098891,16098901⟩,
⟨64,176164979,176165077⟩]
theorem checked69868 : checkPrefixCuts (2^48) 9161670657 10 Manual.Count131072.C069868.packed 64 cuts69868 = true := by
 decide +kernel
def pointBounds69868 : List (Nat × Nat × Nat) := [(9161682944,115790610686276,115791000177902)]
theorem point_links_checked69868 : (cuts69868.take 1).map (fun c => (9161670657-1+2*2^10*c.k,115790594587385+c.lower,115790984079001+c.upper)) = pointBounds69868 := by
 decide +kernel
def cuts69869 : List PrefixCut := [⟨64,173704669,173704772⟩]
theorem checked69869 : checkPrefixCuts (2^48) 9161801729 10 Manual.Count131072.C069869.packed 64 cuts69869 = true := by
 decide +kernel
def cuts69870 : List PrefixCut := [⟨18,49001839,49001865⟩,
⟨64,173087739,173087838⟩]
theorem checked69870 : checkPrefixCuts (2^48) 9161932801 10 Manual.Count131072.C069870.packed 64 cuts69870 = true := by
 decide +kernel
def pointBounds69870 : List (Nat × Nat × Nat) := [(9161969664,115790993458872,115791382950715)]
theorem point_links_checked69870 : (cuts69870.take 1).map (fun c => (9161932801-1+2*2^10*c.k,115790944457033+c.lower,115791333948850+c.upper)) = pointBounds69870 := by
 decide +kernel
def cuts69871 : List PrefixCut := [⟨64,174314110,174314219⟩]
theorem checked69871 : checkPrefixCuts (2^48) 9162063873 10 Manual.Count131072.C069871.packed 64 cuts69871 = true := by
 decide +kernel
def cuts69872 : List PrefixCut := [⟨30,82486516,82486566⟩,
⟨64,174373072,174373179⟩]
theorem checked69872 : checkPrefixCuts (2^48) 9162194945 10 Manual.Count131072.C069872.packed 64 cuts69872 = true := by
 decide +kernel
def pointBounds69872 : List (Nat × Nat × Nat) := [(9162256384,115791374345398,115791763837473)]
theorem point_links_checked69872 : (cuts69872.take 1).map (fun c => (9162194945-1+2*2^10*c.k,115791291858882+c.lower,115791681350907+c.upper)) = pointBounds69872 := by
 decide +kernel
def cuts69873 : List PrefixCut := [⟨64,173387518,173387621⟩]
theorem checked69873 : checkPrefixCuts (2^48) 9162326017 10 Manual.Count131072.C069873.packed 64 cuts69873 = true := by
 decide +kernel
def cuts69874 : List PrefixCut := [⟨42,113849488,113849552⟩,
⟨64,172893512,172893610⟩]
theorem checked69874 : checkPrefixCuts (2^48) 9162457089 10 Manual.Count131072.C069874.packed 64 cuts69874 = true := by
 decide +kernel
def pointBounds69874 : List (Nat × Nat × Nat) := [(9162543104,115791753468960,115792142961259)]
theorem point_links_checked69874 : (cuts69874.take 1).map (fun c => (9162457089-1+2*2^10*c.k,115791639619472+c.lower,115792029111707+c.upper)) = pointBounds69874 := by
 decide +kernel
def cuts69875 : List PrefixCut := [⟨64,174273411,174273521⟩]
theorem checked69875 : checkPrefixCuts (2^48) 9162588161 10 Manual.Count131072.C069875.packed 64 cuts69875 = true := by
 decide +kernel
def cuts69876 : List PrefixCut := [⟨54,147698852,147698941⟩,
⟨64,174701008,174701113⟩]
theorem checked69876 : checkPrefixCuts (2^48) 9162719233 10 Manual.Count131072.C069876.packed 64 cuts69876 = true := by
 decide +kernel
def pointBounds69876 : List (Nat × Nat × Nat) := [(9162829824,115792134485247,115792523977779)]
theorem point_links_checked69876 : (cuts69876.take 1).map (fun c => (9162719233-1+2*2^10*c.k,115791986786395+c.lower,115792376278838+c.upper)) = pointBounds69876 := by
 decide +kernel
def cuts69877 : List PrefixCut := [⟨64,175896530,175896635⟩]
theorem checked69877 : checkPrefixCuts (2^48) 9162850305 10 Manual.Count131072.C069877.packed 64 cuts69877 = true := by
 decide +kernel
def cuts69878 : List PrefixCut := [⟨64,174972482,174972586⟩]
theorem checked69878 : checkPrefixCuts (2^48) 9162981377 10 Manual.Count131072.C069878.packed 64 cuts69878 = true := by
 decide +kernel
def cuts69879 : List PrefixCut := [⟨2,5775032,5775035⟩,
⟨64,175277146,175277243⟩]
theorem checked69879 : checkPrefixCuts (2^48) 9163112449 10 Manual.Count131072.C069879.packed 64 cuts69879 = true := by
 decide +kernel
def pointBounds69879 : List (Nat × Nat × Nat) := [(9163116544,115792518131447,115792907624207)]
theorem point_links_checked69879 : (cuts69879.take 1).map (fun c => (9163112449-1+2*2^10*c.k,115792512356415+c.lower,115792901849172+c.upper)) = pointBounds69879 := by
 decide +kernel
def cuts69880 : List PrefixCut := [⟨64,176042594,176042692⟩]
theorem checked69880 : checkPrefixCuts (2^48) 9163243521 10 Manual.Count131072.C069880.packed 64 cuts69880 = true := by
 decide +kernel
def cuts69881 : List PrefixCut := [⟨14,38673125,38673147⟩,
⟨64,177422333,177422443⟩]
theorem checked69881 : checkPrefixCuts (2^48) 9163374593 10 Manual.Count131072.C069881.packed 64 cuts69881 = true := by
 decide +kernel
def pointBounds69881 : List (Nat × Nat × Nat) := [(9163403264,115792902349280,115793291842254)]
theorem point_links_checked69881 : (cuts69881.take 1).map (fun c => (9163374593-1+2*2^10*c.k,115792863676155+c.lower,115793253169107+c.upper)) = pointBounds69881 := by
 decide +kernel
def cuts69882 : List PrefixCut := [⟨64,177235501,177235602⟩]
theorem checked69882 : checkPrefixCuts (2^48) 9163505665 10 Manual.Count131072.C069882.packed 64 cuts69882 = true := by
 decide +kernel
def cuts69883 : List PrefixCut := [⟨26,71569250,71569293⟩,
⟨64,173792750,173792853⟩]
theorem checked69883 : checkPrefixCuts (2^48) 9163636737 10 Manual.Count131072.C069883.packed 64 cuts69883 = true := by
 decide +kernel
def pointBounds69883 : List (Nat × Nat × Nat) := [(9163689984,115793289903239,115793679396445)]
theorem point_links_checked69883 : (cuts69883.take 1).map (fun c => (9163636737-1+2*2^10*c.k,115793218333989+c.lower,115793607827152+c.upper)) = pointBounds69883 := by
 decide +kernel
def cuts69884 : List PrefixCut := [⟨64,175418196,175418304⟩]
theorem checked69884 : checkPrefixCuts (2^48) 9163767809 10 Manual.Count131072.C069884.packed 64 cuts69884 = true := by
 decide +kernel
def cuts69885 : List PrefixCut := [⟨38,103910522,103910581⟩,
⟨64,174340649,174340752⟩]
theorem checked69885 : checkPrefixCuts (2^48) 9163898881 10 Manual.Count131072.C069885.packed 64 cuts69885 = true := by
 decide +kernel
def pointBounds69885 : List (Nat × Nat × Nat) := [(9163976704,115793671455457,115794060948890)]
theorem point_links_checked69885 : (cuts69885.take 1).map (fun c => (9163898881-1+2*2^10*c.k,115793567544935+c.lower,115793957038309+c.upper)) = pointBounds69885 := by
 decide +kernel
def cuts69886 : List PrefixCut := [⟨64,177716800,177716901⟩]
theorem checked69886 : checkPrefixCuts (2^48) 9164029953 10 Manual.Count131072.C069886.packed 64 cuts69886 = true := by
 decide +kernel
def cuts69887 : List PrefixCut := [⟨50,138277024,138277098⟩,
⟨64,178082832,178082927⟩]
theorem checked69887 : checkPrefixCuts (2^48) 9164161025 10 Manual.Count131072.C069887.packed 64 cuts69887 = true := by
 decide +kernel
def pointBounds69887 : List (Nat × Nat × Nat) := [(9164263424,115794057879408,115794447373060)]
theorem point_links_checked69887 : (cuts69887.take 1).map (fun c => (9164161025-1+2*2^10*c.k,115793919602384+c.lower,115794309095962+c.upper)) = pointBounds69887 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S7.B000308
