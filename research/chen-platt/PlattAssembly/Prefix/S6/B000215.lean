import PlattAssemblyKernel
import PlattCertificates.Count131072.C056880
import PlattCertificates.Count131072.C056881
import PlattCertificates.Count131072.C056882
import PlattCertificates.Count131072.C056883
import PlattCertificates.Count131072.C056884
import PlattCertificates.Count131072.C056885
import PlattCertificates.Count131072.C056886
import PlattCertificates.Count131072.C056887
import PlattCertificates.Count131072.C056888
import PlattCertificates.Count131072.C056889
import PlattCertificates.Count131072.C056890
import PlattCertificates.Count131072.C056891
import PlattCertificates.Count131072.C056892
import PlattCertificates.Count131072.C056893
import PlattCertificates.Count131072.C056894
import PlattCertificates.Count131072.C056895
import PlattCertificates.Count131072.C056896
import PlattCertificates.Count131072.C056897
import PlattCertificates.Count131072.C056898
import PlattCertificates.Count131072.C056899
import PlattCertificates.Count131072.C056900
import PlattCertificates.Count131072.C056901
import PlattCertificates.Count131072.C056902
import PlattCertificates.Count131072.C056903
import PlattCertificates.Count131072.C056904
import PlattCertificates.Count131072.C056905
import PlattCertificates.Count131072.C056906
import PlattCertificates.Count131072.C056907
import PlattCertificates.Count131072.C056908
import PlattCertificates.Count131072.C056909
import PlattCertificates.Count131072.C056910
import PlattCertificates.Count131072.C056911
namespace ChenEffective.PlattWindow.Assembly.Prefix.S6.B000215
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts56880 : List PrefixCut := [⟨32,108939664,108939724⟩,
⟨64,220029221,220029341⟩]
theorem checked56880 : checkPrefixCuts (2^48) 7459307521 10 Manual.Count131072.C056880.packed 64 cuts56880 = true := by
 decide +kernel
def pointBounds56880 : List (Nat × Nat × Nat) := [(7459373056,113256874870568,113257262901545)]
theorem point_links_checked56880 : (cuts56880.take 1).map (fun c => (7459307521-1+2*2^10*c.k,113256765930904+c.lower,113257153961821+c.upper)) = pointBounds56880 := by
 decide +kernel
def cuts56881 : List PrefixCut := [⟨64,217723607,217723727⟩]
theorem checked56881 : checkPrefixCuts (2^48) 7459438593 10 Manual.Count131072.C056881.packed 64 cuts56881 = true := by
 decide +kernel
def cuts56882 : List PrefixCut := [⟨18,61052484,61052519⟩,
⟨64,216512328,216512454⟩]
theorem checked56882 : checkPrefixCuts (2^48) 7459569665 10 Manual.Count131072.C056882.packed 64 cuts56882 = true := by
 decide +kernel
def pointBounds56882 : List (Nat × Nat × Nat) := [(7459606528,113257264736216,113257652767408)]
theorem point_links_checked56882 : (cuts56882.take 1).map (fun c => (7459569665-1+2*2^10*c.k,113257203683732+c.lower,113257591714889+c.upper)) = pointBounds56882 := by
 decide +kernel
def cuts56883 : List PrefixCut := [⟨64,220319487,220319609⟩]
theorem checked56883 : checkPrefixCuts (2^48) 7459700737 10 Manual.Count131072.C056883.packed 64 cuts56883 = true := by
 decide +kernel
def cuts56884 : List PrefixCut := [⟨4,12640236,12640244⟩,
⟨64,218391306,218391430⟩]
theorem checked56884 : checkPrefixCuts (2^48) 7459831809 10 Manual.Count131072.C056884.packed 64 cuts56884 = true := by
 decide +kernel
def pointBounds56884 : List (Nat × Nat × Nat) := [(7459840000,113257653155783,113258041187196)]
theorem point_links_checked56884 : (cuts56884.take 1).map (fun c => (7459831809-1+2*2^10*c.k,113257640515547+c.lower,113258028546952+c.upper)) = pointBounds56884 := by
 decide +kernel
def cuts56885 : List PrefixCut := [⟨54,188957498,188957604⟩,
⟨64,223443446,223443572⟩]
theorem checked56885 : checkPrefixCuts (2^48) 7459962881 10 Manual.Count131072.C056885.packed 64 cuts56885 = true := by
 decide +kernel
def pointBounds56885 : List (Nat × Nat × Nat) := [(7460073472,113258047864351,113258435895986)]
theorem point_links_checked56885 : (cuts56885.take 1).map (fun c => (7459962881-1+2*2^10*c.k,113257858906853+c.lower,113258246938382+c.upper)) = pointBounds56885 := by
 decide +kernel
def cuts56886 : List PrefixCut := [⟨64,216610324,216610447⟩]
theorem checked56886 : checkPrefixCuts (2^48) 7460093953 10 Manual.Count131072.C056886.packed 64 cuts56886 = true := by
 decide +kernel
def cuts56887 : List PrefixCut := [⟨40,134771104,134771180⟩,
⟨64,214531360,214531483⟩]
theorem checked56887 : checkPrefixCuts (2^48) 7460225025 10 Manual.Count131072.C056887.packed 64 cuts56887 = true := by
 decide +kernel
def pointBounds56887 : List (Nat × Nat × Nat) := [(7460306944,113258433731727,113258821763581)]
theorem point_links_checked56887 : (cuts56887.take 1).map (fun c => (7460225025-1+2*2^10*c.k,113258298960623+c.lower,113258686992401+c.upper)) = pointBounds56887 := by
 decide +kernel
def cuts56888 : List PrefixCut := [⟨64,216829075,216829201⟩]
theorem checked56888 : checkPrefixCuts (2^48) 7460356097 10 Manual.Count131072.C056888.packed 64 cuts56888 = true := by
 decide +kernel
def cuts56889 : List PrefixCut := [⟨26,87530402,87530451⟩,
⟨64,217240261,217240384⟩]
theorem checked56889 : checkPrefixCuts (2^48) 7460487169 10 Manual.Count131072.C056889.packed 64 cuts56889 = true := by
 decide +kernel
def pointBounds56889 : List (Nat × Nat × Nat) := [(7460540416,113258817851460,113259205883536)]
theorem point_links_checked56889 : (cuts56889.take 1).map (fun c => (7460487169-1+2*2^10*c.k,113258730321058+c.lower,113259118353085+c.upper)) = pointBounds56889 := by
 decide +kernel
def cuts56890 : List PrefixCut := [⟨64,218670118,218670244⟩]
theorem checked56890 : checkPrefixCuts (2^48) 7460618241 10 Manual.Count131072.C056890.packed 64 cuts56890 = true := by
 decide +kernel
def cuts56891 : List PrefixCut := [⟨12,39236462,39236486⟩,
⟨64,218590794,218590920⟩]
theorem checked56891 : checkPrefixCuts (2^48) 7460749313 10 Manual.Count131072.C056891.packed 64 cuts56891 = true := by
 decide +kernel
def pointBounds56891 : List (Nat × Nat × Nat) := [(7460773888,113259205467899,113259593500199)]
theorem point_links_checked56891 : (cuts56891.take 1).map (fun c => (7460749313-1+2*2^10*c.k,113259166231437+c.lower,113259554263713+c.upper)) = pointBounds56891 := by
 decide +kernel
def cuts56892 : List PrefixCut := [⟨62,207759540,207759659⟩,
⟨64,214323884,214324006⟩]
theorem checked56892 : checkPrefixCuts (2^48) 7460880385 10 Manual.Count131072.C056892.packed 64 cuts56892 = true := by
 decide +kernel
def pointBounds56892 : List (Nat × Nat × Nat) := [(7461007360,113259592581771,113259980614292)]
theorem point_links_checked56892 : (cuts56892.take 1).map (fun c => (7460880385-1+2*2^10*c.k,113259384822231+c.lower,113259772854633+c.upper)) = pointBounds56892 := by
 decide +kernel
def cuts56893 : List PrefixCut := [⟨64,215791429,215791555⟩]
theorem checked56893 : checkPrefixCuts (2^48) 7461011457 10 Manual.Count131072.C056893.packed 64 cuts56893 = true := by
 decide +kernel
def cuts56894 : List PrefixCut := [⟨48,164180028,164180123⟩,
⟨64,216542138,216542262⟩]
theorem checked56894 : checkPrefixCuts (2^48) 7461142529 10 Manual.Count131072.C056894.packed 64 cuts56894 = true := by
 decide +kernel
def pointBounds56894 : List (Nat × Nat × Nat) := [(7461240832,113259979117572,113260367150317)]
theorem point_links_checked56894 : (cuts56894.take 1).map (fun c => (7461142529-1+2*2^10*c.k,113259814937544+c.lower,113260202970194+c.upper)) = pointBounds56894 := by
 decide +kernel
def cuts56895 : List PrefixCut := [⟨64,215670666,215670789⟩]
theorem checked56895 : checkPrefixCuts (2^48) 7461273601 10 Manual.Count131072.C056895.packed 64 cuts56895 = true := by
 decide +kernel
def cuts56896 : List PrefixCut := [⟨34,117396898,117396964⟩,
⟨64,219288368,219288491⟩]
theorem checked56896 : checkPrefixCuts (2^48) 7461404673 10 Manual.Count131072.C056896.packed 64 cuts56896 = true := by
 decide +kernel
def pointBounds56896 : List (Nat × Nat × Nat) := [(7461474304,113260364547246,113260752580209)]
theorem point_links_checked56896 : (cuts56896.take 1).map (fun c => (7461404673-1+2*2^10*c.k,113260247150348+c.lower,113260635183245+c.upper)) = pointBounds56896 := by
 decide +kernel
def cuts56897 : List PrefixCut := [⟨64,216643884,216644010⟩]
theorem checked56897 : checkPrefixCuts (2^48) 7461535745 10 Manual.Count131072.C056897.packed 64 cuts56897 = true := by
 decide +kernel
def cuts56898 : List PrefixCut := [⟨20,65901536,65901575⟩,
⟨64,215093453,215093579⟩]
theorem checked56898 : checkPrefixCuts (2^48) 7461666817 10 Manual.Count131072.C056898.packed 64 cuts56898 = true := by
 decide +kernel
def pointBounds56898 : List (Nat × Nat × Nat) := [(7461707776,113260748984136,113261137017321)]
theorem point_links_checked56898 : (cuts56898.take 1).map (fun c => (7461666817-1+2*2^10*c.k,113260683082600+c.lower,113261071115746+c.upper)) = pointBounds56898 := by
 decide +kernel
def cuts56899 : List PrefixCut := [⟨64,217692525,217692646⟩]
theorem checked56899 : checkPrefixCuts (2^48) 7461797889 10 Manual.Count131072.C056899.packed 64 cuts56899 = true := by
 decide +kernel
def cuts56900 : List PrefixCut := [⟨6,21538939,21538951⟩,
⟨64,219989655,219989780⟩]
theorem checked56900 : checkPrefixCuts (2^48) 7461928961 10 Manual.Count131072.C056900.packed 64 cuts56900 = true := by
 decide +kernel
def pointBounds56900 : List (Nat × Nat × Nat) := [(7461941248,113261137407517,113261525440922)]
theorem point_links_checked56900 : (cuts56900.take 1).map (fun c => (7461928961-1+2*2^10*c.k,113261115868578+c.lower,113261503901971+c.upper)) = pointBounds56900 := by
 decide +kernel
def cuts56901 : List PrefixCut := [⟨56,193506248,193506355⟩,
⟨64,219495454,219495575⟩]
theorem checked56901 : checkPrefixCuts (2^48) 7462060033 10 Manual.Count131072.C056901.packed 64 cuts56901 = true := by
 decide +kernel
def pointBounds56901 : List (Nat × Nat × Nat) := [(7462174720,113261529364481,113261917398106)]
theorem point_links_checked56901 : (cuts56901.take 1).map (fun c => (7462060033-1+2*2^10*c.k,113261335858233+c.lower,113261723891751+c.upper)) = pointBounds56901 := by
 decide +kernel
def cuts56902 : List PrefixCut := [⟨64,214701166,214701289⟩]
theorem checked56902 : checkPrefixCuts (2^48) 7462191105 10 Manual.Count131072.C056902.packed 64 cuts56902 = true := by
 decide +kernel
def cuts56903 : List PrefixCut := [⟨42,141220904,141220986⟩,
⟨64,215791232,215791354⟩]
theorem checked56903 : checkPrefixCuts (2^48) 7462322177 10 Manual.Count131072.C056903.packed 64 cuts56903 = true := by
 decide +kernel
def pointBounds56903 : List (Nat × Nat × Nat) := [(7462408192,113261911275757,113262299309601)]
theorem point_links_checked56903 : (cuts56903.take 1).map (fun c => (7462322177-1+2*2^10*c.k,113261770054853+c.lower,113262158088615+c.upper)) = pointBounds56903 := by
 decide +kernel
def cuts56904 : List PrefixCut := [⟨64,219408422,219408545⟩]
theorem checked56904 : checkPrefixCuts (2^48) 7462453249 10 Manual.Count131072.C056904.packed 64 cuts56904 = true := by
 decide +kernel
def cuts56905 : List PrefixCut := [⟨28,94785348,94785403⟩,
⟨64,214991573,214991698⟩]
theorem checked56905 : checkPrefixCuts (2^48) 7462584321 10 Manual.Count131072.C056905.packed 64 cuts56905 = true := by
 decide +kernel
def pointBounds56905 : List (Nat × Nat × Nat) := [(7462641664,113262300039855,113262688073917)]
theorem point_links_checked56905 : (cuts56905.take 1).map (fun c => (7462584321-1+2*2^10*c.k,113262205254507+c.lower,113262593288514+c.upper)) = pointBounds56905 := by
 decide +kernel
def cuts56906 : List PrefixCut := [⟨64,216496497,216496621⟩]
theorem checked56906 : checkPrefixCuts (2^48) 7462715393 10 Manual.Count131072.C056906.packed 64 cuts56906 = true := by
 decide +kernel
def cuts56907 : List PrefixCut := [⟨14,46353893,46353920⟩,
⟨64,218039053,218039176⟩]
theorem checked56907 : checkPrefixCuts (2^48) 7462846465 10 Manual.Count131072.C056907.packed 64 cuts56907 = true := by
 decide +kernel
def pointBounds56907 : List (Nat × Nat × Nat) := [(7462875136,113262683096470,113263071130753)]
theorem point_links_checked56907 : (cuts56907.take 1).map (fun c => (7462846465-1+2*2^10*c.k,113262636742577+c.lower,113263024776833+c.upper)) = pointBounds56907 := by
 decide +kernel
def cuts56908 : List PrefixCut := [⟨64,218638678,218638804⟩]
theorem checked56908 : checkPrefixCuts (2^48) 7462977537 10 Manual.Count131072.C056908.packed 64 cuts56908 = true := by
 decide +kernel
def pointBounds56908 : List (Nat × Nat × Nat) := [(7463108608,113263073420308,113263461454813)]
theorem point_links_checked56908 : (cuts56908.take 1).map (fun c => (7462977537-1+2*2^10*c.k,113262854781630+c.lower,113263242816009+c.upper)) = pointBounds56908 := by
 decide +kernel
def cuts56909 : List PrefixCut := [⟨64,220181180,220181302⟩]
theorem checked56909 : checkPrefixCuts (2^48) 7463108609 10 Manual.Count131072.C056909.packed 64 cuts56909 = true := by
 decide +kernel
def cuts56910 : List PrefixCut := [⟨50,169187607,169187704⟩,
⟨64,217046991,217047116⟩]
theorem checked56910 : checkPrefixCuts (2^48) 7463239681 10 Manual.Count131072.C056910.packed 64 cuts56910 = true := by
 decide +kernel
def pointBounds56910 : List (Nat × Nat × Nat) := [(7463342080,113263462789095,113263850823819)]
theorem point_links_checked56910 : (cuts56910.take 1).map (fun c => (7463239681-1+2*2^10*c.k,113263293601488+c.lower,113263681636115+c.upper)) = pointBounds56910 := by
 decide +kernel
def cuts56911 : List PrefixCut := [⟨64,214327795,214327916⟩]
theorem checked56911 : checkPrefixCuts (2^48) 7463370753 10 Manual.Count131072.C056911.packed 64 cuts56911 = true := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S6.B000215
