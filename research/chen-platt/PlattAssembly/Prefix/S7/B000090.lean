import PlattAssemblyKernel
import PlattCertificates.Count131072.C062880
import PlattCertificates.Count131072.C062881
import PlattCertificates.Count131072.C062882
import PlattCertificates.Count131072.C062883
import PlattCertificates.Count131072.C062884
import PlattCertificates.Count131072.C062885
import PlattCertificates.Count131072.C062886
import PlattCertificates.Count131072.C062887
import PlattCertificates.Count131072.C062888
import PlattCertificates.Count131072.C062889
import PlattCertificates.Count131072.C062890
import PlattCertificates.Count131072.C062891
import PlattCertificates.Count131072.C062892
import PlattCertificates.Count131072.C062893
import PlattCertificates.Count131072.C062894
import PlattCertificates.Count131072.C062895
import PlattCertificates.Count131072.C062896
import PlattCertificates.Count131072.C062897
import PlattCertificates.Count131072.C062898
import PlattCertificates.Count131072.C062899
import PlattCertificates.Count131072.C062900
import PlattCertificates.Count131072.C062901
import PlattCertificates.Count131072.C062902
import PlattCertificates.Count131072.C062903
import PlattCertificates.Count131072.C062904
import PlattCertificates.Count131072.C062905
import PlattCertificates.Count131072.C062906
import PlattCertificates.Count131072.C062907
import PlattCertificates.Count131072.C062908
import PlattCertificates.Count131072.C062909
import PlattCertificates.Count131072.C062910
import PlattCertificates.Count131072.C062911
namespace ChenEffective.PlattWindow.Assembly.Prefix.S7.B000090
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts62880 : List PrefixCut := [⟨8,25158058,25158073⟩,
⟨64,196040327,196040443⟩]
theorem checked62880 : checkPrefixCuts (2^48) 8245739521 10 Manual.Count131072.C062880.packed 64 cuts62880 = true := by
 decide +kernel
def pointBounds62880 : List (Nat × Nat × Nat) := [(8245755904,114495155999539,114495544738222)]
theorem point_links_checked62880 : (cuts62880.take 1).map (fun c => (8245739521-1+2*2^10*c.k,114495130841481+c.lower,114495519580149+c.upper)) = pointBounds62880 := by
 decide +kernel
def cuts62881 : List PrefixCut := [⟨64,198051162,198051277⟩]
theorem checked62881 : checkPrefixCuts (2^48) 8245870593 10 Manual.Count131072.C062881.packed 64 cuts62881 = true := by
 decide +kernel
def cuts62882 : List PrefixCut := [⟨6,18774078,18774088⟩,
⟨64,196136498,196136612⟩]
theorem checked62882 : checkPrefixCuts (2^48) 8246001665 10 Manual.Count131072.C062882.packed 64 cuts62882 = true := by
 decide +kernel
def pointBounds62882 : List (Nat × Nat × Nat) := [(8246013952,114495543707048,114495932445957)]
theorem point_links_checked62882 : (cuts62882.take 1).map (fun c => (8246001665-1+2*2^10*c.k,114495524932970+c.lower,114495913671869+c.upper)) = pointBounds62882 := by
 decide +kernel
def cuts62883 : List PrefixCut := [⟨64,195348283,195348401⟩]
theorem checked62883 : checkPrefixCuts (2^48) 8246132737 10 Manual.Count131072.C062883.packed 64 cuts62883 = true := by
 decide +kernel
def cuts62884 : List PrefixCut := [⟨4,12083298,12083305⟩,
⟨64,196369200,196369308⟩]
theorem checked62884 : checkPrefixCuts (2^48) 8246263809 10 Manual.Count131072.C062884.packed 64 cuts62884 = true := by
 decide +kernel
def pointBounds62884 : List (Nat × Nat × Nat) := [(8246272000,114495928501049,114496317240187)]
theorem point_links_checked62884 : (cuts62884.take 1).map (fun c => (8246263809-1+2*2^10*c.k,114495916417751+c.lower,114496305156882+c.upper)) = pointBounds62884 := by
 decide +kernel
def cuts62885 : List PrefixCut := [⟨64,192952786,192952897⟩]
theorem checked62885 : checkPrefixCuts (2^48) 8246394881 10 Manual.Count131072.C062885.packed 64 cuts62885 = true := by
 decide +kernel
def cuts62886 : List PrefixCut := [⟨2,5631868,5631871⟩,
⟨64,196704264,196704375⟩]
theorem checked62886 : checkPrefixCuts (2^48) 8246525953 10 Manual.Count131072.C062886.packed 64 cuts62886 = true := by
 decide +kernel
def pointBounds62886 : List (Nat × Nat × Nat) := [(8246530048,114496311371605,114496700110958)]
theorem point_links_checked62886 : (cuts62886.take 1).map (fun c => (8246525953-1+2*2^10*c.k,114496305739737+c.lower,114496694479087+c.upper)) = pointBounds62886 := by
 decide +kernel
def cuts62887 : List PrefixCut := [⟨64,196462236,196462344⟩]
theorem checked62887 : checkPrefixCuts (2^48) 8246657025 10 Manual.Count131072.C062887.packed 64 cuts62887 = true := by
 decide +kernel
def pointBounds62887 : List (Nat × Nat × Nat) := [(8246788096,114496698906237,114497087645806)]
theorem point_links_checked62887 : (cuts62887.take 1).map (fun c => (8246657025-1+2*2^10*c.k,114496502444001+c.lower,114496891183462+c.upper)) = pointBounds62887 := by
 decide +kernel
def cuts62888 : List PrefixCut := [⟨64,195025590,195025701⟩]
theorem checked62888 : checkPrefixCuts (2^48) 8246788097 10 Manual.Count131072.C062888.packed 64 cuts62888 = true := by
 decide +kernel
def cuts62889 : List PrefixCut := [⟨62,190483167,190483273⟩,
⟨64,196831418,196831527⟩]
theorem checked62889 : checkPrefixCuts (2^48) 8246919169 10 Manual.Count131072.C062889.packed 64 cuts62889 = true := by
 decide +kernel
def pointBounds62889 : List (Nat × Nat × Nat) := [(8247046144,114497084414994,114497473154780)]
theorem point_links_checked62889 : (cuts62889.take 1).map (fun c => (8246919169-1+2*2^10*c.k,114496893931827+c.lower,114497282671507+c.upper)) = pointBounds62889 := by
 decide +kernel
def cuts62890 : List PrefixCut := [⟨64,195838514,195838632⟩]
theorem checked62890 : checkPrefixCuts (2^48) 8247050241 10 Manual.Count131072.C062890.packed 64 cuts62890 = true := by
 decide +kernel
def cuts62891 : List PrefixCut := [⟨60,182866262,182866371⟩,
⟨64,194436096,194436212⟩]
theorem checked62891 : checkPrefixCuts (2^48) 8247181313 10 Manual.Count131072.C062891.packed 64 cuts62891 = true := by
 decide +kernel
def pointBounds62891 : List (Nat × Nat × Nat) := [(8247304192,114497469468021,114497858208037)]
theorem point_links_checked62891 : (cuts62891.take 1).map (fun c => (8247181313-1+2*2^10*c.k,114497286601759+c.lower,114497675341666+c.upper)) = pointBounds62891 := by
 decide +kernel
def cuts62892 : List PrefixCut := [⟨64,195047320,195047428⟩]
theorem checked62892 : checkPrefixCuts (2^48) 8247312385 10 Manual.Count131072.C062892.packed 64 cuts62892 = true := by
 decide +kernel
def cuts62893 : List PrefixCut := [⟨58,178799217,178799314⟩,
⟨64,196341126,196341234⟩]
theorem checked62893 : checkPrefixCuts (2^48) 8247443457 10 Manual.Count131072.C062893.packed 64 cuts62893 = true := by
 decide +kernel
def pointBounds62893 : List (Nat × Nat × Nat) := [(8247562240,114497854884392,114498243624620)]
theorem point_links_checked62893 : (cuts62893.take 1).map (fun c => (8247443457-1+2*2^10*c.k,114497676085175+c.lower,114498064825306+c.upper)) = pointBounds62893 := by
 decide +kernel
def cuts62894 : List PrefixCut := [⟨64,194358569,194358682⟩]
theorem checked62894 : checkPrefixCuts (2^48) 8247574529 10 Manual.Count131072.C062894.packed 64 cuts62894 = true := by
 decide +kernel
def cuts62895 : List PrefixCut := [⟨56,172957778,172957881⟩,
⟨64,197222182,197222299⟩]
theorem checked62895 : checkPrefixCuts (2^48) 8247705601 10 Manual.Count131072.C062895.packed 64 cuts62895 = true := by
 decide +kernel
def pointBounds62895 : List (Nat × Nat × Nat) := [(8247820288,114498239742648,114498628483103)]
theorem point_links_checked62895 : (cuts62895.take 1).map (fun c => (8247705601-1+2*2^10*c.k,114498066784870+c.lower,114498455525222+c.upper)) = pointBounds62895 := by
 decide +kernel
def cuts62896 : List PrefixCut := [⟨64,194966695,194966808⟩]
theorem checked62896 : checkPrefixCuts (2^48) 8247836673 10 Manual.Count131072.C062896.packed 64 cuts62896 = true := by
 decide +kernel
def cuts62897 : List PrefixCut := [⟨54,165478656,165478752⟩,
⟨64,196123872,196123984⟩]
theorem checked62897 : checkPrefixCuts (2^48) 8247967745 10 Manual.Count131072.C062897.packed 64 cuts62897 = true := by
 decide +kernel
def pointBounds62897 : List (Nat × Nat × Nat) := [(8248078336,114498624452403,114499013193081)]
theorem point_links_checked62897 : (cuts62897.take 1).map (fun c => (8247967745-1+2*2^10*c.k,114498458973747+c.lower,114498847714329+c.upper)) = pointBounds62897 := by
 decide +kernel
def cuts62898 : List PrefixCut := [⟨64,196632650,196632761⟩]
theorem checked62898 : checkPrefixCuts (2^48) 8248098817 10 Manual.Count131072.C062898.packed 64 cuts62898 = true := by
 decide +kernel
def cuts62899 : List PrefixCut := [⟨52,159501513,159501607⟩,
⟨64,195708138,195708253⟩]
theorem checked62899 : checkPrefixCuts (2^48) 8248229889 10 Manual.Count131072.C062899.packed 64 cuts62899 = true := by
 decide +kernel
def pointBounds62899 : List (Nat × Nat × Nat) := [(8248336384,114499011231782,114499399972681)]
theorem point_links_checked62899 : (cuts62899.take 1).map (fun c => (8248229889-1+2*2^10*c.k,114498851730269+c.lower,114499240471074+c.upper)) = pointBounds62899 := by
 decide +kernel
def cuts62900 : List PrefixCut := [⟨64,194715419,194715529⟩]
theorem checked62900 : checkPrefixCuts (2^48) 8248360961 10 Manual.Count131072.C062900.packed 64 cuts62900 = true := by
 decide +kernel
def cuts62901 : List PrefixCut := [⟨50,150624195,150624283⟩,
⟨64,192357753,192357866⟩]
theorem checked62901 : checkPrefixCuts (2^48) 8248492033 10 Manual.Count131072.C062901.packed 64 cuts62901 = true := by
 decide +kernel
def pointBounds62901 : List (Nat × Nat × Nat) := [(8248594432,114499392778021,114499781519139)]
theorem point_links_checked62901 : (cuts62901.take 1).map (fun c => (8248492033-1+2*2^10*c.k,114499242153826+c.lower,114499630894856+c.upper)) = pointBounds62901 := by
 decide +kernel
def cuts62902 : List PrefixCut := [⟨64,196893129,196893240⟩]
theorem checked62902 : checkPrefixCuts (2^48) 8248623105 10 Manual.Count131072.C062902.packed 64 cuts62902 = true := by
 decide +kernel
def cuts62903 : List PrefixCut := [⟨48,146865893,146865979⟩,
⟨64,193545949,193546062⟩]
theorem checked62903 : checkPrefixCuts (2^48) 8248754177 10 Manual.Count131072.C062903.packed 64 cuts62903 = true := by
 decide +kernel
def pointBounds62903 : List (Nat × Nat × Nat) := [(8248852480,114499778270601,114500167011941)]
theorem point_links_checked62903 : (cuts62903.take 1).map (fun c => (8248754177-1+2*2^10*c.k,114499631404708+c.lower,114500020145962+c.upper)) = pointBounds62903 := by
 decide +kernel
def cuts62904 : List PrefixCut := [⟨64,194873648,194873754⟩]
theorem checked62904 : checkPrefixCuts (2^48) 8248885249 10 Manual.Count131072.C062904.packed 64 cuts62904 = true := by
 decide +kernel
def cuts62905 : List PrefixCut := [⟨46,140275713,140275792⟩,
⟨64,194085748,194085860⟩]
theorem checked62905 : checkPrefixCuts (2^48) 8249016321 10 Manual.Count131072.C062905.packed 64 cuts62905 = true := by
 decide +kernel
def pointBounds62905 : List (Nat × Nat × Nat) := [(8249110528,114500160100018,114500548841570)]
theorem point_links_checked62905 : (cuts62905.take 1).map (fun c => (8249016321-1+2*2^10*c.k,114500019824305+c.lower,114500408565778+c.upper)) = pointBounds62905 := by
 decide +kernel
def cuts62906 : List PrefixCut := [⟨64,195072162,195072278⟩]
theorem checked62906 : checkPrefixCuts (2^48) 8249147393 10 Manual.Count131072.C062906.packed 64 cuts62906 = true := by
 decide +kernel
def cuts62907 : List PrefixCut := [⟨44,135972043,135972118⟩,
⟨64,197628138,197628249⟩]
theorem checked62907 : checkPrefixCuts (2^48) 8249278465 10 Manual.Count131072.C062907.packed 64 cuts62907 = true := by
 decide +kernel
def pointBounds62907 : List (Nat × Nat × Nat) := [(8249368576,114500544954258,114500933696034)]
theorem point_links_checked62907 : (cuts62907.take 1).map (fun c => (8249278465-1+2*2^10*c.k,114500408982215+c.lower,114500797723916+c.upper)) = pointBounds62907 := by
 decide +kernel
def cuts62908 : List PrefixCut := [⟨64,194690667,194690777⟩]
theorem checked62908 : checkPrefixCuts (2^48) 8249409537 10 Manual.Count131072.C062908.packed 64 cuts62908 = true := by
 decide +kernel
def cuts62909 : List PrefixCut := [⟨42,129723833,129723905⟩,
⟨64,195574700,195574808⟩]
theorem checked62909 : checkPrefixCuts (2^48) 8249540609 10 Manual.Count131072.C062909.packed 64 cuts62909 = true := by
 decide +kernel
def pointBounds62909 : List (Nat × Nat × Nat) := [(8249626624,114500931024853,114501319766847)]
theorem point_links_checked62909 : (cuts62909.take 1).map (fun c => (8249540609-1+2*2^10*c.k,114500801301020+c.lower,114501190042942+c.upper)) = pointBounds62909 := by
 decide +kernel
def cuts62910 : List PrefixCut := [⟨64,194104456,194104569⟩]
theorem checked62910 : checkPrefixCuts (2^48) 8249671681 10 Manual.Count131072.C062910.packed 64 cuts62910 = true := by
 decide +kernel
def cuts62911 : List PrefixCut := [⟨40,122315951,122316022⟩,
⟨64,196523783,196523897⟩]
theorem checked62911 : checkPrefixCuts (2^48) 8249802753 10 Manual.Count131072.C062911.packed 64 cuts62911 = true := by
 decide +kernel
def pointBounds62911 : List (Nat × Nat × Nat) := [(8249884672,114501313296127,114501702038341)]
theorem point_links_checked62911 : (cuts62911.take 1).map (fun c => (8249802753-1+2*2^10*c.k,114501190980176+c.lower,114501579722319+c.upper)) = pointBounds62911 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S7.B000090
