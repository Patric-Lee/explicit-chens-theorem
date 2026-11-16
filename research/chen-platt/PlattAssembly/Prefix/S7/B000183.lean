import PlattAssemblyKernel
import PlattCertificates.Count131072.C065856
import PlattCertificates.Count131072.C065857
import PlattCertificates.Count131072.C065858
import PlattCertificates.Count131072.C065859
import PlattCertificates.Count131072.C065860
import PlattCertificates.Count131072.C065861
import PlattCertificates.Count131072.C065862
import PlattCertificates.Count131072.C065863
import PlattCertificates.Count131072.C065864
import PlattCertificates.Count131072.C065865
import PlattCertificates.Count131072.C065866
import PlattCertificates.Count131072.C065867
import PlattCertificates.Count131072.C065868
import PlattCertificates.Count131072.C065869
import PlattCertificates.Count131072.C065870
import PlattCertificates.Count131072.C065871
import PlattCertificates.Count131072.C065872
import PlattCertificates.Count131072.C065873
import PlattCertificates.Count131072.C065874
import PlattCertificates.Count131072.C065875
import PlattCertificates.Count131072.C065876
import PlattCertificates.Count131072.C065877
import PlattCertificates.Count131072.C065878
import PlattCertificates.Count131072.C065879
import PlattCertificates.Count131072.C065880
import PlattCertificates.Count131072.C065881
import PlattCertificates.Count131072.C065882
import PlattCertificates.Count131072.C065883
import PlattCertificates.Count131072.C065884
import PlattCertificates.Count131072.C065885
import PlattCertificates.Count131072.C065886
import PlattCertificates.Count131072.C065887
namespace ChenEffective.PlattWindow.Assembly.Prefix.S7.B000183
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts65856 : List PrefixCut := [⟨64,183437180,183437293⟩]
theorem checked65856 : checkPrefixCuts (2^48) 8635809793 10 Manual.Count131072.C065856.packed 64 cuts65856 = true := by
 decide +kernel
def cuts65857 : List PrefixCut := [⟨31,90250858,90250911⟩,
⟨64,187084830,187084942⟩]
theorem checked65857 : checkPrefixCuts (2^48) 8635940865 10 Manual.Count131072.C065857.packed 64 cuts65857 = true := by
 decide +kernel
def pointBounds65857 : List (Nat × Nat × Nat) := [(8636004352,115064628141724,115065017209300)]
theorem point_links_checked65857 : (cuts65857.take 1).map (fun c => (8635940865-1+2*2^10*c.k,115064537890866+c.lower,115064926958389+c.upper)) = pointBounds65857 := by
 decide +kernel
def cuts65858 : List PrefixCut := [⟨64,187147192,187147298⟩]
theorem checked65858 : checkPrefixCuts (2^48) 8636071937 10 Manual.Count131072.C065858.packed 64 cuts65858 = true := by
 decide +kernel
def cuts65859 : List PrefixCut := [⟨35,101720566,101720626⟩,
⟨64,185742882,185742990⟩]
theorem checked65859 : checkPrefixCuts (2^48) 8636203009 10 Manual.Count131072.C065859.packed 64 cuts65859 = true := by
 decide +kernel
def pointBounds65859 : List (Nat × Nat × Nat) := [(8636274688,115065013843454,115065402911255)]
theorem point_links_checked65859 : (cuts65859.take 1).map (fun c => (8636203009-1+2*2^10*c.k,115064912122888+c.lower,115065301190629+c.upper)) = pointBounds65859 := by
 decide +kernel
def cuts65860 : List PrefixCut := [⟨64,187956295,187956396⟩]
theorem checked65860 : checkPrefixCuts (2^48) 8636334081 10 Manual.Count131072.C065860.packed 64 cuts65860 = true := by
 decide +kernel
def cuts65861 : List PrefixCut := [⟨39,111885925,111885994⟩,
⟨64,184042507,184042618⟩]
theorem checked65861 : checkPrefixCuts (2^48) 8636465153 10 Manual.Count131072.C065861.packed 64 cuts65861 = true := by
 decide +kernel
def pointBounds65861 : List (Nat × Nat × Nat) := [(8636545024,115065397707990,115065786776009)]
theorem point_links_checked65861 : (cuts65861.take 1).map (fun c => (8636465153-1+2*2^10*c.k,115065285822065+c.lower,115065674890015+c.upper)) = pointBounds65861 := by
 decide +kernel
def cuts65862 : List PrefixCut := [⟨64,187689865,187689972⟩]
theorem checked65862 : checkPrefixCuts (2^48) 8636596225 10 Manual.Count131072.C065862.packed 64 cuts65862 = true := by
 decide +kernel
def cuts65863 : List PrefixCut := [⟨43,126580693,126580764⟩,
⟨64,187980334,187980442⟩]
theorem checked65863 : checkPrefixCuts (2^48) 8636727297 10 Manual.Count131072.C065863.packed 64 cuts65863 = true := by
 decide +kernel
def pointBounds65863 : List (Nat × Nat × Nat) := [(8636815360,115065784135130,115066173203369)]
theorem point_links_checked65863 : (cuts65863.take 1).map (fun c => (8636727297-1+2*2^10*c.k,115065657554437+c.lower,115066046622605+c.upper)) = pointBounds65863 := by
 decide +kernel
def cuts65864 : List PrefixCut := [⟨64,186608726,186608832⟩]
theorem checked65864 : checkPrefixCuts (2^48) 8636858369 10 Manual.Count131072.C065864.packed 64 cuts65864 = true := by
 decide +kernel
def cuts65865 : List PrefixCut := [⟨47,137396442,137396525⟩,
⟨64,186442947,186443060⟩]
theorem checked65865 : checkPrefixCuts (2^48) 8636989441 10 Manual.Count131072.C065865.packed 64 cuts65865 = true := by
 decide +kernel
def pointBounds65865 : List (Nat × Nat × Nat) := [(8637085696,115066169539939,115066558608404)]
theorem point_links_checked65865 : (cuts65865.take 1).map (fun c => (8636989441-1+2*2^10*c.k,115066032143497+c.lower,115066421211879+c.upper)) = pointBounds65865 := by
 decide +kernel
def cuts65866 : List PrefixCut := [⟨64,183702656,183702760⟩]
theorem checked65866 : checkPrefixCuts (2^48) 8637120513 10 Manual.Count131072.C065866.packed 64 cuts65866 = true := by
 decide +kernel
def cuts65867 : List PrefixCut := [⟨51,150818573,150818653⟩,
⟨64,188816220,188816323⟩]
theorem checked65867 : checkPrefixCuts (2^48) 8637251585 10 Manual.Count131072.C065867.packed 64 cuts65867 = true := by
 decide +kernel
def pointBounds65867 : List (Nat × Nat × Nat) := [(8637356032,115066553107673,115066942176352)]
theorem point_links_checked65867 : (cuts65867.take 1).map (fun c => (8637251585-1+2*2^10*c.k,115066402289100+c.lower,115066791357699+c.upper)) = pointBounds65867 := by
 decide +kernel
def cuts65868 : List PrefixCut := [⟨64,187346908,187347022⟩]
theorem checked65868 : checkPrefixCuts (2^48) 8637382657 10 Manual.Count131072.C065868.packed 64 cuts65868 = true := by
 decide +kernel
def cuts65869 : List PrefixCut := [⟨55,162545345,162545441⟩,
⟨64,187702533,187702644⟩]
theorem checked65869 : checkPrefixCuts (2^48) 8637513729 10 Manual.Count131072.C065869.packed 64 cuts65869 = true := by
 decide +kernel
def pointBounds65869 : List (Nat × Nat × Nat) := [(8637626368,115066940997573,115067330066485)]
theorem point_links_checked65869 : (cuts65869.take 1).map (fun c => (8637513729-1+2*2^10*c.k,115066778452228+c.lower,115067167521044+c.upper)) = pointBounds65869 := by
 decide +kernel
def cuts65870 : List PrefixCut := [⟨64,185418606,185418717⟩]
theorem checked65870 : checkPrefixCuts (2^48) 8637644801 10 Manual.Count131072.C065870.packed 64 cuts65870 = true := by
 decide +kernel
def cuts65871 : List PrefixCut := [⟨59,171957769,171957870⟩,
⟨64,185611314,185611423⟩]
theorem checked65871 : checkPrefixCuts (2^48) 8637775873 10 Manual.Count131072.C065871.packed 64 cuts65871 = true := by
 decide +kernel
def pointBounds65871 : List (Nat × Nat × Nat) := [(8637896704,115067323531136,115067712600275)]
theorem point_links_checked65871 : (cuts65871.take 1).map (fun c => (8637775873-1+2*2^10*c.k,115067151573367+c.lower,115067540642405+c.upper)) = pointBounds65871 := by
 decide +kernel
def cuts65872 : List PrefixCut := [⟨64,186325368,186325475⟩]
theorem checked65872 : checkPrefixCuts (2^48) 8637906945 10 Manual.Count131072.C065872.packed 64 cuts65872 = true := by
 decide +kernel
def cuts65873 : List PrefixCut := [⟨63,185345019,185345123⟩,
⟨64,188342841,188342947⟩]
theorem checked65873 : checkPrefixCuts (2^48) 8638038017 10 Manual.Count131072.C065873.packed 64 cuts65873 = true := by
 decide +kernel
def pointBounds65873 : List (Nat × Nat × Nat) := [(8638167040,115067708855068,115068097924426)]
theorem point_links_checked65873 : (cuts65873.take 1).map (fun c => (8638038017-1+2*2^10*c.k,115067523510049+c.lower,115067912579303+c.upper)) = pointBounds65873 := by
 decide +kernel
def cuts65874 : List PrefixCut := [⟨64,187460190,187460290⟩]
theorem checked65874 : checkPrefixCuts (2^48) 8638169089 10 Manual.Count131072.C065874.packed 64 cuts65874 = true := by
 decide +kernel
def cuts65875 : List PrefixCut := [⟨64,187685432,187685537⟩]
theorem checked65875 : checkPrefixCuts (2^48) 8638300161 10 Manual.Count131072.C065875.packed 64 cuts65875 = true := by
 decide +kernel
def cuts65876 : List PrefixCut := [⟨3,9286445,9286450⟩,
⟨64,186444393,186444504⟩]
theorem checked65876 : checkPrefixCuts (2^48) 8638431233 10 Manual.Count131072.C065876.packed 64 cuts65876 = true := by
 decide +kernel
def pointBounds65876 : List (Nat × Nat × Nat) := [(8638437376,115068096284957,115068485354527)]
theorem point_links_checked65876 : (cuts65876.take 1).map (fun c => (8638431233-1+2*2^10*c.k,115068086998512+c.lower,115068476068077+c.upper)) = pointBounds65876 := by
 decide +kernel
def cuts65877 : List PrefixCut := [⟨64,187744894,187745001⟩]
theorem checked65877 : checkPrefixCuts (2^48) 8638562305 10 Manual.Count131072.C065877.packed 64 cuts65877 = true := by
 decide +kernel
def cuts65878 : List PrefixCut := [⟨7,20787964,20787975⟩,
⟨64,187351066,187351176⟩]
theorem checked65878 : checkPrefixCuts (2^48) 8638693377 10 Manual.Count131072.C065878.packed 64 cuts65878 = true := by
 decide +kernel
def pointBounds65878 : List (Nat × Nat × Nat) := [(8638707712,115068481975763,115068871045557)]
theorem point_links_checked65878 : (cuts65878.take 1).map (fun c => (8638693377-1+2*2^10*c.k,115068461187799+c.lower,115068850257582+c.upper)) = pointBounds65878 := by
 decide +kernel
def cuts65879 : List PrefixCut := [⟨64,188195366,188195477⟩]
theorem checked65879 : checkPrefixCuts (2^48) 8638824449 10 Manual.Count131072.C065879.packed 64 cuts65879 = true := by
 decide +kernel
def cuts65880 : List PrefixCut := [⟨11,31376474,31376492⟩,
⟨64,186302754,186302862⟩]
theorem checked65880 : checkPrefixCuts (2^48) 8638955521 10 Manual.Count131072.C065880.packed 64 cuts65880 = true := by
 decide +kernel
def pointBounds65880 : List (Nat × Nat × Nat) := [(8638978048,115068868110705,115069257180727)]
theorem point_links_checked65880 : (cuts65880.take 1).map (fun c => (8638955521-1+2*2^10*c.k,115068836734231+c.lower,115069225804235+c.upper)) = pointBounds65880 := by
 decide +kernel
def cuts65881 : List PrefixCut := [⟨64,184182148,184182254⟩]
theorem checked65881 : checkPrefixCuts (2^48) 8639086593 10 Manual.Count131072.C065881.packed 64 cuts65881 = true := by
 decide +kernel
def cuts65882 : List PrefixCut := [⟨15,42550790,42550816⟩,
⟨64,184016447,184016544⟩]
theorem checked65882 : checkPrefixCuts (2^48) 8639217665 10 Manual.Count131072.C065882.packed 64 cuts65882 = true := by
 decide +kernel
def pointBounds65882 : List (Nat × Nat × Nat) := [(8639248384,115069249769923,115069638840167)]
theorem point_links_checked65882 : (cuts65882.take 1).map (fun c => (8639217665-1+2*2^10*c.k,115069207219133+c.lower,115069596289351+c.upper)) = pointBounds65882 := by
 decide +kernel
def cuts65883 : List PrefixCut := [⟨64,187108792,187108894⟩]
theorem checked65883 : checkPrefixCuts (2^48) 8639348737 10 Manual.Count131072.C065883.packed 64 cuts65883 = true := by
 decide +kernel
def cuts65884 : List PrefixCut := [⟨19,55972444,55972475⟩,
⟨64,186682409,186682517⟩]
theorem checked65884 : checkPrefixCuts (2^48) 8639479809 10 Manual.Count131072.C065884.packed 64 cuts65884 = true := by
 decide +kernel
def pointBounds65884 : List (Nat × Nat × Nat) := [(8639518720,115069634316816,115070023387264)]
theorem point_links_checked65884 : (cuts65884.take 1).map (fun c => (8639479809-1+2*2^10*c.k,115069578344372+c.lower,115069967414789+c.upper)) = pointBounds65884 := by
 decide +kernel
def cuts65885 : List PrefixCut := [⟨64,186451531,186451636⟩]
theorem checked65885 : checkPrefixCuts (2^48) 8639610881 10 Manual.Count131072.C065885.packed 64 cuts65885 = true := by
 decide +kernel
def cuts65886 : List PrefixCut := [⟨23,65027677,65027717⟩,
⟨64,188664044,188664155⟩]
theorem checked65886 : checkPrefixCuts (2^48) 8639741953 10 Manual.Count131072.C065886.packed 64 cuts65886 = true := by
 decide +kernel
def pointBounds65886 : List (Nat × Nat × Nat) := [(8639789056,115070016505989,115070405576659)]
theorem point_links_checked65886 : (cuts65886.take 1).map (fun c => (8639741953-1+2*2^10*c.k,115069951478312+c.lower,115070340548942+c.upper)) = pointBounds65886 := by
 decide +kernel
def cuts65887 : List PrefixCut := [⟨64,187097429,187097540⟩]
theorem checked65887 : checkPrefixCuts (2^48) 8639873025 10 Manual.Count131072.C065887.packed 64 cuts65887 = true := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S7.B000183
