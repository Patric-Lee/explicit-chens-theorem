import PlattAssemblyKernel
import PlattCertificates.Count131072.C069888
import PlattCertificates.Count131072.C069889
import PlattCertificates.Count131072.C069890
import PlattCertificates.Count131072.C069891
import PlattCertificates.Count131072.C069892
import PlattCertificates.Count131072.C069893
import PlattCertificates.Count131072.C069894
import PlattCertificates.Count131072.C069895
import PlattCertificates.Count131072.C069896
import PlattCertificates.Count131072.C069897
import PlattCertificates.Count131072.C069898
import PlattCertificates.Count131072.C069899
import PlattCertificates.Count131072.C069900
import PlattCertificates.Count131072.C069901
import PlattCertificates.Count131072.C069902
import PlattCertificates.Count131072.C069903
import PlattCertificates.Count131072.C069904
import PlattCertificates.Count131072.C069905
import PlattCertificates.Count131072.C069906
import PlattCertificates.Count131072.C069907
import PlattCertificates.Count131072.C069908
import PlattCertificates.Count131072.C069909
import PlattCertificates.Count131072.C069910
import PlattCertificates.Count131072.C069911
import PlattCertificates.Count131072.C069912
import PlattCertificates.Count131072.C069913
import PlattCertificates.Count131072.C069914
import PlattCertificates.Count131072.C069915
import PlattCertificates.Count131072.C069916
import PlattCertificates.Count131072.C069917
import PlattCertificates.Count131072.C069918
import PlattCertificates.Count131072.C069919
namespace ChenEffective.PlattWindow.Assembly.Prefix.S7.B000309
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts69888 : List PrefixCut := [⟨64,174732456,174732562⟩]
theorem checked69888 : checkPrefixCuts (2^48) 9164292097 10 Manual.Count131072.C069888.packed 64 cuts69888 = true := by
 decide +kernel
def cuts69889 : List PrefixCut := [⟨62,169324372,169324474⟩,
⟨64,174852791,174852895⟩]
theorem checked69889 : checkPrefixCuts (2^48) 9164423169 10 Manual.Count131072.C069889.packed 64 cuts69889 = true := by
 decide +kernel
def pointBounds69889 : List (Nat × Nat × Nat) := [(9164550144,115794441742044,115794831235925)]
theorem point_links_checked69889 : (cuts69889.take 1).map (fun c => (9164423169-1+2*2^10*c.k,115794272417672+c.lower,115794661911451+c.upper)) = pointBounds69889 := by
 decide +kernel
def cuts69890 : List PrefixCut := [⟨64,175188148,175188261⟩]
theorem checked69890 : checkPrefixCuts (2^48) 9164554241 10 Manual.Count131072.C069890.packed 64 cuts69890 = true := by
 decide +kernel
def cuts69891 : List PrefixCut := [⟨64,173158591,173158700⟩]
theorem checked69891 : checkPrefixCuts (2^48) 9164685313 10 Manual.Count131072.C069891.packed 64 cuts69891 = true := by
 decide +kernel
def cuts69892 : List PrefixCut := [⟨10,27364852,27364869⟩,
⟨64,177056593,177056697⟩]
theorem checked69892 : checkPrefixCuts (2^48) 9164816385 10 Manual.Count131072.C069892.packed 64 cuts69892 = true := by
 decide +kernel
def pointBounds69892 : List (Nat × Nat × Nat) := [(9164836864,115794822982054,115795212476176)]
theorem point_links_checked69892 : (cuts69892.take 1).map (fun c => (9164816385-1+2*2^10*c.k,115794795617202+c.lower,115795185111307+c.upper)) = pointBounds69892 := by
 decide +kernel
def cuts69893 : List PrefixCut := [⟨64,176071288,176071389⟩]
theorem checked69893 : checkPrefixCuts (2^48) 9164947457 10 Manual.Count131072.C069893.packed 64 cuts69893 = true := by
 decide +kernel
def cuts69894 : List PrefixCut := [⟨22,60501847,60501886⟩,
⟨64,176621561,176621671⟩]
theorem checked69894 : checkPrefixCuts (2^48) 9165078529 10 Manual.Count131072.C069894.packed 64 cuts69894 = true := by
 decide +kernel
def pointBounds69894 : List (Nat × Nat × Nat) := [(9165123584,115795209246930,115795598741279)]
theorem point_links_checked69894 : (cuts69894.take 1).map (fun c => (9165078529-1+2*2^10*c.k,115795148745083+c.lower,115795538239393+c.upper)) = pointBounds69894 := by
 decide +kernel
def cuts69895 : List PrefixCut := [⟨64,177018298,177018400⟩]
theorem checked69895 : checkPrefixCuts (2^48) 9165209601 10 Manual.Count131072.C069895.packed 64 cuts69895 = true := by
 decide +kernel
def cuts69896 : List PrefixCut := [⟨34,93698281,93698335⟩,
⟨64,175971599,175971701⟩]
theorem checked69896 : checkPrefixCuts (2^48) 9165340673 10 Manual.Count131072.C069896.packed 64 cuts69896 = true := by
 decide +kernel
def pointBounds69896 : List (Nat × Nat × Nat) := [(9165410304,115795596083223,115795985577799)]
theorem point_links_checked69896 : (cuts69896.take 1).map (fun c => (9165340673-1+2*2^10*c.k,115795502384942+c.lower,115795891879464+c.upper)) = pointBounds69896 := by
 decide +kernel
def cuts69897 : List PrefixCut := [⟨64,176798250,176798353⟩]
theorem checked69897 : checkPrefixCuts (2^48) 9165471745 10 Manual.Count131072.C069897.packed 64 cuts69897 = true := by
 decide +kernel
def cuts69898 : List PrefixCut := [⟨46,124865876,124865955⟩,
⟨64,173571204,173571312⟩]
theorem checked69898 : checkPrefixCuts (2^48) 9165602817 10 Manual.Count131072.C069898.packed 64 cuts69898 = true := by
 decide +kernel
def pointBounds69898 : List (Nat × Nat × Nat) := [(9165697024,115795980020667,115796369515473)]
theorem point_links_checked69898 : (cuts69898.take 1).map (fun c => (9165602817-1+2*2^10*c.k,115795855154791+c.lower,115796244649518+c.upper)) = pointBounds69898 := by
 decide +kernel
def cuts69899 : List PrefixCut := [⟨64,175779779,175779879⟩]
theorem checked69899 : checkPrefixCuts (2^48) 9165733889 10 Manual.Count131072.C069899.packed 64 cuts69899 = true := by
 decide +kernel
def cuts69900 : List PrefixCut := [⟨58,156522951,156523042⟩,
⟨64,172921353,172921454⟩]
theorem checked69900 : checkPrefixCuts (2^48) 9165864961 10 Manual.Count131072.C069900.packed 64 cuts69900 = true := by
 decide +kernel
def pointBounds69900 : List (Nat × Nat × Nat) := [(9165983744,115796361028725,115796750523751)]
theorem point_links_checked69900 : (cuts69900.take 1).map (fun c => (9165864961-1+2*2^10*c.k,115796204505774+c.lower,115796594000709+c.upper)) = pointBounds69900 := by
 decide +kernel
def cuts69901 : List PrefixCut := [⟨64,178047183,178047290⟩]
theorem checked69901 : checkPrefixCuts (2^48) 9165996033 10 Manual.Count131072.C069901.packed 64 cuts69901 = true := by
 decide +kernel
def cuts69902 : List PrefixCut := [⟨64,172916408,172916514⟩]
theorem checked69902 : checkPrefixCuts (2^48) 9166127105 10 Manual.Count131072.C069902.packed 64 cuts69902 = true := by
 decide +kernel
def cuts69903 : List PrefixCut := [⟨6,16490035,16490044⟩,
⟨64,172821813,172821919⟩]
theorem checked69903 : checkPrefixCuts (2^48) 9166258177 10 Manual.Count131072.C069903.packed 64 cuts69903 = true := by
 decide +kernel
def pointBounds69903 : List (Nat × Nat × Nat) := [(9166270464,115796744880753,115797134376011)]
theorem point_links_checked69903 : (cuts69903.take 1).map (fun c => (9166258177-1+2*2^10*c.k,115796728390718+c.lower,115797117885967+c.upper)) = pointBounds69903 := by
 decide +kernel
def cuts69904 : List PrefixCut := [⟨64,179114288,179114395⟩]
theorem checked69904 : checkPrefixCuts (2^48) 9166389249 10 Manual.Count131072.C069904.packed 64 cuts69904 = true := by
 decide +kernel
def cuts69905 : List PrefixCut := [⟨18,49560743,49560771⟩,
⟨64,176501668,176501771⟩]
theorem checked69905 : checkPrefixCuts (2^48) 9166520321 10 Manual.Count131072.C069905.packed 64 cuts69905 = true := by
 decide +kernel
def pointBounds69905 : List (Nat × Nat × Nat) := [(9166557184,115797129887562,115797519383052)]
theorem point_links_checked69905 : (cuts69905.take 1).map (fun c => (9166520321-1+2*2^10*c.k,115797080326819+c.lower,115797469822281+c.upper)) = pointBounds69905 := by
 decide +kernel
def cuts69906 : List PrefixCut := [⟨64,171831799,171831902⟩]
theorem checked69906 : checkPrefixCuts (2^48) 9166651393 10 Manual.Count131072.C069906.packed 64 cuts69906 = true := by
 decide +kernel
def cuts69907 : List PrefixCut := [⟨30,83243594,83243642⟩,
⟨64,176588739,176588846⟩]
theorem checked69907 : checkPrefixCuts (2^48) 9166782465 10 Manual.Count131072.C069907.packed 64 cuts69907 = true := by
 decide +kernel
def pointBounds69907 : List (Nat × Nat × Nat) := [(9166843904,115797511903880,115797901399596)]
theorem point_links_checked69907 : (cuts69907.take 1).map (fun c => (9166782465-1+2*2^10*c.k,115797428660286+c.lower,115797818155954+c.upper)) = pointBounds69907 := by
 decide +kernel
def cuts69908 : List PrefixCut := [⟨64,174590377,174590476⟩]
theorem checked69908 : checkPrefixCuts (2^48) 9166913537 10 Manual.Count131072.C069908.packed 64 cuts69908 = true := by
 decide +kernel
def cuts69909 : List PrefixCut := [⟨42,113853934,113853997⟩,
⟨64,175754656,175754753⟩]
theorem checked69909 : checkPrefixCuts (2^48) 9167044609 10 Manual.Count131072.C069909.packed 64 cuts69909 = true := by
 decide +kernel
def pointBounds69909 : List (Nat × Nat × Nat) := [(9167130624,115797893693336,115798283189273)]
theorem point_links_checked69909 : (cuts69909.take 1).map (fun c => (9167044609-1+2*2^10*c.k,115797779839402+c.lower,115798169335276+c.upper)) = pointBounds69909 := by
 decide +kernel
def cuts69910 : List PrefixCut := [⟨64,176489043,176489143⟩]
theorem checked69910 : checkPrefixCuts (2^48) 9167175681 10 Manual.Count131072.C069910.packed 64 cuts69910 = true := by
 decide +kernel
def cuts69911 : List PrefixCut := [⟨54,146427481,146427569⟩,
⟨64,173293309,173293412⟩]
theorem checked69911 : checkPrefixCuts (2^48) 9167306753 10 Manual.Count131072.C069911.packed 64 cuts69911 = true := by
 decide +kernel
def pointBounds69911 : List (Nat × Nat × Nat) := [(9167417344,115798278510582,115798668006741)]
theorem point_links_checked69911 : (cuts69911.take 1).map (fun c => (9167306753-1+2*2^10*c.k,115798132083101+c.lower,115798521579172+c.upper)) = pointBounds69911 := by
 decide +kernel
def cuts69912 : List PrefixCut := [⟨64,172400431,172400535⟩]
theorem checked69912 : checkPrefixCuts (2^48) 9167437825 10 Manual.Count131072.C069912.packed 64 cuts69912 = true := by
 decide +kernel
def cuts69913 : List PrefixCut := [⟨64,176696397,176696496⟩]
theorem checked69913 : checkPrefixCuts (2^48) 9167568897 10 Manual.Count131072.C069913.packed 64 cuts69913 = true := by
 decide +kernel
def cuts69914 : List PrefixCut := [⟨2,5465113,5465117⟩,
⟨64,176571060,176571168⟩]
theorem checked69914 : checkPrefixCuts (2^48) 9167699969 10 Manual.Count131072.C069914.packed 64 cuts69914 = true := by
 decide +kernel
def pointBounds69914 : List (Nat × Nat × Nat) := [(9167704064,115798659938351,115799049434732)]
theorem point_links_checked69914 : (cuts69914.take 1).map (fun c => (9167699969-1+2*2^10*c.k,115798654473238+c.lower,115799043969615+c.upper)) = pointBounds69914 := by
 decide +kernel
def cuts69915 : List PrefixCut := [⟨64,174327274,174327375⟩]
theorem checked69915 : checkPrefixCuts (2^48) 9167831041 10 Manual.Count131072.C069915.packed 64 cuts69915 = true := by
 decide +kernel
def cuts69916 : List PrefixCut := [⟨14,38930090,38930115⟩,
⟨64,174693203,174693308⟩]
theorem checked69916 : checkPrefixCuts (2^48) 9167962113 10 Manual.Count131072.C069916.packed 64 cuts69916 = true := by
 decide +kernel
def pointBounds69916 : List (Nat × Nat × Nat) := [(9167990784,115799044301662,115799433798273)]
theorem point_links_checked69916 : (cuts69916.take 1).map (fun c => (9167962113-1+2*2^10*c.k,115799005371572+c.lower,115799394868158+c.upper)) = pointBounds69916 := by
 decide +kernel
def cuts69917 : List PrefixCut := [⟨64,175181945,175182044⟩]
theorem checked69917 : checkPrefixCuts (2^48) 9168093185 10 Manual.Count131072.C069917.packed 64 cuts69917 = true := by
 decide +kernel
def cuts69918 : List PrefixCut := [⟨26,71042220,71042260⟩,
⟨64,176775868,176775972⟩]
theorem checked69918 : checkPrefixCuts (2^48) 9168224257 10 Manual.Count131072.C069918.packed 64 cuts69918 = true := by
 decide +kernel
def pointBounds69918 : List (Nat × Nat × Nat) := [(9168277504,115799426288940,115799815785770)]
theorem point_links_checked69918 : (cuts69918.take 1).map (fun c => (9168224257-1+2*2^10*c.k,115799355246720+c.lower,115799744743510+c.upper)) = pointBounds69918 := by
 decide +kernel
def cuts69919 : List PrefixCut := [⟨64,175238313,175238414⟩]
theorem checked69919 : checkPrefixCuts (2^48) 9168355329 10 Manual.Count131072.C069919.packed 64 cuts69919 = true := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S7.B000309
