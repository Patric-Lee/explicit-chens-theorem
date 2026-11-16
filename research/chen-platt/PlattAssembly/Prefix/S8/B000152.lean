import PlattAssemblyKernel
import PlattCertificates.Count131072.C074864
import PlattCertificates.Count131072.C074865
import PlattCertificates.Count131072.C074866
import PlattCertificates.Count131072.C074867
import PlattCertificates.Count131072.C074868
import PlattCertificates.Count131072.C074869
import PlattCertificates.Count131072.C074870
import PlattCertificates.Count131072.C074871
import PlattCertificates.Count131072.C074872
import PlattCertificates.Count131072.C074873
import PlattCertificates.Count131072.C074874
import PlattCertificates.Count131072.C074875
import PlattCertificates.Count131072.C074876
import PlattCertificates.Count131072.C074877
import PlattCertificates.Count131072.C074878
import PlattCertificates.Count131072.C074879
import PlattCertificates.Count131072.C074880
import PlattCertificates.Count131072.C074881
import PlattCertificates.Count131072.C074882
import PlattCertificates.Count131072.C074883
import PlattCertificates.Count131072.C074884
import PlattCertificates.Count131072.C074885
import PlattCertificates.Count131072.C074886
import PlattCertificates.Count131072.C074887
import PlattCertificates.Count131072.C074888
import PlattCertificates.Count131072.C074889
import PlattCertificates.Count131072.C074890
import PlattCertificates.Count131072.C074891
import PlattCertificates.Count131072.C074892
import PlattCertificates.Count131072.C074893
import PlattCertificates.Count131072.C074894
import PlattCertificates.Count131072.C074895
namespace ChenEffective.PlattWindow.Assembly.Prefix.S8.B000152
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts74864 : List PrefixCut := [⟨64,162119636,162119732⟩]
theorem checked74864 : checkPrefixCuts (2^48) 9816506369 10 Manual.Count131072.C074864.packed 64 cuts74864 = true := by
 decide +kernel
def cuts74865 : List PrefixCut := [⟨1,2408553,2408554⟩,
⟨64,163321746,163321841⟩]
theorem checked74865 : checkPrefixCuts (2^48) 9816637441 10 Manual.Count131072.C074865.packed 64 cuts74865 = true := by
 decide +kernel
def pointBounds74865 : List (Nat × Nat × Nat) := [(9816639488,116636697334590,116637087328752)]
theorem point_links_checked74865 : (cuts74865.take 1).map (fun c => (9816637441-1+2*2^10*c.k,116636694926037+c.lower,116637084920198+c.upper)) = pointBounds74865 := by
 decide +kernel
def cuts74866 : List PrefixCut := [⟨64,161799908,161800007⟩]
theorem checked74866 : checkPrefixCuts (2^48) 9816768513 10 Manual.Count131072.C074866.packed 64 cuts74866 = true := by
 decide +kernel
def cuts74867 : List PrefixCut := [⟨23,59638626,59638663⟩,
⟨64,166299302,166299400⟩]
theorem checked74867 : checkPrefixCuts (2^48) 9816899585 10 Manual.Count131072.C074867.packed 64 cuts74867 = true := by
 decide +kernel
def pointBounds74867 : List (Nat × Nat × Nat) := [(9816946688,116637079686317,116637469680709)]
theorem point_links_checked74867 : (cuts74867.take 1).map (fun c => (9816899585-1+2*2^10*c.k,116637020047691+c.lower,116637410042046+c.upper)) = pointBounds74867 := by
 decide +kernel
def cuts74868 : List PrefixCut := [⟨64,164720121,164720217⟩]
theorem checked74868 : checkPrefixCuts (2^48) 9817030657 10 Manual.Count131072.C074868.packed 64 cuts74868 = true := by
 decide +kernel
def cuts74869 : List PrefixCut := [⟨45,113740170,113740240⟩,
⟨64,163198322,163198421⟩]
theorem checked74869 : checkPrefixCuts (2^48) 9817161729 10 Manual.Count131072.C074869.packed 64 cuts74869 = true := by
 decide +kernel
def pointBounds74869 : List (Nat × Nat × Nat) := [(9817253888,116637464807284,116637854801903)]
theorem point_links_checked74869 : (cuts74869.take 1).map (fun c => (9817161729-1+2*2^10*c.k,116637351067114+c.lower,116637741061663+c.upper)) = pointBounds74869 := by
 decide +kernel
def cuts74870 : List PrefixCut := [⟨64,163224818,163224914⟩]
theorem checked74870 : checkPrefixCuts (2^48) 9817292801 10 Manual.Count131072.C074870.packed 64 cuts74870 = true := by
 decide +kernel
def cuts74871 : List PrefixCut := [⟨64,164684843,164684938⟩]
theorem checked74871 : checkPrefixCuts (2^48) 9817423873 10 Manual.Count131072.C074871.packed 64 cuts74871 = true := by
 decide +kernel
def cuts74872 : List PrefixCut := [⟨3,7081628,7081634⟩,
⟨64,161299555,161299644⟩]
theorem checked74872 : checkPrefixCuts (2^48) 9817554945 10 Manual.Count131072.C074872.packed 64 cuts74872 = true := by
 decide +kernel
def pointBounds74872 : List (Nat × Nat × Nat) := [(9817561088,116637849256725,116638239251570)]
theorem point_links_checked74872 : (cuts74872.take 1).map (fun c => (9817554945-1+2*2^10*c.k,116637842175097+c.lower,116638232169936+c.upper)) = pointBounds74872 := by
 decide +kernel
def cuts74873 : List PrefixCut := [⟨64,163361621,163361718⟩]
theorem checked74873 : checkPrefixCuts (2^48) 9817686017 10 Manual.Count131072.C074873.packed 64 cuts74873 = true := by
 decide +kernel
def cuts74874 : List PrefixCut := [⟨25,64162857,64162895⟩,
⟨64,165366327,165366421⟩]
theorem checked74874 : checkPrefixCuts (2^48) 9817817089 10 Manual.Count131072.C074874.packed 64 cuts74874 = true := by
 decide +kernel
def pointBounds74874 : List (Nat × Nat × Nat) := [(9817868288,116638230999130,116638620994193)]
theorem point_links_checked74874 : (cuts74874.take 1).map (fun c => (9817817089-1+2*2^10*c.k,116638166836273+c.lower,116638556831298+c.upper)) = pointBounds74874 := by
 decide +kernel
def cuts74875 : List PrefixCut := [⟨64,164160013,164160108⟩]
theorem checked74875 : checkPrefixCuts (2^48) 9817948161 10 Manual.Count131072.C074875.packed 64 cuts74875 = true := by
 decide +kernel
def cuts74876 : List PrefixCut := [⟨47,119262618,119262690⟩,
⟨64,162753044,162753145⟩]
theorem checked74876 : checkPrefixCuts (2^48) 9818079233 10 Manual.Count131072.C074876.packed 64 cuts74876 = true := by
 decide +kernel
def pointBounds74876 : List (Nat × Nat × Nat) := [(9818175488,116638615625231,116639005620517)]
theorem point_links_checked74876 : (cuts74876.take 1).map (fun c => (9818079233-1+2*2^10*c.k,116638496362613+c.lower,116638886357827+c.upper)) = pointBounds74876 := by
 decide +kernel
def cuts74877 : List PrefixCut := [⟨64,163496249,163496343⟩]
theorem checked74877 : checkPrefixCuts (2^48) 9818210305 10 Manual.Count131072.C074877.packed 64 cuts74877 = true := by
 decide +kernel
def cuts74878 : List PrefixCut := [⟨64,163494080,163494171⟩]
theorem checked74878 : checkPrefixCuts (2^48) 9818341377 10 Manual.Count131072.C074878.packed 64 cuts74878 = true := by
 decide +kernel
def cuts74879 : List PrefixCut := [⟨5,12957880,12957888⟩,
⟨64,162947198,162947294⟩]
theorem checked74879 : checkPrefixCuts (2^48) 9818472449 10 Manual.Count131072.C074879.packed 64 cuts74879 = true := by
 decide +kernel
def pointBounds74879 : List (Nat × Nat × Nat) := [(9818482688,116638999063866,116639389059374)]
theorem point_links_checked74879 : (cuts74879.take 1).map (fun c => (9818472449-1+2*2^10*c.k,116638986105986+c.lower,116639376101486+c.upper)) = pointBounds74879 := by
 decide +kernel
def cuts74880 : List PrefixCut := [⟨64,161224976,161225082⟩]
theorem checked74880 : checkPrefixCuts (2^48) 9818603521 10 Manual.Count131072.C074880.packed 64 cuts74880 = true := by
 decide +kernel
def cuts74881 : List PrefixCut := [⟨27,68313567,68313606⟩,
⟨64,161853512,161853607⟩]
theorem checked74881 : checkPrefixCuts (2^48) 9818734593 10 Manual.Count131072.C074881.packed 64 cuts74881 = true := by
 decide +kernel
def pointBounds74881 : List (Nat × Nat × Nat) := [(9818789888,116639378591727,116639768587468)]
theorem point_links_checked74881 : (cuts74881.take 1).map (fun c => (9818734593-1+2*2^10*c.k,116639310278160+c.lower,116639700273862+c.upper)) = pointBounds74881 := by
 decide +kernel
def cuts74882 : List PrefixCut := [⟨64,162826007,162826108⟩]
theorem checked74882 : checkPrefixCuts (2^48) 9818865665 10 Manual.Count131072.C074882.packed 64 cuts74882 = true := by
 decide +kernel
def cuts74883 : List PrefixCut := [⟨49,124583364,124583433⟩,
⟨64,162651841,162651934⟩]
theorem checked74883 : checkPrefixCuts (2^48) 9818996737 10 Manual.Count131072.C074883.packed 64 cuts74883 = true := by
 decide +kernel
def pointBounds74883 : List (Nat × Nat × Nat) := [(9819097088,116639759541043,116640149537010)]
theorem point_links_checked74883 : (cuts74883.take 1).map (fun c => (9818996737-1+2*2^10*c.k,116639634957679+c.lower,116640024953577+c.upper)) = pointBounds74883 := by
 decide +kernel
def cuts74884 : List PrefixCut := [⟨64,160413739,160413829⟩]
theorem checked74884 : checkPrefixCuts (2^48) 9819127809 10 Manual.Count131072.C074884.packed 64 cuts74884 = true := by
 decide +kernel
def cuts74885 : List PrefixCut := [⟨64,163880101,163880200⟩]
theorem checked74885 : checkPrefixCuts (2^48) 9819258881 10 Manual.Count131072.C074885.packed 64 cuts74885 = true := by
 decide +kernel
def cuts74886 : List PrefixCut := [⟨7,17113119,17113129⟩,
⟨64,163218627,163218725⟩]
theorem checked74886 : checkPrefixCuts (2^48) 9819389953 10 Manual.Count131072.C074886.packed 64 cuts74886 = true := by
 decide +kernel
def pointBounds74886 : List (Nat × Nat × Nat) := [(9819404288,116640139016479,116640529012669)]
theorem point_links_checked74886 : (cuts74886.take 1).map (fun c => (9819389953-1+2*2^10*c.k,116640121903360+c.lower,116640511899540+c.upper)) = pointBounds74886 := by
 decide +kernel
def cuts74887 : List PrefixCut := [⟨64,159891350,159891443⟩]
theorem checked74887 : checkPrefixCuts (2^48) 9819521025 10 Manual.Count131072.C074887.packed 64 cuts74887 = true := by
 decide +kernel
def cuts74888 : List PrefixCut := [⟨29,74584663,74584707⟩,
⟨64,165134769,165134867⟩]
theorem checked74888 : checkPrefixCuts (2^48) 9819652097 10 Manual.Count131072.C074888.packed 64 cuts74888 = true := by
 decide +kernel
def pointBounds74888 : List (Nat × Nat × Nat) := [(9819711488,116640519598000,116640909594415)]
theorem point_links_checked74888 : (cuts74888.take 1).map (fun c => (9819652097-1+2*2^10*c.k,116640445013337+c.lower,116640835009708+c.upper)) = pointBounds74888 := by
 decide +kernel
def cuts74889 : List PrefixCut := [⟨64,164444642,164444739⟩]
theorem checked74889 : checkPrefixCuts (2^48) 9819783169 10 Manual.Count131072.C074889.packed 64 cuts74889 = true := by
 decide +kernel
def cuts74890 : List PrefixCut := [⟨51,128727916,128727996⟩,
⟨64,161805406,161805507⟩]
theorem checked74890 : checkPrefixCuts (2^48) 9819914241 10 Manual.Count131072.C074890.packed 64 cuts74890 = true := by
 decide +kernel
def pointBounds74890 : List (Nat × Nat × Nat) := [(9820018688,116640903320664,116641293317310)]
theorem point_links_checked74890 : (cuts74890.take 1).map (fun c => (9819914241-1+2*2^10*c.k,116640774592748+c.lower,116641164589314+c.upper)) = pointBounds74890 := by
 decide +kernel
def cuts74891 : List PrefixCut := [⟨64,161344636,161344733⟩]
theorem checked74891 : checkPrefixCuts (2^48) 9820045313 10 Manual.Count131072.C074891.packed 64 cuts74891 = true := by
 decide +kernel
def cuts74892 : List PrefixCut := [⟨64,164323412,164323508⟩]
theorem checked74892 : checkPrefixCuts (2^48) 9820176385 10 Manual.Count131072.C074892.packed 64 cuts74892 = true := by
 decide +kernel
def cuts74893 : List PrefixCut := [⟨9,22643379,22643397⟩,
⟨64,163432669,163432775⟩]
theorem checked74893 : checkPrefixCuts (2^48) 9820307457 10 Manual.Count131072.C074893.packed 64 cuts74893 = true := by
 decide +kernel
def pointBounds74893 : List (Nat × Nat × Nat) := [(9820325888,116641284709581,116641674706459)]
theorem point_links_checked74893 : (cuts74893.take 1).map (fun c => (9820307457-1+2*2^10*c.k,116641262066202+c.lower,116641652063062+c.upper)) = pointBounds74893 := by
 decide +kernel
def cuts74894 : List PrefixCut := [⟨64,163545155,163545251⟩]
theorem checked74894 : checkPrefixCuts (2^48) 9820438529 10 Manual.Count131072.C074894.packed 64 cuts74894 = true := by
 decide +kernel
def cuts74895 : List PrefixCut := [⟨31,79507490,79507538⟩,
⟨64,164001551,164001648⟩]
theorem checked74895 : checkPrefixCuts (2^48) 9820569601 10 Manual.Count131072.C074895.packed 64 cuts74895 = true := by
 decide +kernel
def pointBounds74895 : List (Nat × Nat × Nat) := [(9820633088,116641668551516,116642058548626)]
theorem point_links_checked74895 : (cuts74895.take 1).map (fun c => (9820569601-1+2*2^10*c.k,116641589044026+c.lower,116641979041088+c.upper)) = pointBounds74895 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S8.B000152
