import PlattAssemblyKernel
import PlattCertificates.Count131072.C068960
import PlattCertificates.Count131072.C068961
import PlattCertificates.Count131072.C068962
import PlattCertificates.Count131072.C068963
import PlattCertificates.Count131072.C068964
import PlattCertificates.Count131072.C068965
import PlattCertificates.Count131072.C068966
import PlattCertificates.Count131072.C068967
import PlattCertificates.Count131072.C068968
import PlattCertificates.Count131072.C068969
import PlattCertificates.Count131072.C068970
import PlattCertificates.Count131072.C068971
import PlattCertificates.Count131072.C068972
import PlattCertificates.Count131072.C068973
import PlattCertificates.Count131072.C068974
import PlattCertificates.Count131072.C068975
import PlattCertificates.Count131072.C068976
import PlattCertificates.Count131072.C068977
import PlattCertificates.Count131072.C068978
import PlattCertificates.Count131072.C068979
import PlattCertificates.Count131072.C068980
import PlattCertificates.Count131072.C068981
import PlattCertificates.Count131072.C068982
import PlattCertificates.Count131072.C068983
import PlattCertificates.Count131072.C068984
import PlattCertificates.Count131072.C068985
import PlattCertificates.Count131072.C068986
import PlattCertificates.Count131072.C068987
import PlattCertificates.Count131072.C068988
import PlattCertificates.Count131072.C068989
import PlattCertificates.Count131072.C068990
import PlattCertificates.Count131072.C068991
namespace ChenEffective.PlattWindow.Assembly.Prefix.S7.B000280
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts68960 : List PrefixCut := [⟨64,178919305,178919412⟩]
theorem checked68960 : checkPrefixCuts (2^48) 9042657281 10 Manual.Count131072.C068960.packed 64 cuts68960 = true := by
 decide +kernel
def cuts68961 : List PrefixCut := [⟨53,147354359,147354441⟩,
⟨64,176800111,176800213⟩]
theorem checked68961 : checkPrefixCuts (2^48) 9042788353 10 Manual.Count131072.C068961.packed 64 cuts68961 = true := by
 decide +kernel
def pointBounds68961 : List (Nat × Nat × Nat) := [(9042896896,115630441213322,115630830610705)]
theorem point_links_checked68961 : (cuts68961.take 1).map (fun c => (9042788353-1+2*2^10*c.k,115630293858963+c.lower,115630683256264+c.upper)) = pointBounds68961 := by
 decide +kernel
def cuts68962 : List PrefixCut := [⟨64,177544573,177544678⟩]
theorem checked68962 : checkPrefixCuts (2^48) 9042919425 10 Manual.Count131072.C068962.packed 64 cuts68962 = true := by
 decide +kernel
def cuts68963 : List PrefixCut := [⟨63,176608224,176608332⟩,
⟨64,179627412,179627522⟩]
theorem checked68963 : checkPrefixCuts (2^48) 9043050497 10 Manual.Count131072.C068963.packed 64 cuts68963 = true := by
 decide +kernel
def pointBounds68963 : List (Nat × Nat × Nat) := [(9043179520,115630824811871,115631214209487)]
theorem point_links_checked68963 : (cuts68963.take 1).map (fun c => (9043050497-1+2*2^10*c.k,115630648203647+c.lower,115631037601155+c.upper)) = pointBounds68963 := by
 decide +kernel
def cuts68964 : List PrefixCut := [⟨64,178815555,178815658⟩]
theorem checked68964 : checkPrefixCuts (2^48) 9043181569 10 Manual.Count131072.C068964.packed 64 cuts68964 = true := by
 decide +kernel
def cuts68965 : List PrefixCut := [⟨64,180587085,180587195⟩]
theorem checked68965 : checkPrefixCuts (2^48) 9043312641 10 Manual.Count131072.C068965.packed 64 cuts68965 = true := by
 decide +kernel
def cuts68966 : List PrefixCut := [⟨9,23997155,23997170⟩,
⟨64,177876632,177876732⟩]
theorem checked68966 : checkPrefixCuts (2^48) 9043443713 10 Manual.Count131072.C068966.packed 64 cuts68966 = true := by
 decide +kernel
def pointBounds68966 : List (Nat × Nat × Nat) := [(9043462144,115631211230854,115631600628700)]
theorem point_links_checked68966 : (cuts68966.take 1).map (fun c => (9043443713-1+2*2^10*c.k,115631187233699+c.lower,115631576631530+c.upper)) = pointBounds68966 := by
 decide +kernel
def cuts68967 : List PrefixCut := [⟨64,178652159,178652263⟩]
theorem checked68967 : checkPrefixCuts (2^48) 9043574785 10 Manual.Count131072.C068967.packed 64 cuts68967 = true := by
 decide +kernel
def cuts68968 : List PrefixCut := [⟨19,51540977,51541006⟩,
⟨64,177933724,177933826⟩]
theorem checked68968 : checkPrefixCuts (2^48) 9043705857 10 Manual.Count131072.C068968.packed 64 cuts68968 = true := by
 decide +kernel
def pointBounds68968 : List (Nat × Nat × Nat) := [(9043744768,115631595303467,115631984701531)]
theorem point_links_checked68968 : (cuts68968.take 1).map (fun c => (9043705857-1+2*2^10*c.k,115631543762490+c.lower,115631933160525+c.upper)) = pointBounds68968 := by
 decide +kernel
def cuts68969 : List PrefixCut := [⟨64,178615854,178615963⟩]
theorem checked68969 : checkPrefixCuts (2^48) 9043836929 10 Manual.Count131072.C068969.packed 64 cuts68969 = true := by
 decide +kernel
def cuts68970 : List PrefixCut := [⟨29,80296931,80296975⟩,
⟨64,175998966,175999070⟩]
theorem checked68970 : checkPrefixCuts (2^48) 9043968001 10 Manual.Count131072.C068970.packed 64 cuts68970 = true := by
 decide +kernel
def pointBounds68970 : List (Nat × Nat × Nat) := [(9044027392,115631980608999,115632370007289)]
theorem point_links_checked68970 : (cuts68970.take 1).map (fun c => (9043968001-1+2*2^10*c.k,115631900312068+c.lower,115632289710314+c.upper)) = pointBounds68970 := by
 decide +kernel
def cuts68971 : List PrefixCut := [⟨64,179980062,179980165⟩]
theorem checked68971 : checkPrefixCuts (2^48) 9044099073 10 Manual.Count131072.C068971.packed 64 cuts68971 = true := by
 decide +kernel
def cuts68972 : List PrefixCut := [⟨40,109082257,109082322⟩,
⟨64,175838248,175838349⟩]
theorem checked68972 : checkPrefixCuts (2^48) 9044230145 10 Manual.Count131072.C068972.packed 64 cuts68972 = true := by
 decide +kernel
def pointBounds68972 : List (Nat × Nat × Nat) := [(9044312064,115632365373353,115632754771871)]
theorem point_links_checked68972 : (cuts68972.take 1).map (fun c => (9044230145-1+2*2^10*c.k,115632256291096+c.lower,115632645689549+c.upper)) = pointBounds68972 := by
 decide +kernel
def cuts68973 : List PrefixCut := [⟨64,177765235,177765344⟩]
theorem checked68973 : checkPrefixCuts (2^48) 9044361217 10 Manual.Count131072.C068973.packed 64 cuts68973 = true := by
 decide +kernel
def cuts68974 : List PrefixCut := [⟨51,138177056,138177141⟩,
⟨64,174339347,174339456⟩]
theorem checked68974 : checkPrefixCuts (2^48) 9044492289 10 Manual.Count131072.C068974.packed 64 cuts68974 = true := by
 decide +kernel
def pointBounds68974 : List (Nat × Nat × Nat) := [(9044596736,115632748071635,115633137470383)]
theorem point_links_checked68974 : (cuts68974.take 1).map (fun c => (9044492289-1+2*2^10*c.k,115632609894579+c.lower,115632999293242+c.upper)) = pointBounds68974 := by
 decide +kernel
def cuts68975 : List PrefixCut := [⟨64,180529794,180529900⟩]
theorem checked68975 : checkPrefixCuts (2^48) 9044623361 10 Manual.Count131072.C068975.packed 64 cuts68975 = true := by
 decide +kernel
def cuts68976 : List PrefixCut := [⟨62,168763855,168763960⟩,
⟨64,174178699,174178807⟩]
theorem checked68976 : checkPrefixCuts (2^48) 9044754433 10 Manual.Count131072.C068976.packed 64 cuts68976 = true := by
 decide +kernel
def pointBounds68976 : List (Nat × Nat × Nat) := [(9044881408,115633133527575,115633522926558)]
theorem point_links_checked68976 : (cuts68976.take 1).map (fun c => (9044754433-1+2*2^10*c.k,115632964763720+c.lower,115633354162598+c.upper)) = pointBounds68976 := by
 decide +kernel
def cuts68977 : List PrefixCut := [⟨64,179030825,179030927⟩]
theorem checked68977 : checkPrefixCuts (2^48) 9044885505 10 Manual.Count131072.C068977.packed 64 cuts68977 = true := by
 decide +kernel
def cuts68978 : List PrefixCut := [⟨64,175947453,175947559⟩]
theorem checked68978 : checkPrefixCuts (2^48) 9045016577 10 Manual.Count131072.C068978.packed 64 cuts68978 = true := by
 decide +kernel
def cuts68979 : List PrefixCut := [⟨9,25455218,25455236⟩,
⟨64,180239272,180239382⟩]
theorem checked68979 : checkPrefixCuts (2^48) 9045147649 10 Manual.Count131072.C068979.packed 64 cuts68979 = true := by
 decide +kernel
def pointBounds68979 : List (Nat × Nat × Nat) := [(9045166080,115633519375915,115633908775127)]
theorem point_links_checked68979 : (cuts68979.take 1).map (fun c => (9045147649-1+2*2^10*c.k,115633493920697+c.lower,115633883319891+c.upper)) = pointBounds68979 := by
 decide +kernel
def cuts68980 : List PrefixCut := [⟨64,178991932,178992031⟩]
theorem checked68980 : checkPrefixCuts (2^48) 9045278721 10 Manual.Count131072.C068980.packed 64 cuts68980 = true := by
 decide +kernel
def cuts68981 : List PrefixCut := [⟨20,55047581,55047616⟩,
⟨64,176188735,176188845⟩]
theorem checked68981 : checkPrefixCuts (2^48) 9045409793 10 Manual.Count131072.C068981.packed 64 cuts68981 = true := by
 decide +kernel
def pointBounds68981 : List (Nat × Nat × Nat) := [(9045450752,115633908199482,115634297598920)]
theorem point_links_checked68981 : (cuts68981.take 1).map (fun c => (9045409793-1+2*2^10*c.k,115633853151901+c.lower,115634242551304+c.upper)) = pointBounds68981 := by
 decide +kernel
def cuts68982 : List PrefixCut := [⟨64,178022107,178022211⟩]
theorem checked68982 : checkPrefixCuts (2^48) 9045540865 10 Manual.Count131072.C068982.packed 64 cuts68982 = true := by
 decide +kernel
def cuts68983 : List PrefixCut := [⟨31,84980444,84980498⟩,
⟨64,176743729,176743836⟩]
theorem checked68983 : checkPrefixCuts (2^48) 9045671937 10 Manual.Count131072.C068983.packed 64 cuts68983 = true := by
 decide +kernel
def pointBounds68983 : List (Nat × Nat × Nat) := [(9045735424,115634292343187,115634681742858)]
theorem point_links_checked68983 : (cuts68983.take 1).map (fun c => (9045671937-1+2*2^10*c.k,115634207362743+c.lower,115634596762360+c.upper)) = pointBounds68983 := by
 decide +kernel
def cuts68984 : List PrefixCut := [⟨64,179852819,179852924⟩]
theorem checked68984 : checkPrefixCuts (2^48) 9045803009 10 Manual.Count131072.C068984.packed 64 cuts68984 = true := by
 decide +kernel
def cuts68985 : List PrefixCut := [⟨42,113417930,113418001⟩,
⟨64,174653835,174653942⟩]
theorem checked68985 : checkPrefixCuts (2^48) 9045934081 10 Manual.Count131072.C068985.packed 64 cuts68985 = true := by
 decide +kernel
def pointBounds68985 : List (Nat × Nat × Nat) := [(9046020096,115634677377221,115635066777121)]
theorem point_links_checked68985 : (cuts68985.take 1).map (fun c => (9045934081-1+2*2^10*c.k,115634563959291+c.lower,115634953359120+c.upper)) = pointBounds68985 := by
 decide +kernel
def cuts68986 : List PrefixCut := [⟨64,175304743,175304845⟩]
theorem checked68986 : checkPrefixCuts (2^48) 9046065153 10 Manual.Count131072.C068986.packed 64 cuts68986 = true := by
 decide +kernel
def cuts68987 : List PrefixCut := [⟨53,148356749,148356837⟩,
⟨64,178942659,178942767⟩]
theorem checked68987 : checkPrefixCuts (2^48) 9046196225 10 Manual.Count131072.C068987.packed 64 cuts68987 = true := by
 decide +kernel
def pointBounds68987 : List (Nat × Nat × Nat) := [(9046304768,115635062274618,115635451674744)]
theorem point_links_checked68987 : (cuts68987.take 1).map (fun c => (9046196225-1+2*2^10*c.k,115634913917869+c.lower,115635303317907+c.upper)) = pointBounds68987 := by
 decide +kernel
def cuts68988 : List PrefixCut := [⟨64,177477666,177477779⟩]
theorem checked68988 : checkPrefixCuts (2^48) 9046327297 10 Manual.Count131072.C068988.packed 64 cuts68988 = true := by
 decide +kernel
def cuts68989 : List PrefixCut := [⟨64,177288415,177288523⟩]
theorem checked68989 : checkPrefixCuts (2^48) 9046458369 10 Manual.Count131072.C068989.packed 64 cuts68989 = true := by
 decide +kernel
def pointBounds68989 : List (Nat × Nat × Nat) := [(9046589440,115635447626609,115635837026976)]
theorem point_links_checked68989 : (cuts68989.take 1).map (fun c => (9046458369-1+2*2^10*c.k,115635270338194+c.lower,115635659738453+c.upper)) = pointBounds68989 := by
 decide +kernel
def cuts68990 : List PrefixCut := [⟨64,179183798,179183898⟩]
theorem checked68990 : checkPrefixCuts (2^48) 9046589441 10 Manual.Count131072.C068990.packed 64 cuts68990 = true := by
 decide +kernel
def cuts68991 : List PrefixCut := [⟨64,176847686,176847787⟩]
theorem checked68991 : checkPrefixCuts (2^48) 9046720513 10 Manual.Count131072.C068991.packed 64 cuts68991 = true := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S7.B000280
