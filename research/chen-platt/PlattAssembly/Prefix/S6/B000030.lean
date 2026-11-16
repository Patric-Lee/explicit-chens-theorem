import PlattAssemblyKernel
import PlattCertificates.Count131072.C050960
import PlattCertificates.Count131072.C050961
import PlattCertificates.Count131072.C050962
import PlattCertificates.Count131072.C050963
import PlattCertificates.Count131072.C050964
import PlattCertificates.Count131072.C050965
import PlattCertificates.Count131072.C050966
import PlattCertificates.Count131072.C050967
import PlattCertificates.Count131072.C050968
import PlattCertificates.Count131072.C050969
import PlattCertificates.Count131072.C050970
import PlattCertificates.Count131072.C050971
import PlattCertificates.Count131072.C050972
import PlattCertificates.Count131072.C050973
import PlattCertificates.Count131072.C050974
import PlattCertificates.Count131072.C050975
import PlattCertificates.Count131072.C050976
import PlattCertificates.Count131072.C050977
import PlattCertificates.Count131072.C050978
import PlattCertificates.Count131072.C050979
import PlattCertificates.Count131072.C050980
import PlattCertificates.Count131072.C050981
import PlattCertificates.Count131072.C050982
import PlattCertificates.Count131072.C050983
import PlattCertificates.Count131072.C050984
import PlattCertificates.Count131072.C050985
import PlattCertificates.Count131072.C050986
import PlattCertificates.Count131072.C050987
import PlattCertificates.Count131072.C050988
import PlattCertificates.Count131072.C050989
import PlattCertificates.Count131072.C050990
import PlattCertificates.Count131072.C050991
namespace ChenEffective.PlattWindow.Assembly.Prefix.S6.B000030
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts50960 : List PrefixCut := [⟨64,244353281,244353420⟩]
theorem checked50960 : checkPrefixCuts (2^48) 6683361281 10 Manual.Count131072.C050960.packed 64 cuts50960 = true := by
 decide +kernel
def cuts50961 : List PrefixCut := [⟨22,84524408,84524455⟩,
⟨64,243632553,243632692⟩]
theorem checked50961 : checkPrefixCuts (2^48) 6683492353 10 Manual.Count131072.C050961.packed 64 cuts50961 = true := by
 decide +kernel
def pointBounds50961 : List (Nat × Nat × Nat) := [(6683537408,111893799987728,111894187244602)]
theorem point_links_checked50961 : (cuts50961.take 1).map (fun c => (6683492353-1+2*2^10*c.k,111893715463320+c.lower,111894102720147+c.upper)) = pointBounds50961 := by
 decide +kernel
def cuts50962 : List PrefixCut := [⟨60,230909568,230909700⟩,
⟨64,246617834,246617975⟩]
theorem checked50962 : checkPrefixCuts (2^48) 6683623425 10 Manual.Count131072.C050962.packed 64 cuts50962 = true := by
 decide +kernel
def pointBounds50962 : List (Nat × Nat × Nat) := [(6683746304,111894190005441,111894577262539)]
theorem point_links_checked50962 : (cuts50962.take 1).map (fun c => (6683623425-1+2*2^10*c.k,111893959095873+c.lower,111894346352839+c.upper)) = pointBounds50962 := by
 decide +kernel
def cuts50963 : List PrefixCut := [⟨64,244465257,244465395⟩]
theorem checked50963 : checkPrefixCuts (2^48) 6683754497 10 Manual.Count131072.C050963.packed 64 cuts50963 = true := by
 decide +kernel
def cuts50964 : List PrefixCut := [⟨34,130505851,130505925⟩,
⟨64,244376244,244376382⟩]
theorem checked50964 : checkPrefixCuts (2^48) 6683885569 10 Manual.Count131072.C050964.packed 64 cuts50964 = true := by
 decide +kernel
def pointBounds50964 : List (Nat × Nat × Nat) := [(6683955200,111894580684815,111894967942134)]
theorem point_links_checked50964 : (cuts50964.take 1).map (fun c => (6683885569-1+2*2^10*c.k,111894450178964+c.lower,111894837436209+c.upper)) = pointBounds50964 := by
 decide +kernel
def cuts50965 : List PrefixCut := [⟨64,244287253,244287388⟩]
theorem checked50965 : checkPrefixCuts (2^48) 6684016641 10 Manual.Count131072.C050965.packed 64 cuts50965 = true := by
 decide +kernel
def cuts50966 : List PrefixCut := [⟨8,30488194,30488210⟩,
⟨64,246135286,246135423⟩]
theorem checked50966 : checkPrefixCuts (2^48) 6684147713 10 Manual.Count131072.C050966.packed 64 cuts50966 = true := by
 decide +kernel
def pointBounds50966 : List (Nat × Nat × Nat) := [(6684164096,111894969330655,111895356588189)]
theorem point_links_checked50966 : (cuts50966.take 1).map (fun c => (6684147713-1+2*2^10*c.k,111894938842461+c.lower,111895326099979+c.upper)) = pointBounds50966 := by
 decide +kernel
def cuts50967 : List PrefixCut := [⟨46,178334543,178334639⟩,
⟨64,243814467,243814602⟩]
theorem checked50967 : checkPrefixCuts (2^48) 6684278785 10 Manual.Count131072.C050967.packed 64 cuts50967 = true := by
 decide +kernel
def pointBounds50967 : List (Nat × Nat × Nat) := [(6684372992,111895363312290,111895750570041)]
theorem point_links_checked50967 : (cuts50967.take 1).map (fun c => (6684278785-1+2*2^10*c.k,111895184977747+c.lower,111895572235402+c.upper)) = pointBounds50967 := by
 decide +kernel
def cuts50968 : List PrefixCut := [⟨64,245620341,245620478⟩]
theorem checked50968 : checkPrefixCuts (2^48) 6684409857 10 Manual.Count131072.C050968.packed 64 cuts50968 = true := by
 decide +kernel
def cuts50969 : List PrefixCut := [⟨20,76468504,76468549⟩,
⟨64,243046942,243047082⟩]
theorem checked50969 : checkPrefixCuts (2^48) 6684540929 10 Manual.Count131072.C050969.packed 64 cuts50969 = true := by
 decide +kernel
def pointBounds50969 : List (Nat × Nat × Nat) := [(6684581888,111895750881059,111896138139031)]
theorem point_links_checked50969 : (cuts50969.take 1).map (fun c => (6684540929-1+2*2^10*c.k,111895674412555+c.lower,111896061670482+c.upper)) = pointBounds50969 := by
 decide +kernel
def cuts50970 : List PrefixCut := [⟨58,221862491,221862617⟩,
⟨64,244768549,244768687⟩]
theorem checked50970 : checkPrefixCuts (2^48) 6684672001 10 Manual.Count131072.C050970.packed 64 cuts50970 = true := by
 decide +kernel
def pointBounds50970 : List (Nat × Nat × Nat) := [(6684790784,111896139321988,111896526580181)]
theorem point_links_checked50970 : (cuts50970.take 1).map (fun c => (6684672001-1+2*2^10*c.k,111895917459497+c.lower,111896304717564+c.upper)) = pointBounds50970 := by
 decide +kernel
def cuts50971 : List PrefixCut := [⟨64,244595310,244595451⟩]
theorem checked50971 : checkPrefixCuts (2^48) 6684803073 10 Manual.Count131072.C050971.packed 64 cuts50971 = true := by
 decide +kernel
def cuts50972 : List PrefixCut := [⟨33,126485361,126485435⟩,
⟨64,241643181,241643318⟩]
theorem checked50972 : checkPrefixCuts (2^48) 6684934145 10 Manual.Count131072.C050972.packed 64 cuts50972 = true := by
 decide +kernel
def pointBounds50972 : List (Nat × Nat × Nat) := [(6685001728,111896533308717,111896920567137)]
theorem point_links_checked50972 : (cuts50972.take 1).map (fun c => (6684934145-1+2*2^10*c.k,111896406823356+c.lower,111896794081702+c.upper)) = pointBounds50972 := by
 decide +kernel
def cuts50973 : List PrefixCut := [⟨64,246185709,246185852⟩]
theorem checked50973 : checkPrefixCuts (2^48) 6685065217 10 Manual.Count131072.C050973.packed 64 cuts50973 = true := by
 decide +kernel
def cuts50974 : List PrefixCut := [⟨8,30062368,30062385⟩,
⟨64,241338973,241339115⟩]
theorem checked50974 : checkPrefixCuts (2^48) 6685196289 10 Manual.Count131072.C050974.packed 64 cuts50974 = true := by
 decide +kernel
def pointBounds50974 : List (Nat × Nat × Nat) := [(6685212672,111896924714614,111897311973257)]
theorem point_links_checked50974 : (cuts50974.take 1).map (fun c => (6685196289-1+2*2^10*c.k,111896894652246+c.lower,111897281910872+c.upper)) = pointBounds50974 := by
 decide +kernel
def cuts50975 : List PrefixCut := [⟨47,180201184,180201284⟩,
⟨64,242260517,242260653⟩]
theorem checked50975 : checkPrefixCuts (2^48) 6685327361 10 Manual.Count131072.C050975.packed 64 cuts50975 = true := by
 decide +kernel
def pointBounds50975 : List (Nat × Nat × Nat) := [(6685423616,111897316192403,111897703451271)]
theorem point_links_checked50975 : (cuts50975.take 1).map (fun c => (6685327361-1+2*2^10*c.k,111897135991219+c.lower,111897523249987+c.upper)) = pointBounds50975 := by
 decide +kernel
def cuts50976 : List PrefixCut := [⟨64,242760979,242761115⟩]
theorem checked50976 : checkPrefixCuts (2^48) 6685458433 10 Manual.Count131072.C050976.packed 64 cuts50976 = true := by
 decide +kernel
def cuts50977 : List PrefixCut := [⟨22,87655513,87655563⟩,
⟨64,250629166,250629310⟩]
theorem checked50977 : checkPrefixCuts (2^48) 6685589505 10 Manual.Count131072.C050977.packed 64 cuts50977 = true := by
 decide +kernel
def pointBounds50977 : List (Nat × Nat × Nat) := [(6685634560,111897708668228,111898095927318)]
theorem point_links_checked50977 : (cuts50977.take 1).map (fun c => (6685589505-1+2*2^10*c.k,111897621012715+c.lower,111898008271755+c.upper)) = pointBounds50977 := by
 decide +kernel
def cuts50978 : List PrefixCut := [⟨61,233194717,233194844⟩,
⟨64,245024846,245024979⟩]
theorem checked50978 : checkPrefixCuts (2^48) 6685720577 10 Manual.Count131072.C050978.packed 64 cuts50978 = true := by
 decide +kernel
def pointBounds50978 : List (Nat × Nat × Nat) := [(6685845504,111898104836598,111898492095909)]
theorem point_links_checked50978 : (cuts50978.take 1).map (fun c => (6685720577-1+2*2^10*c.k,111897871641881+c.lower,111898258901065+c.upper)) = pointBounds50978 := by
 decide +kernel
def cuts50979 : List PrefixCut := [⟨64,241020623,241020759⟩]
theorem checked50979 : checkPrefixCuts (2^48) 6685851649 10 Manual.Count131072.C050979.packed 64 cuts50979 = true := by
 decide +kernel
def cuts50980 : List PrefixCut := [⟨36,135011575,135011650⟩,
⟨64,245436223,245436362⟩]
theorem checked50980 : checkPrefixCuts (2^48) 6685982721 10 Manual.Count131072.C050980.packed 64 cuts50980 = true := by
 decide +kernel
def pointBounds50980 : List (Nat × Nat × Nat) := [(6686056448,111898492698925,111898879958453)]
theorem point_links_checked50980 : (cuts50980.take 1).map (fun c => (6685982721-1+2*2^10*c.k,111898357687350+c.lower,111898744946803+c.upper)) = pointBounds50980 := by
 decide +kernel
def cuts50981 : List PrefixCut := [⟨64,240463883,240464021⟩]
theorem checked50981 : checkPrefixCuts (2^48) 6686113793 10 Manual.Count131072.C050981.packed 64 cuts50981 = true := by
 decide +kernel
def cuts50982 : List PrefixCut := [⟨11,40497829,40497851⟩,
⟨64,242479801,242479940⟩]
theorem checked50982 : checkPrefixCuts (2^48) 6686244865 10 Manual.Count131072.C050982.packed 64 cuts50982 = true := by
 decide +kernel
def pointBounds50982 : List (Nat × Nat × Nat) := [(6686267392,111898884085285,111899271345037)]
theorem point_links_checked50982 : (cuts50982.take 1).map (fun c => (6686244865-1+2*2^10*c.k,111898843587456+c.lower,111899230847186+c.upper)) = pointBounds50982 := by
 decide +kernel
def cuts50983 : List PrefixCut := [⟨50,188886801,188886906⟩,
⟨64,242475067,242475203⟩]
theorem checked50983 : checkPrefixCuts (2^48) 6686375937 10 Manual.Count131072.C050983.packed 64 cuts50983 = true := by
 decide +kernel
def pointBounds50983 : List (Nat × Nat × Nat) := [(6686478336,111899274954058,111899662214032)]
theorem point_links_checked50983 : (cuts50983.take 1).map (fun c => (6686375937-1+2*2^10*c.k,111899086067257+c.lower,111899473327126+c.upper)) = pointBounds50983 := by
 decide +kernel
def cuts50984 : List PrefixCut := [⟨64,245711686,245711819⟩]
theorem checked50984 : checkPrefixCuts (2^48) 6686507009 10 Manual.Count131072.C050984.packed 64 cuts50984 = true := by
 decide +kernel
def cuts50985 : List PrefixCut := [⟨25,94208540,94208593⟩,
⟨64,243265351,243265488⟩]
theorem checked50985 : checkPrefixCuts (2^48) 6686638081 10 Manual.Count131072.C050985.packed 64 cuts50985 = true := by
 decide +kernel
def pointBounds50985 : List (Nat × Nat × Nat) := [(6686689280,111899668462550,111900055722741)]
theorem point_links_checked50985 : (cuts50985.take 1).map (fun c => (6686638081-1+2*2^10*c.k,111899574254010+c.lower,111899961514148+c.upper)) = pointBounds50985 := by
 decide +kernel
def cuts50986 : List PrefixCut := [⟨64,242039864,242040003⟩]
theorem checked50986 : checkPrefixCuts (2^48) 6686769153 10 Manual.Count131072.C050986.packed 64 cuts50986 = true := by
 decide +kernel
def pointBounds50986 : List (Nat × Nat × Nat) := [(6686900224,111900059559225,111900446819639)]
theorem point_links_checked50986 : (cuts50986.take 1).map (fun c => (6686769153-1+2*2^10*c.k,111899817519361+c.lower,111900204779636+c.upper)) = pointBounds50986 := by
 decide +kernel
def cuts50987 : List PrefixCut := [⟨64,246328636,246328769⟩]
theorem checked50987 : checkPrefixCuts (2^48) 6686900225 10 Manual.Count131072.C050987.packed 64 cuts50987 = true := by
 decide +kernel
def cuts50988 : List PrefixCut := [⟨39,148123168,148123252⟩,
⟨64,243629901,243630038⟩]
theorem checked50988 : checkPrefixCuts (2^48) 6687031297 10 Manual.Count131072.C050988.packed 64 cuts50988 = true := by
 decide +kernel
def pointBounds50988 : List (Nat × Nat × Nat) := [(6687111168,111900454011029,111900841271660)]
theorem point_links_checked50988 : (cuts50988.take 1).map (fun c => (6687031297-1+2*2^10*c.k,111900305887861+c.lower,111900693148408+c.upper)) = pointBounds50988 := by
 decide +kernel
def cuts50989 : List PrefixCut := [⟨64,243456763,243456899⟩]
theorem checked50989 : checkPrefixCuts (2^48) 6687162369 10 Manual.Count131072.C050989.packed 64 cuts50989 = true := by
 decide +kernel
def cuts50990 : List PrefixCut := [⟨14,54255190,54255220⟩,
⟨64,245851163,245851298⟩]
theorem checked50990 : checkPrefixCuts (2^48) 6687293441 10 Manual.Count131072.C050990.packed 64 cuts50990 = true := by
 decide +kernel
def pointBounds50990 : List (Nat × Nat × Nat) := [(6687322112,111900847229715,111901234490565)]
theorem point_links_checked50990 : (cuts50990.take 1).map (fun c => (6687293441-1+2*2^10*c.k,111900792974525+c.lower,111901180235345+c.upper)) = pointBounds50990 := by
 decide +kernel
def cuts50991 : List PrefixCut := [⟨53,201778689,201778807⟩,
⟨64,244162739,244162881⟩]
theorem checked50991 : checkPrefixCuts (2^48) 6687424513 10 Manual.Count131072.C050991.packed 64 cuts50991 = true := by
 decide +kernel
def pointBounds50991 : List (Nat × Nat × Nat) := [(6687533056,111901240604377,111901627865450)]
theorem point_links_checked50991 : (cuts50991.take 1).map (fun c => (6687424513-1+2*2^10*c.k,111901038825688+c.lower,111901426086643+c.upper)) = pointBounds50991 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S6.B000030
