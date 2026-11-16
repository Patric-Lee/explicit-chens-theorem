import PlattAssemblyKernel
import PlattCertificates.Count131072.C049984
import PlattCertificates.Count131072.C049985
import PlattCertificates.Count131072.C049986
import PlattCertificates.Count131072.C049987
import PlattCertificates.Count131072.C049988
import PlattCertificates.Count131072.C049989
import PlattCertificates.Count131072.C049990
import PlattCertificates.Count131072.C049991
import PlattCertificates.Count131072.C049992
import PlattCertificates.Count131072.C049993
import PlattCertificates.Count131072.C049994
import PlattCertificates.Count131072.C049995
import PlattCertificates.Count131072.C049996
import PlattCertificates.Count131072.C049997
import PlattCertificates.Count131072.C049998
import PlattCertificates.Count131072.C049999
namespace ChenEffective.PlattWindow.Assembly.Prefix.S5.B000312
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts49984 : List PrefixCut := [⟨26,101590037,101590097⟩,
⟨64,246760151,246760296⟩]
theorem checked49984 : checkPrefixCuts (2^48) 6555435009 10 Manual.Count131072.C049984.packed 64 cuts49984 = true := by
 decide +kernel
def pointBounds49984 : List (Nat × Nat × Nat) := [(6555488256,111652969202496,111653356322357)]
theorem point_links_checked49984 : (cuts49984.take 1).map (fun c => (6555435009-1+2*2^10*c.k,111652867612459+c.lower,111653254732260+c.upper)) = pointBounds49984 := by
 decide +kernel
def cuts49985 : List PrefixCut := [⟨63,242332806,242332949⟩,
⟨64,246197040,246197185⟩]
theorem checked49985 : checkPrefixCuts (2^48) 6555566081 10 Manual.Count131072.C049985.packed 64 cuts49985 = true := by
 decide +kernel
def pointBounds49985 : List (Nat × Nat × Nat) := [(6555695104,111653356705416,111653743825505)]
theorem point_links_checked49985 : (cuts49985.take 1).map (fun c => (6555566081-1+2*2^10*c.k,111653114372610+c.lower,111653501492556+c.upper)) = pointBounds49985 := by
 decide +kernel
def cuts49986 : List PrefixCut := [⟨64,245548093,245548230⟩]
theorem checked49986 : checkPrefixCuts (2^48) 6555697153 10 Manual.Count131072.C049986.packed 64 cuts49986 = true := by
 decide +kernel
def cuts49987 : List PrefixCut := [⟨36,140740350,140740429⟩,
⟨64,247303507,247303652⟩]
theorem checked49987 : checkPrefixCuts (2^48) 6555828225 10 Manual.Count131072.C049987.packed 64 cuts49987 = true := by
 decide +kernel
def pointBounds49987 : List (Nat × Nat × Nat) := [(6555901952,111653746858093,111654133978400)]
theorem point_links_checked49987 : (cuts49987.take 1).map (fun c => (6555828225-1+2*2^10*c.k,111653606117743+c.lower,111653993237971+c.upper)) = pointBounds49987 := by
 decide +kernel
def cuts49988 : List PrefixCut := [⟨64,249402301,249402449⟩]
theorem checked49988 : checkPrefixCuts (2^48) 6555959297 10 Manual.Count131072.C049988.packed 64 cuts49988 = true := by
 decide +kernel
def cuts49989 : List PrefixCut := [⟨9,35033561,35033582⟩,
⟨64,249397319,249397460⟩]
theorem checked49989 : checkPrefixCuts (2^48) 6556090369 10 Manual.Count131072.C049989.packed 64 cuts49989 = true := by
 decide +kernel
def pointBounds49989 : List (Nat × Nat × Nat) := [(6556108800,111654137857112,111654524977654)]
theorem point_links_checked49989 : (cuts49989.take 1).map (fun c => (6556090369-1+2*2^10*c.k,111654102823551+c.lower,111654489944072+c.upper)) = pointBounds49989 := by
 decide +kernel
def cuts49990 : List PrefixCut := [⟨46,177481652,177481751⟩,
⟨64,247503335,247503474⟩]
theorem checked49990 : checkPrefixCuts (2^48) 6556221441 10 Manual.Count131072.C049990.packed 64 cuts49990 = true := by
 decide +kernel
def pointBounds49990 : List (Nat × Nat × Nat) := [(6556315648,111654529702522,111654916823283)]
theorem point_links_checked49990 : (cuts49990.take 1).map (fun c => (6556221441-1+2*2^10*c.k,111654352220870+c.lower,111654739341532+c.upper)) = pointBounds49990 := by
 decide +kernel
def cuts49991 : List PrefixCut := [⟨64,248829268,248829408⟩]
theorem checked49991 : checkPrefixCuts (2^48) 6556352513 10 Manual.Count131072.C049991.packed 64 cuts49991 = true := by
 decide +kernel
def cuts49992 : List PrefixCut := [⟨19,73110883,73110929⟩,
⟨64,247922713,247922865⟩]
theorem checked49992 : checkPrefixCuts (2^48) 6556483585 10 Manual.Count131072.C049992.packed 64 cuts49992 = true := by
 decide +kernel
def pointBounds49992 : List (Nat × Nat × Nat) := [(6556522496,111654921664356,111655308785343)]
theorem point_links_checked49992 : (cuts49992.take 1).map (fun c => (6556483585-1+2*2^10*c.k,111654848553473+c.lower,111655235674414+c.upper)) = pointBounds49992 := by
 decide +kernel
def cuts49993 : List PrefixCut := [⟨56,215635079,215635201⟩,
⟨64,247488478,247488618⟩]
theorem checked49993 : checkPrefixCuts (2^48) 6556614657 10 Manual.Count131072.C049993.packed 64 cuts49993 = true := by
 decide +kernel
def pointBounds49993 : List (Nat × Nat × Nat) := [(6556729344,111655312111265,111655699232480)]
theorem point_links_checked49993 : (cuts49993.take 1).map (fun c => (6556614657-1+2*2^10*c.k,111655096476186+c.lower,111655483597279+c.upper)) = pointBounds49993 := by
 decide +kernel
def cuts49994 : List PrefixCut := [⟨64,249758732,249758874⟩]
theorem checked49994 : checkPrefixCuts (2^48) 6556745729 10 Manual.Count131072.C049994.packed 64 cuts49994 = true := by
 decide +kernel
def cuts49995 : List PrefixCut := [⟨29,112771858,112771925⟩,
⟨64,251556702,251556850⟩]
theorem checked49995 : checkPrefixCuts (2^48) 6556876801 10 Manual.Count131072.C049995.packed 64 cuts49995 = true := by
 decide +kernel
def pointBounds49995 : List (Nat × Nat × Nat) := [(6556936192,111655706495254,111656093616696)]
theorem point_links_checked49995 : (cuts49995.take 1).map (fun c => (6556876801-1+2*2^10*c.k,111655593723396+c.lower,111655980844771+c.upper)) = pointBounds49995 := by
 decide +kernel
def cuts49996 : List PrefixCut := [⟨64,248847297,248847441⟩]
theorem checked49996 : checkPrefixCuts (2^48) 6557007873 10 Manual.Count131072.C049996.packed 64 cuts49996 = true := by
 decide +kernel
def cuts49997 : List PrefixCut := [⟨2,7597985,7597989⟩,
⟨64,244721429,244721564⟩]
theorem checked49997 : checkPrefixCuts (2^48) 6557138945 10 Manual.Count131072.C049997.packed 64 cuts49997 = true := by
 decide +kernel
def pointBounds49997 : List (Nat × Nat × Nat) := [(6557143040,111656101725380,111656488847051)]
theorem point_links_checked49997 : (cuts49997.take 1).map (fun c => (6557138945-1+2*2^10*c.k,111656094127395+c.lower,111656481249062+c.upper)) = pointBounds49997 := by
 decide +kernel
def cuts49998 : List PrefixCut := [⟨39,151526527,151526613⟩,
⟨64,247077424,247077568⟩]
theorem checked49998 : checkPrefixCuts (2^48) 6557270017 10 Manual.Count131072.C049998.packed 64 cuts49998 = true := by
 decide +kernel
def pointBounds49998 : List (Nat × Nat × Nat) := [(6557349888,111656490375351,111656877497239)]
theorem point_links_checked49998 : (cuts49998.take 1).map (fun c => (6557270017-1+2*2^10*c.k,111656338848824+c.lower,111656725970626+c.upper)) = pointBounds49998 := by
 decide +kernel
def cuts49999 : List PrefixCut := [⟨64,251879999,251880146⟩]
theorem checked49999 : checkPrefixCuts (2^48) 6557401089 10 Manual.Count131072.C049999.packed 64 cuts49999 = true := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S5.B000312
