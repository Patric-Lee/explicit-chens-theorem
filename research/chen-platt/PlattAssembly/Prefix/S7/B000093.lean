import PlattAssemblyKernel
import PlattCertificates.Count131072.C062976
import PlattCertificates.Count131072.C062977
import PlattCertificates.Count131072.C062978
import PlattCertificates.Count131072.C062979
import PlattCertificates.Count131072.C062980
import PlattCertificates.Count131072.C062981
import PlattCertificates.Count131072.C062982
import PlattCertificates.Count131072.C062983
import PlattCertificates.Count131072.C062984
import PlattCertificates.Count131072.C062985
import PlattCertificates.Count131072.C062986
import PlattCertificates.Count131072.C062987
import PlattCertificates.Count131072.C062988
import PlattCertificates.Count131072.C062989
import PlattCertificates.Count131072.C062990
import PlattCertificates.Count131072.C062991
import PlattCertificates.Count131072.C062992
import PlattCertificates.Count131072.C062993
import PlattCertificates.Count131072.C062994
import PlattCertificates.Count131072.C062995
import PlattCertificates.Count131072.C062996
import PlattCertificates.Count131072.C062997
import PlattCertificates.Count131072.C062998
import PlattCertificates.Count131072.C062999
import PlattCertificates.Count131072.C063000
import PlattCertificates.Count131072.C063001
import PlattCertificates.Count131072.C063002
import PlattCertificates.Count131072.C063003
import PlattCertificates.Count131072.C063004
import PlattCertificates.Count131072.C063005
import PlattCertificates.Count131072.C063006
import PlattCertificates.Count131072.C063007
namespace ChenEffective.PlattWindow.Assembly.Prefix.S7.B000093
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts62976 : List PrefixCut := [⟨41,125086864,125086932⟩,
⟨64,196457383,196457494⟩]
theorem checked62976 : checkPrefixCuts (2^48) 8258322433 10 Manual.Count131072.C062976.packed 64 cuts62976 = true := by
 decide +kernel
def pointBounds62976 : List (Nat × Nat × Nat) := [(8258406400,114514045502666,114514434252214)]
theorem point_links_checked62976 : (cuts62976.take 1).map (fun c => (8258322433-1+2*2^10*c.k,114513920415802+c.lower,114514309165282+c.upper)) = pointBounds62976 := by
 decide +kernel
def cuts62977 : List PrefixCut := [⟨64,195977114,195977229⟩]
theorem checked62977 : checkPrefixCuts (2^48) 8258453505 10 Manual.Count131072.C062977.packed 64 cuts62977 = true := by
 decide +kernel
def cuts62978 : List PrefixCut := [⟨40,120754427,120754496⟩,
⟨64,194235789,194235899⟩]
theorem checked62978 : checkPrefixCuts (2^48) 8258584577 10 Manual.Count131072.C062978.packed 64 cuts62978 = true := by
 decide +kernel
def pointBounds62978 : List (Nat × Nat × Nat) := [(8258666496,114514433604726,114514822354501)]
theorem point_links_checked62978 : (cuts62978.take 1).map (fun c => (8258584577-1+2*2^10*c.k,114514312850299+c.lower,114514701600005+c.upper)) = pointBounds62978 := by
 decide +kernel
def cuts62979 : List PrefixCut := [⟨64,196857018,196857133⟩]
theorem checked62979 : checkPrefixCuts (2^48) 8258715649 10 Manual.Count131072.C062979.packed 64 cuts62979 = true := by
 decide +kernel
def cuts62980 : List PrefixCut := [⟨39,120375710,120375779⟩,
⟨64,197092466,197092575⟩]
theorem checked62980 : checkPrefixCuts (2^48) 8258846721 10 Manual.Count131072.C062980.packed 64 cuts62980 = true := by
 decide +kernel
def pointBounds62980 : List (Nat × Nat × Nat) := [(8258926592,114514824318816,114515213068816)]
theorem point_links_checked62980 : (cuts62980.take 1).map (fun c => (8258846721-1+2*2^10*c.k,114514703943106+c.lower,114515092693037+c.upper)) = pointBounds62980 := by
 decide +kernel
def cuts62981 : List PrefixCut := [⟨64,196884850,196884964⟩]
theorem checked62981 : checkPrefixCuts (2^48) 8258977793 10 Manual.Count131072.C062981.packed 64 cuts62981 = true := by
 decide +kernel
def cuts62982 : List PrefixCut := [⟨38,116793467,116793530⟩,
⟨64,195382200,195382308⟩]
theorem checked62982 : checkPrefixCuts (2^48) 8259108865 10 Manual.Count131072.C062982.packed 64 cuts62982 = true := by
 decide +kernel
def pointBounds62982 : List (Nat × Nat × Nat) := [(8259186688,114515214713889,114515603464106)]
theorem point_links_checked62982 : (cuts62982.take 1).map (fun c => (8259108865-1+2*2^10*c.k,114515097920422+c.lower,114515486670576+c.upper)) = pointBounds62982 := by
 decide +kernel
def cuts62983 : List PrefixCut := [⟨64,193266155,193266264⟩]
theorem checked62983 : checkPrefixCuts (2^48) 8259239937 10 Manual.Count131072.C062983.packed 64 cuts62983 = true := by
 decide +kernel
def cuts62984 : List PrefixCut := [⟨37,112666175,112666241⟩,
⟨64,195784932,195785048⟩]
theorem checked62984 : checkPrefixCuts (2^48) 8259371009 10 Manual.Count131072.C062984.packed 64 cuts62984 = true := by
 decide +kernel
def pointBounds62984 : List (Nat × Nat × Nat) := [(8259446784,114515599234952,114515987985389)]
theorem point_links_checked62984 : (cuts62984.take 1).map (fun c => (8259371009-1+2*2^10*c.k,114515486568777+c.lower,114515875319148+c.upper)) = pointBounds62984 := by
 decide +kernel
def cuts62985 : List PrefixCut := [⟨64,195372899,195373008⟩]
theorem checked62985 : checkPrefixCuts (2^48) 8259502081 10 Manual.Count131072.C062985.packed 64 cuts62985 = true := by
 decide +kernel
def cuts62986 : List PrefixCut := [⟨36,109902282,109902348⟩,
⟨64,193495503,193495617⟩]
theorem checked62986 : checkPrefixCuts (2^48) 8259633153 10 Manual.Count131072.C062986.packed 64 cuts62986 = true := by
 decide +kernel
def pointBounds62986 : List (Nat × Nat × Nat) := [(8259706880,114515987628890,114516376379552)]
theorem point_links_checked62986 : (cuts62986.take 1).map (fun c => (8259633153-1+2*2^10*c.k,114515877726608+c.lower,114516266477204+c.upper)) = pointBounds62986 := by
 decide +kernel
def cuts62987 : List PrefixCut := [⟨64,194208042,194208157⟩]
theorem checked62987 : checkPrefixCuts (2^48) 8259764225 10 Manual.Count131072.C062987.packed 64 cuts62987 = true := by
 decide +kernel
def cuts62988 : List PrefixCut := [⟨35,107888252,107888315⟩,
⟨64,196454061,196454174⟩]
theorem checked62988 : checkPrefixCuts (2^48) 8259895297 10 Manual.Count131072.C062988.packed 64 cuts62988 = true := by
 decide +kernel
def pointBounds62988 : List (Nat × Nat × Nat) := [(8259966976,114516373318405,114516762069293)]
theorem point_links_checked62988 : (cuts62988.take 1).map (fun c => (8259895297-1+2*2^10*c.k,114516265430153+c.lower,114516654180978+c.upper)) = pointBounds62988 := by
 decide +kernel
def cuts62989 : List PrefixCut := [⟨64,196621328,196621439⟩]
theorem checked62989 : checkPrefixCuts (2^48) 8260026369 10 Manual.Count131072.C062989.packed 64 cuts62989 = true := by
 decide +kernel
def cuts62990 : List PrefixCut := [⟨34,103727556,103727615⟩,
⟨64,193687669,193687777⟩]
theorem checked62990 : checkPrefixCuts (2^48) 8260157441 10 Manual.Count131072.C062990.packed 64 cuts62990 = true := by
 decide +kernel
def pointBounds62990 : List (Nat × Nat × Nat) := [(8260227072,114516762233098,114517150984206)]
theorem point_links_checked62990 : (cuts62990.take 1).map (fun c => (8260157441-1+2*2^10*c.k,114516658505542+c.lower,114517047256591+c.upper)) = pointBounds62990 := by
 decide +kernel
def cuts62991 : List PrefixCut := [⟨64,195388362,195388475⟩]
theorem checked62991 : checkPrefixCuts (2^48) 8260288513 10 Manual.Count131072.C062991.packed 64 cuts62991 = true := by
 decide +kernel
def cuts62992 : List PrefixCut := [⟨33,100282707,100282762⟩,
⟨64,196816406,196816518⟩]
theorem checked62992 : checkPrefixCuts (2^48) 8260419585 10 Manual.Count131072.C062992.packed 64 cuts62992 = true := by
 decide +kernel
def pointBounds62992 : List (Nat × Nat × Nat) := [(8260487168,114517147864280,114517536615605)]
theorem point_links_checked62992 : (cuts62992.take 1).map (fun c => (8260419585-1+2*2^10*c.k,114517047581573+c.lower,114517436332843+c.upper)) = pointBounds62992 := by
 decide +kernel
def cuts62993 : List PrefixCut := [⟨64,193951040,193951158⟩]
theorem checked62993 : checkPrefixCuts (2^48) 8260550657 10 Manual.Count131072.C062993.packed 64 cuts62993 = true := by
 decide +kernel
def cuts62994 : List PrefixCut := [⟨32,97655847,97655901⟩,
⟨64,195379063,195379174⟩]
theorem checked62994 : checkPrefixCuts (2^48) 8260681729 10 Manual.Count131072.C062994.packed 64 cuts62994 = true := by
 decide +kernel
def pointBounds62994 : List (Nat × Nat × Nat) := [(8260747264,114517536004866,114517924756420)]
theorem point_links_checked62994 : (cuts62994.take 1).map (fun c => (8260681729-1+2*2^10*c.k,114517438349019+c.lower,114517827100519+c.upper)) = pointBounds62994 := by
 decide +kernel
def cuts62995 : List PrefixCut := [⟨64,195614470,195614585⟩]
theorem checked62995 : checkPrefixCuts (2^48) 8260812801 10 Manual.Count131072.C062995.packed 64 cuts62995 = true := by
 decide +kernel
def cuts62996 : List PrefixCut := [⟨31,94654346,94654399⟩,
⟨64,196701687,196701794⟩]
theorem checked62996 : checkPrefixCuts (2^48) 8260943873 10 Manual.Count131072.C062996.packed 64 cuts62996 = true := by
 decide +kernel
def pointBounds62996 : List (Nat × Nat × Nat) := [(8261007360,114517923996898,114518312748677)]
theorem point_links_checked62996 : (cuts62996.take 1).map (fun c => (8260943873-1+2*2^10*c.k,114517829342552+c.lower,114518218094278+c.upper)) = pointBounds62996 := by
 decide +kernel
def cuts62997 : List PrefixCut := [⟨64,194654243,194654351⟩]
theorem checked62997 : checkPrefixCuts (2^48) 8261074945 10 Manual.Count131072.C062997.packed 64 cuts62997 = true := by
 decide +kernel
def cuts62998 : List PrefixCut := [⟨30,92879626,92879681⟩,
⟨64,197342818,197342932⟩]
theorem checked62998 : checkPrefixCuts (2^48) 8261206017 10 Manual.Count131072.C062998.packed 64 cuts62998 = true := by
 decide +kernel
def pointBounds62998 : List (Nat × Nat × Nat) := [(8261267456,114518313578108,114518702330104)]
theorem point_links_checked62998 : (cuts62998.take 1).map (fun c => (8261206017-1+2*2^10*c.k,114518220698482+c.lower,114518609450423+c.upper)) = pointBounds62998 := by
 decide +kernel
def cuts62999 : List PrefixCut := [⟨64,196113124,196113236⟩]
theorem checked62999 : checkPrefixCuts (2^48) 8261337089 10 Manual.Count131072.C062999.packed 64 cuts62999 = true := by
 decide +kernel
def cuts63000 : List PrefixCut := [⟨29,88481569,88481619⟩,
⟨64,194202067,194202176⟩]
theorem checked63000 : checkPrefixCuts (2^48) 8261468161 10 Manual.Count131072.C063000.packed 64 cuts63000 = true := by
 decide +kernel
def pointBounds63000 : List (Nat × Nat × Nat) := [(8261527552,114518702635993,114519091388210)]
theorem point_links_checked63000 : (cuts63000.take 1).map (fun c => (8261468161-1+2*2^10*c.k,114518614154424+c.lower,114519002906591+c.upper)) = pointBounds63000 := by
 decide +kernel
def cuts63001 : List PrefixCut := [⟨64,195664000,195664109⟩]
theorem checked63001 : checkPrefixCuts (2^48) 8261599233 10 Manual.Count131072.C063001.packed 64 cuts63001 = true := by
 decide +kernel
def cuts63002 : List PrefixCut := [⟨28,85344369,85344417⟩,
⟨64,193753004,193753115⟩]
theorem checked63002 : checkPrefixCuts (2^48) 8261730305 10 Manual.Count131072.C063002.packed 64 cuts63002 = true := by
 decide +kernel
def pointBounds63002 : List (Nat × Nat × Nat) := [(8261787648,114519089364860,114519478117293)]
theorem point_links_checked63002 : (cuts63002.take 1).map (fun c => (8261730305-1+2*2^10*c.k,114519004020491+c.lower,114519392772876+c.upper)) = pointBounds63002 := by
 decide +kernel
def cuts63003 : List PrefixCut := [⟨64,194431310,194431425⟩]
theorem checked63003 : checkPrefixCuts (2^48) 8261861377 10 Manual.Count131072.C063003.packed 64 cuts63003 = true := by
 decide +kernel
def cuts63004 : List PrefixCut := [⟨27,81968888,81968931⟩,
⟨64,194360089,194360196⟩]
theorem checked63004 : checkPrefixCuts (2^48) 8261992449 10 Manual.Count131072.C063004.packed 64 cuts63004 = true := by
 decide +kernel
def pointBounds63004 : List (Nat × Nat × Nat) := [(8262047744,114519474173693,114519862926347)]
theorem point_links_checked63004 : (cuts63004.take 1).map (fun c => (8261992449-1+2*2^10*c.k,114519392204805+c.lower,114519780957416+c.upper)) = pointBounds63004 := by
 decide +kernel
def cuts63005 : List PrefixCut := [⟨64,195719711,195719825⟩]
theorem checked63005 : checkPrefixCuts (2^48) 8262123521 10 Manual.Count131072.C063005.packed 64 cuts63005 = true := by
 decide +kernel
def cuts63006 : List PrefixCut := [⟨26,80365123,80365169⟩,
⟨64,197249634,197249746⟩]
theorem checked63006 : checkPrefixCuts (2^48) 8262254593 10 Manual.Count131072.C063006.packed 64 cuts63006 = true := by
 decide +kernel
def pointBounds63006 : List (Nat × Nat × Nat) := [(8262307840,114519862649728,114520251402606)]
theorem point_links_checked63006 : (cuts63006.take 1).map (fun c => (8262254593-1+2*2^10*c.k,114519782284605+c.lower,114520171037437+c.upper)) = pointBounds63006 := by
 decide +kernel
def cuts63007 : List PrefixCut := [⟨64,195406895,195407011⟩]
theorem checked63007 : checkPrefixCuts (2^48) 8262385665 10 Manual.Count131072.C063007.packed 64 cuts63007 = true := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S7.B000093
