import PlattAssemblyKernel
import PlattCertificates.Count131072.C052976
import PlattCertificates.Count131072.C052977
import PlattCertificates.Count131072.C052978
import PlattCertificates.Count131072.C052979
import PlattCertificates.Count131072.C052980
import PlattCertificates.Count131072.C052981
import PlattCertificates.Count131072.C052982
import PlattCertificates.Count131072.C052983
import PlattCertificates.Count131072.C052984
import PlattCertificates.Count131072.C052985
import PlattCertificates.Count131072.C052986
import PlattCertificates.Count131072.C052987
import PlattCertificates.Count131072.C052988
import PlattCertificates.Count131072.C052989
import PlattCertificates.Count131072.C052990
import PlattCertificates.Count131072.C052991
import PlattCertificates.Count131072.C052992
import PlattCertificates.Count131072.C052993
import PlattCertificates.Count131072.C052994
import PlattCertificates.Count131072.C052995
import PlattCertificates.Count131072.C052996
import PlattCertificates.Count131072.C052997
import PlattCertificates.Count131072.C052998
import PlattCertificates.Count131072.C052999
import PlattCertificates.Count131072.C053000
import PlattCertificates.Count131072.C053001
import PlattCertificates.Count131072.C053002
import PlattCertificates.Count131072.C053003
import PlattCertificates.Count131072.C053004
import PlattCertificates.Count131072.C053005
import PlattCertificates.Count131072.C053006
import PlattCertificates.Count131072.C053007
namespace ChenEffective.PlattWindow.Assembly.Prefix.S6.B000093
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts52976 : List PrefixCut := [⟨64,237085450,237085581⟩]
theorem checked52976 : checkPrefixCuts (2^48) 6947602433 10 Manual.Count131072.C052976.packed 64 cuts52976 = true := by
 decide +kernel
def cuts52977 : List PrefixCut := [⟨36,133409251,133409324⟩,
⟨64,236716376,236716507⟩]
theorem checked52977 : checkPrefixCuts (2^48) 6947733505 10 Manual.Count131072.C052977.packed 64 cuts52977 = true := by
 decide +kernel
def pointBounds52977 : List (Nat × Nat × Nat) := [(6947807232,112375822935780,112376210466517)]
theorem point_links_checked52977 : (cuts52977.take 1).map (fun c => (6947733505-1+2*2^10*c.k,112375689526529+c.lower,112376077057193+c.upper)) = pointBounds52977 := by
 decide +kernel
def cuts52978 : List PrefixCut := [⟨64,234443239,234443370⟩]
theorem checked52978 : checkPrefixCuts (2^48) 6947864577 10 Manual.Count131072.C052978.packed 64 cuts52978 = true := by
 decide +kernel
def cuts52979 : List PrefixCut := [⟨15,56270583,56270614⟩,
⟨64,237517669,237517800⟩]
theorem checked52979 : checkPrefixCuts (2^48) 6947995649 10 Manual.Count131072.C052979.packed 64 cuts52979 = true := by
 decide +kernel
def pointBounds52979 : List (Nat × Nat × Nat) := [(6948026368,112376216956727,112376604487684)]
theorem point_links_checked52979 : (cuts52979.take 1).map (fun c => (6947995649-1+2*2^10*c.k,112376160686144+c.lower,112376548217070+c.upper)) = pointBounds52979 := by
 decide +kernel
def cuts52980 : List PrefixCut := [⟨58,212761439,212761560⟩,
⟨64,234191322,234191455⟩]
theorem checked52980 : checkPrefixCuts (2^48) 6948126721 10 Manual.Count131072.C052980.packed 64 cuts52980 = true := by
 decide +kernel
def pointBounds52980 : List (Nat × Nat × Nat) := [(6948245504,112376610965252,112376998496430)]
theorem point_links_checked52980 : (cuts52980.take 1).map (fun c => (6948126721-1+2*2^10*c.k,112376398203813+c.lower,112376785734870+c.upper)) = pointBounds52980 := by
 decide +kernel
def cuts52981 : List PrefixCut := [⟨64,235442726,235442862⟩]
theorem checked52981 : checkPrefixCuts (2^48) 6948257793 10 Manual.Count131072.C052981.packed 64 cuts52981 = true := by
 decide +kernel
def cuts52982 : List PrefixCut := [⟨37,133963780,133963858⟩,
⟨64,233777399,233777534⟩]
theorem checked52982 : checkPrefixCuts (2^48) 6948388865 10 Manual.Count131072.C052982.packed 64 cuts52982 = true := by
 decide +kernel
def pointBounds52982 : List (Nat × Nat × Nat) := [(6948464640,112377001801641,112377389333045)]
theorem point_links_checked52982 : (cuts52982.take 1).map (fun c => (6948388865-1+2*2^10*c.k,112376867837861+c.lower,112377255369187+c.upper)) = pointBounds52982 := by
 decide +kernel
def cuts52983 : List PrefixCut := [⟨64,231990609,231990738⟩]
theorem checked52983 : checkPrefixCuts (2^48) 6948519937 10 Manual.Count131072.C052983.packed 64 cuts52983 = true := by
 decide +kernel
def cuts52984 : List PrefixCut := [⟨16,58088116,58088148⟩,
⟨64,233566045,233566179⟩]
theorem checked52984 : checkPrefixCuts (2^48) 6948651009 10 Manual.Count131072.C052984.packed 64 cuts52984 = true := by
 decide +kernel
def pointBounds52984 : List (Nat × Nat × Nat) := [(6948683776,112377391693985,112377779225607)]
theorem point_links_checked52984 : (cuts52984.take 1).map (fun c => (6948651009-1+2*2^10*c.k,112377333605869+c.lower,112377721137459+c.upper)) = pointBounds52984 := by
 decide +kernel
def cuts52985 : List PrefixCut := [⟨59,217926207,217926327⟩,
⟨64,235667988,235668118⟩]
theorem checked52985 : checkPrefixCuts (2^48) 6948782081 10 Manual.Count131072.C052985.packed 64 cuts52985 = true := by
 decide +kernel
def pointBounds52985 : List (Nat × Nat × Nat) := [(6948902912,112377785098121,112378172629965)]
theorem point_links_checked52985 : (cuts52985.take 1).map (fun c => (6948782081-1+2*2^10*c.k,112377567171914+c.lower,112377954703638+c.upper)) = pointBounds52985 := by
 decide +kernel
def cuts52986 : List PrefixCut := [⟨64,231855967,231856099⟩]
theorem checked52986 : checkPrefixCuts (2^48) 6948913153 10 Manual.Count131072.C052986.packed 64 cuts52986 = true := by
 decide +kernel
def cuts52987 : List PrefixCut := [⟨38,138771257,138771335⟩,
⟨64,232904745,232904876⟩]
theorem checked52987 : checkPrefixCuts (2^48) 6949044225 10 Manual.Count131072.C052987.packed 64 cuts52987 = true := by
 decide +kernel
def pointBounds52987 : List (Nat × Nat × Nat) := [(6949122048,112378173467126,112378560999190)]
theorem point_links_checked52987 : (cuts52987.take 1).map (fun c => (6949044225-1+2*2^10*c.k,112378034695869+c.lower,112378422227855+c.upper)) = pointBounds52987 := by
 decide +kernel
def cuts52988 : List PrefixCut := [⟨64,231968751,231968889⟩]
theorem checked52988 : checkPrefixCuts (2^48) 6949175297 10 Manual.Count131072.C052988.packed 64 cuts52988 = true := by
 decide +kernel
def cuts52989 : List PrefixCut := [⟨17,60310344,60310381⟩,
⟨64,229372131,229372264⟩]
theorem checked52989 : checkPrefixCuts (2^48) 6949306369 10 Manual.Count131072.C052989.packed 64 cuts52989 = true := by
 decide +kernel
def pointBounds52989 : List (Nat × Nat × Nat) := [(6949341184,112378559879709,112378947412001)]
theorem point_links_checked52989 : (cuts52989.take 1).map (fun c => (6949306369-1+2*2^10*c.k,112378499569365+c.lower,112378887101620+c.upper)) = pointBounds52989 := by
 decide +kernel
def cuts52990 : List PrefixCut := [⟨60,220173798,220173923⟩,
⟨64,234754707,234754839⟩]
theorem checked52990 : checkPrefixCuts (2^48) 6949437441 10 Manual.Count131072.C052990.packed 64 cuts52990 = true := by
 decide +kernel
def pointBounds52990 : List (Nat × Nat × Nat) := [(6949560320,112378949115294,112379336647807)]
theorem point_links_checked52990 : (cuts52990.take 1).map (fun c => (6949437441-1+2*2^10*c.k,112378728941496+c.lower,112379116473884+c.upper)) = pointBounds52990 := by
 decide +kernel
def cuts52991 : List PrefixCut := [⟨64,235641329,235641461⟩]
theorem checked52991 : checkPrefixCuts (2^48) 6949568513 10 Manual.Count131072.C052991.packed 64 cuts52991 = true := by
 decide +kernel
def cuts52992 : List PrefixCut := [⟨39,144914382,144914464⟩,
⟨64,236770925,236771059⟩]
theorem checked52992 : checkPrefixCuts (2^48) 6949699585 10 Manual.Count131072.C052992.packed 64 cuts52992 = true := by
 decide +kernel
def pointBounds52992 : List (Nat × Nat × Nat) := [(6949779456,112379344251914,112379731784648)]
theorem point_links_checked52992 : (cuts52992.take 1).map (fun c => (6949699585-1+2*2^10*c.k,112379199337532+c.lower,112379586870184+c.upper)) = pointBounds52992 := by
 decide +kernel
def cuts52993 : List PrefixCut := [⟨64,231582377,231582510⟩]
theorem checked52993 : checkPrefixCuts (2^48) 6949830657 10 Manual.Count131072.C052993.packed 64 cuts52993 = true := by
 decide +kernel
def cuts52994 : List PrefixCut := [⟨18,65934164,65934202⟩,
⟨64,235911484,235911617⟩]
theorem checked52994 : checkPrefixCuts (2^48) 6949961729 10 Manual.Count131072.C052994.packed 64 cuts52994 = true := by
 decide +kernel
def pointBounds52994 : List (Nat × Nat × Nat) := [(6949998592,112379733624998,112380121157955)]
theorem point_links_checked52994 : (cuts52994.take 1).map (fun c => (6949961729-1+2*2^10*c.k,112379667690834+c.lower,112380055223753+c.upper)) = pointBounds52994 := by
 decide +kernel
def cuts52995 : List PrefixCut := [⟨61,226065884,226066012⟩,
⟨64,237162527,237162661⟩]
theorem checked52995 : checkPrefixCuts (2^48) 6950092801 10 Manual.Count131072.C052995.packed 64 cuts52995 = true := by
 decide +kernel
def pointBounds52995 : List (Nat × Nat × Nat) := [(6950217728,112380129668202,112380517201382)]
theorem point_links_checked52995 : (cuts52995.take 1).map (fun c => (6950092801-1+2*2^10*c.k,112379903602318+c.lower,112380291135370+c.upper)) = pointBounds52995 := by
 decide +kernel
def cuts52996 : List PrefixCut := [⟨64,232784220,232784354⟩]
theorem checked52996 : checkPrefixCuts (2^48) 6950223873 10 Manual.Count131072.C052996.packed 64 cuts52996 = true := by
 decide +kernel
def cuts52997 : List PrefixCut := [⟨40,150084392,150084479⟩,
⟨64,235817162,235817299⟩]
theorem checked52997 : checkPrefixCuts (2^48) 6950354945 10 Manual.Count131072.C052997.packed 64 cuts52997 = true := by
 decide +kernel
def pointBounds52997 : List (Nat × Nat × Nat) := [(6950436864,112380523633457,112380911166864)]
theorem point_links_checked52997 : (cuts52997.take 1).map (fun c => (6950354945-1+2*2^10*c.k,112380373549065+c.lower,112380761082385+c.upper)) = pointBounds52997 := by
 decide +kernel
def cuts52998 : List PrefixCut := [⟨64,235691203,235691336⟩]
theorem checked52998 : checkPrefixCuts (2^48) 6950486017 10 Manual.Count131072.C052998.packed 64 cuts52998 = true := by
 decide +kernel
def cuts52999 : List PrefixCut := [⟨19,67912255,67912294⟩,
⟨64,229976820,229976953⟩]
theorem checked52999 : checkPrefixCuts (2^48) 6950617089 10 Manual.Count131072.C052999.packed 64 cuts52999 = true := by
 decide +kernel
def pointBounds52999 : List (Nat × Nat × Nat) := [(6950656000,112380912969685,112381300503314)]
theorem point_links_checked52999 : (cuts52999.take 1).map (fun c => (6950617089-1+2*2^10*c.k,112380845057430+c.lower,112381232591020+c.upper)) = pointBounds52999 := by
 decide +kernel
def cuts53000 : List PrefixCut := [⟨62,227826310,227826442⟩,
⟨64,235803800,235803937⟩]
theorem checked53000 : checkPrefixCuts (2^48) 6950748161 10 Manual.Count131072.C053000.packed 64 cuts53000 = true := by
 decide +kernel
def pointBounds53000 : List (Nat × Nat × Nat) := [(6950875136,112381302860560,112381690394415)]
theorem point_links_checked53000 : (cuts53000.take 1).map (fun c => (6950748161-1+2*2^10*c.k,112381075034250+c.lower,112381462567973+c.upper)) = pointBounds53000 := by
 decide +kernel
def cuts53001 : List PrefixCut := [⟨64,232843252,232843387⟩]
theorem checked53001 : checkPrefixCuts (2^48) 6950879233 10 Manual.Count131072.C053001.packed 64 cuts53001 = true := by
 decide +kernel
def cuts53002 : List PrefixCut := [⟨41,146466278,146466364⟩,
⟨64,231219115,231219248⟩]
theorem checked53002 : checkPrefixCuts (2^48) 6951010305 10 Manual.Count131072.C053002.packed 64 cuts53002 = true := by
 decide +kernel
def pointBounds53002 : List (Nat × Nat × Nat) := [(6951094272,112381690147580,112382077681661)]
theorem point_links_checked53002 : (cuts53002.take 1).map (fun c => (6951010305-1+2*2^10*c.k,112381543681302+c.lower,112381931215297+c.upper)) = pointBounds53002 := by
 decide +kernel
def cuts53003 : List PrefixCut := [⟨64,235466535,235466669⟩]
theorem checked53003 : checkPrefixCuts (2^48) 6951141377 10 Manual.Count131072.C053003.packed 64 cuts53003 = true := by
 decide +kernel
def cuts53004 : List PrefixCut := [⟨20,73088880,73088919⟩,
⟨64,234287815,234287947⟩]
theorem checked53004 : checkPrefixCuts (2^48) 6951272449 10 Manual.Count131072.C053004.packed 64 cuts53004 = true := by
 decide +kernel
def pointBounds53004 : List (Nat × Nat × Nat) := [(6951313408,112382083455832,112382470990133)]
theorem point_links_checked53004 : (cuts53004.take 1).map (fun c => (6951272449-1+2*2^10*c.k,112382010366952+c.lower,112382397901214+c.upper)) = pointBounds53004 := by
 decide +kernel
def cuts53005 : List PrefixCut := [⟨63,232501808,232501941⟩,
⟨64,235579128,235579263⟩]
theorem checked53005 : checkPrefixCuts (2^48) 6951403521 10 Manual.Count131072.C053005.packed 64 cuts53005 = true := by
 decide +kernel
def pointBounds53005 : List (Nat × Nat × Nat) := [(6951532544,112382477156575,112382864691102)]
theorem point_links_checked53005 : (cuts53005.take 1).map (fun c => (6951403521-1+2*2^10*c.k,112382244654767+c.lower,112382632189161+c.upper)) = pointBounds53005 := by
 decide +kernel
def cuts53006 : List PrefixCut := [⟨64,233793081,233793215⟩]
theorem checked53006 : checkPrefixCuts (2^48) 6951534593 10 Manual.Count131072.C053006.packed 64 cuts53006 = true := by
 decide +kernel
def cuts53007 : List PrefixCut := [⟨42,151189788,151189875⟩,
⟨64,233100352,233100485⟩]
theorem checked53007 : checkPrefixCuts (2^48) 6951665665 10 Manual.Count131072.C053007.packed 64 cuts53007 = true := by
 decide +kernel
def pointBounds53007 : List (Nat × Nat × Nat) := [(6951751680,112382865216764,112383252751514)]
theorem point_links_checked53007 : (cuts53007.take 1).map (fun c => (6951665665-1+2*2^10*c.k,112382714026976+c.lower,112383101561639+c.upper)) = pointBounds53007 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S6.B000093
