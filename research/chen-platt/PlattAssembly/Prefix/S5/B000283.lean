import PlattAssemblyKernel
import PlattCertificates.Count131072.C049056
import PlattCertificates.Count131072.C049057
import PlattCertificates.Count131072.C049058
import PlattCertificates.Count131072.C049059
import PlattCertificates.Count131072.C049060
import PlattCertificates.Count131072.C049061
import PlattCertificates.Count131072.C049062
import PlattCertificates.Count131072.C049063
import PlattCertificates.Count131072.C049064
import PlattCertificates.Count131072.C049065
import PlattCertificates.Count131072.C049066
import PlattCertificates.Count131072.C049067
import PlattCertificates.Count131072.C049068
import PlattCertificates.Count131072.C049069
import PlattCertificates.Count131072.C049070
import PlattCertificates.Count131072.C049071
import PlattCertificates.Count131072.C049072
import PlattCertificates.Count131072.C049073
import PlattCertificates.Count131072.C049074
import PlattCertificates.Count131072.C049075
import PlattCertificates.Count131072.C049076
import PlattCertificates.Count131072.C049077
import PlattCertificates.Count131072.C049078
import PlattCertificates.Count131072.C049079
import PlattCertificates.Count131072.C049080
import PlattCertificates.Count131072.C049081
import PlattCertificates.Count131072.C049082
import PlattCertificates.Count131072.C049083
import PlattCertificates.Count131072.C049084
import PlattCertificates.Count131072.C049085
import PlattCertificates.Count131072.C049086
import PlattCertificates.Count131072.C049087
namespace ChenEffective.PlattWindow.Assembly.Prefix.S5.B000283
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts49056 : List PrefixCut := [⟨64,252825193,252825346⟩]
theorem checked49056 : checkPrefixCuts (2^48) 6433800193 10 Manual.Count131072.C049056.packed 64 cuts49056 = true := by
 decide +kernel
def cuts49057 : List PrefixCut := [⟨14,54948002,54948034⟩,
⟨64,249670184,249670330⟩]
theorem checked49057 : checkPrefixCuts (2^48) 6433931265 10 Manual.Count131072.C049057.packed 64 cuts49057 = true := by
 decide +kernel
def pointBounds49057 : List (Nat × Nat × Nat) := [(6433959936,111419826109362,111420213096317)]
theorem point_links_checked49057 : (cuts49057.take 1).map (fun c => (6433931265-1+2*2^10*c.k,111419771161360+c.lower,111420158148283+c.upper)) = pointBounds49057 := by
 decide +kernel
def cuts49058 : List PrefixCut := [⟨49,194456638,194456745⟩,
⟨64,252114957,252115101⟩]
theorem checked49058 : checkPrefixCuts (2^48) 6434062337 10 Manual.Count131072.C049058.packed 64 cuts49058 = true := by
 decide +kernel
def pointBounds49058 : List (Nat × Nat × Nat) := [(6434162688,111420215288182,111420602275358)]
theorem point_links_checked49058 : (cuts49058.take 1).map (fun c => (6434062337-1+2*2^10*c.k,111420020831544+c.lower,111420407818613+c.upper)) = pointBounds49058 := by
 decide +kernel
def cuts49059 : List PrefixCut := [⟨64,257053142,257053289⟩]
theorem checked49059 : checkPrefixCuts (2^48) 6434193409 10 Manual.Count131072.C049059.packed 64 cuts49059 = true := by
 decide +kernel
def cuts49060 : List PrefixCut := [⟨20,79485927,79485973⟩,
⟨64,254335692,254335837⟩]
theorem checked49060 : checkPrefixCuts (2^48) 6434324481 10 Manual.Count131072.C049060.packed 64 cuts49060 = true := by
 decide +kernel
def pointBounds49060 : List (Nat × Nat × Nat) := [(6434365440,111420609485570,111420996472976)]
theorem point_links_checked49060 : (cuts49060.take 1).map (fun c => (6434324481-1+2*2^10*c.k,111420529999643+c.lower,111420916987003+c.upper)) = pointBounds49060 := by
 decide +kernel
def cuts49061 : List PrefixCut := [⟨55,218504081,218504203⟩,
⟨64,254461743,254461887⟩]
theorem checked49061 : checkPrefixCuts (2^48) 6434455553 10 Manual.Count131072.C049061.packed 64 cuts49061 = true := by
 decide +kernel
def pointBounds49061 : List (Nat × Nat × Nat) := [(6434568192,111421002839416,111421389827043)]
theorem point_links_checked49061 : (cuts49061.take 1).map (fun c => (6434455553-1+2*2^10*c.k,111420784335335+c.lower,111421171322840+c.upper)) = pointBounds49061 := by
 decide +kernel
def cuts49062 : List PrefixCut := [⟨64,254719003,254719148⟩]
theorem checked49062 : checkPrefixCuts (2^48) 6434586625 10 Manual.Count131072.C049062.packed 64 cuts49062 = true := by
 decide +kernel
def cuts49063 : List PrefixCut := [⟨26,103495894,103495951⟩,
⟨64,252701678,252701816⟩]
theorem checked49063 : checkPrefixCuts (2^48) 6434717697 10 Manual.Count131072.C049063.packed 64 cuts49063 = true := by
 decide +kernel
def pointBounds49063 : List (Nat × Nat × Nat) := [(6434770944,111421397011975,111421783999826)]
theorem point_links_checked49063 : (cuts49063.take 1).map (fun c => (6434717697-1+2*2^10*c.k,111421293516081+c.lower,111421680503875+c.upper)) = pointBounds49063 := by
 decide +kernel
def cuts49064 : List PrefixCut := [⟨61,241673693,241673831⟩,
⟨64,253352646,253352792⟩]
theorem checked49064 : checkPrefixCuts (2^48) 6434848769 10 Manual.Count131072.C049064.packed 64 cuts49064 = true := by
 decide +kernel
def pointBounds49064 : List (Nat × Nat × Nat) := [(6434973696,111421787891452,111422174879522)]
theorem point_links_checked49064 : (cuts49064.take 1).map (fun c => (6434848769-1+2*2^10*c.k,111421546217759+c.lower,111421933205691+c.upper)) = pointBounds49064 := by
 decide +kernel
def cuts49065 : List PrefixCut := [⟨64,253303737,253303885⟩]
theorem checked49065 : checkPrefixCuts (2^48) 6434979841 10 Manual.Count131072.C049065.packed 64 cuts49065 = true := by
 decide +kernel
def cuts49066 : List PrefixCut := [⟨32,125578301,125578373⟩,
⟨64,253517265,253517413⟩]
theorem checked49066 : checkPrefixCuts (2^48) 6435110913 10 Manual.Count131072.C049066.packed 64 cuts49066 = true := by
 decide +kernel
def pointBounds49066 : List (Nat × Nat × Nat) := [(6435176448,111422178452443,111422565440741)]
theorem point_links_checked49066 : (cuts49066.take 1).map (fun c => (6435110913-1+2*2^10*c.k,111422052874142+c.lower,111422439862368+c.upper)) = pointBounds49066 := by
 decide +kernel
def cuts49067 : List PrefixCut := [⟨64,255655337,255655484⟩]
theorem checked49067 : checkPrefixCuts (2^48) 6435241985 10 Manual.Count131072.C049067.packed 64 cuts49067 = true := by
 decide +kernel
def cuts49068 : List PrefixCut := [⟨3,10934671,10934678⟩,
⟨64,253944321,253944471⟩]
theorem checked49068 : checkPrefixCuts (2^48) 6435373057 10 Manual.Count131072.C049068.packed 64 cuts49068 = true := by
 decide +kernel
def pointBounds49068 : List (Nat × Nat × Nat) := [(6435379200,111422572981415,111422959969943)]
theorem point_links_checked49068 : (cuts49068.take 1).map (fun c => (6435373057-1+2*2^10*c.k,111422562046744+c.lower,111422949035265+c.upper)) = pointBounds49068 := by
 decide +kernel
def cuts49069 : List PrefixCut := [⟨38,148620201,148620288⟩,
⟨64,249959075,249959217⟩]
theorem checked49069 : checkPrefixCuts (2^48) 6435504129 10 Manual.Count131072.C049069.packed 64 cuts49069 = true := by
 decide +kernel
def pointBounds49069 : List (Nat × Nat × Nat) := [(6435581952,111422964611266,111423351600024)]
theorem point_links_checked49069 : (cuts49069.take 1).map (fun c => (6435504129-1+2*2^10*c.k,111422815991065+c.lower,111423202979736+c.upper)) = pointBounds49069 := by
 decide +kernel
def cuts49070 : List PrefixCut := [⟨64,255464768,255464911⟩]
theorem checked49070 : checkPrefixCuts (2^48) 6435635201 10 Manual.Count131072.C049070.packed 64 cuts49070 = true := by
 decide +kernel
def cuts49071 : List PrefixCut := [⟨9,36432064,36432083⟩,
⟨64,253360288,253360426⟩]
theorem checked49071 : checkPrefixCuts (2^48) 6435766273 10 Manual.Count131072.C049071.packed 64 cuts49071 = true := by
 decide +kernel
def pointBounds49071 : List (Nat × Nat × Nat) := [(6435784704,111423357846972,111423744835947)]
theorem point_links_checked49071 : (cuts49071.take 1).map (fun c => (6435766273-1+2*2^10*c.k,111423321414908+c.lower,111423708403864+c.upper)) = pointBounds49071 := by
 decide +kernel
def cuts49072 : List PrefixCut := [⟨44,175682837,175682935⟩,
⟨64,256022915,256023059⟩]
theorem checked49072 : checkPrefixCuts (2^48) 6435897345 10 Manual.Count131072.C049072.packed 64 cuts49072 = true := by
 decide +kernel
def pointBounds49072 : List (Nat × Nat × Nat) := [(6435987456,111423750458033,111424137447225)]
theorem point_links_checked49072 : (cuts49072.take 1).map (fun c => (6435897345-1+2*2^10*c.k,111423574775196+c.lower,111423961764290+c.upper)) = pointBounds49072 := by
 decide +kernel
def cuts49073 : List PrefixCut := [⟨64,257460934,257461077⟩]
theorem checked49073 : checkPrefixCuts (2^48) 6436028417 10 Manual.Count131072.C049073.packed 64 cuts49073 = true := by
 decide +kernel
def cuts49074 : List PrefixCut := [⟨15,60089495,60089529⟩,
⟨64,254044527,254044672⟩]
theorem checked49074 : checkPrefixCuts (2^48) 6436159489 10 Manual.Count131072.C049074.packed 64 cuts49074 = true := by
 decide +kernel
def pointBounds49074 : List (Nat × Nat × Nat) := [(6436190208,111424148348540,111424535337955)]
theorem point_links_checked49074 : (cuts49074.take 1).map (fun c => (6436159489-1+2*2^10*c.k,111424088259045+c.lower,111424475248426+c.upper)) = pointBounds49074 := by
 decide +kernel
def cuts49075 : List PrefixCut := [⟨50,194214384,194214496⟩,
⟨64,250934378,250934520⟩]
theorem checked49075 : checkPrefixCuts (2^48) 6436290561 10 Manual.Count131072.C049075.packed 64 cuts49075 = true := by
 decide +kernel
def pointBounds49075 : List (Nat × Nat × Nat) := [(6436392960,111424536517956,111424923507594)]
theorem point_links_checked49075 : (cuts49075.take 1).map (fun c => (6436290561-1+2*2^10*c.k,111424342303572+c.lower,111424729293098+c.upper)) = pointBounds49075 := by
 decide +kernel
def cuts49076 : List PrefixCut := [⟨64,256045807,256045949⟩]
theorem checked49076 : checkPrefixCuts (2^48) 6436421633 10 Manual.Count131072.C049076.packed 64 cuts49076 = true := by
 decide +kernel
def cuts49077 : List PrefixCut := [⟨21,82694461,82694505⟩,
⟨64,251755026,251755165⟩]
theorem checked49077 : checkPrefixCuts (2^48) 6436552705 10 Manual.Count131072.C049077.packed 64 cuts49077 = true := by
 decide +kernel
def pointBounds49077 : List (Nat × Nat × Nat) := [(6436595712,111424931978218,111425318968072)]
theorem point_links_checked49077 : (cuts49077.take 1).map (fun c => (6436552705-1+2*2^10*c.k,111424849283757+c.lower,111425236273567+c.upper)) = pointBounds49077 := by
 decide +kernel
def cuts49078 : List PrefixCut := [⟨56,223238641,223238771⟩,
⟨64,255073328,255073476⟩]
theorem checked49078 : checkPrefixCuts (2^48) 6436683777 10 Manual.Count131072.C049078.packed 64 cuts49078 = true := by
 decide +kernel
def pointBounds49078 : List (Nat × Nat × Nat) := [(6436798464,111425324277424,111425711267503)]
theorem point_links_checked49078 : (cuts49078.take 1).map (fun c => (6436683777-1+2*2^10*c.k,111425101038783+c.lower,111425488028732+c.upper)) = pointBounds49078 := by
 decide +kernel
def cuts49079 : List PrefixCut := [⟨64,255330485,255330634⟩]
theorem checked49079 : checkPrefixCuts (2^48) 6436814849 10 Manual.Count131072.C049079.packed 64 cuts49079 = true := by
 decide +kernel
def cuts49080 : List PrefixCut := [⟨27,105908809,105908872⟩,
⟨64,254188376,254188520⟩]
theorem checked49080 : checkPrefixCuts (2^48) 6436945921 10 Manual.Count131072.C049080.packed 64 cuts49080 = true := by
 decide +kernel
def pointBounds49080 : List (Nat × Nat × Nat) := [(6437001216,111425717351405,111426104341714)]
theorem point_links_checked49080 : (cuts49080.take 1).map (fun c => (6436945921-1+2*2^10*c.k,111425611442596+c.lower,111425998432842+c.upper)) = pointBounds49080 := by
 decide +kernel
def cuts49081 : List PrefixCut := [⟨62,244913239,244913377⟩,
⟨64,252696512,252696655⟩]
theorem checked49081 : checkPrefixCuts (2^48) 6437076993 10 Manual.Count131072.C049081.packed 64 cuts49081 = true := by
 decide +kernel
def pointBounds49081 : List (Nat × Nat × Nat) := [(6437203968,111426110544211,111426497534739)]
theorem point_links_checked49081 : (cuts49081.take 1).map (fun c => (6437076993-1+2*2^10*c.k,111425865630972+c.lower,111426252621362+c.upper)) = pointBounds49081 := by
 decide +kernel
def cuts49082 : List PrefixCut := [⟨64,254046863,254047010⟩]
theorem checked49082 : checkPrefixCuts (2^48) 6437208065 10 Manual.Count131072.C049082.packed 64 cuts49082 = true := by
 decide +kernel
def cuts49083 : List PrefixCut := [⟨33,128814203,128814277⟩,
⟨64,250674859,250675002⟩]
theorem checked49083 : checkPrefixCuts (2^48) 6437339137 10 Manual.Count131072.C049083.packed 64 cuts49083 = true := by
 decide +kernel
def pointBounds49083 : List (Nat × Nat × Nat) := [(6437406720,111426501188550,111426888179304)]
theorem point_links_checked49083 : (cuts49083.take 1).map (fun c => (6437339137-1+2*2^10*c.k,111426372374347+c.lower,111426759365027+c.upper)) = pointBounds49083 := by
 decide +kernel
def cuts49084 : List PrefixCut := [⟨64,254298836,254298981⟩]
theorem checked49084 : checkPrefixCuts (2^48) 6437470209 10 Manual.Count131072.C049084.packed 64 cuts49084 = true := by
 decide +kernel
def cuts49085 : List PrefixCut := [⟨4,17227076,17227085⟩,
⟨64,254556044,254556188⟩]
theorem checked49085 : checkPrefixCuts (2^48) 6437601281 10 Manual.Count131072.C049085.packed 64 cuts49085 = true := by
 decide +kernel
def pointBounds49085 : List (Nat × Nat × Nat) := [(6437609472,111426894575118,111427281566095)]
theorem point_links_checked49085 : (cuts49085.take 1).map (fun c => (6437601281-1+2*2^10*c.k,111426877348042+c.lower,111427264339010+c.upper)) = pointBounds49085 := by
 decide +kernel
def cuts49086 : List PrefixCut := [⟨39,153159596,153159686⟩,
⟨64,252539620,252539765⟩]
theorem checked49086 : checkPrefixCuts (2^48) 6437732353 10 Manual.Count131072.C049086.packed 64 cuts49086 = true := by
 decide +kernel
def pointBounds49086 : List (Nat × Nat × Nat) := [(6437812224,111427285063682,111427672054884)]
theorem point_links_checked49086 : (cuts49086.take 1).map (fun c => (6437732353-1+2*2^10*c.k,111427131904086+c.lower,111427518895198+c.upper)) = pointBounds49086 := by
 decide +kernel
def cuts49087 : List PrefixCut := [⟨64,251179109,251179251⟩]
theorem checked49087 : checkPrefixCuts (2^48) 6437863425 10 Manual.Count131072.C049087.packed 64 cuts49087 = true := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S5.B000283
