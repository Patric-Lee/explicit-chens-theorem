import PlattAssemblyKernel
import PlattCertificates.Count131072.C065088
import PlattCertificates.Count131072.C065089
import PlattCertificates.Count131072.C065090
import PlattCertificates.Count131072.C065091
import PlattCertificates.Count131072.C065092
import PlattCertificates.Count131072.C065093
import PlattCertificates.Count131072.C065094
import PlattCertificates.Count131072.C065095
import PlattCertificates.Count131072.C065096
import PlattCertificates.Count131072.C065097
import PlattCertificates.Count131072.C065098
import PlattCertificates.Count131072.C065099
import PlattCertificates.Count131072.C065100
import PlattCertificates.Count131072.C065101
import PlattCertificates.Count131072.C065102
import PlattCertificates.Count131072.C065103
import PlattCertificates.Count131072.C065104
import PlattCertificates.Count131072.C065105
import PlattCertificates.Count131072.C065106
import PlattCertificates.Count131072.C065107
import PlattCertificates.Count131072.C065108
import PlattCertificates.Count131072.C065109
import PlattCertificates.Count131072.C065110
import PlattCertificates.Count131072.C065111
import PlattCertificates.Count131072.C065112
import PlattCertificates.Count131072.C065113
import PlattCertificates.Count131072.C065114
import PlattCertificates.Count131072.C065115
import PlattCertificates.Count131072.C065116
import PlattCertificates.Count131072.C065117
import PlattCertificates.Count131072.C065118
import PlattCertificates.Count131072.C065119
namespace ChenEffective.PlattWindow.Assembly.Prefix.S7.B000159
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts65088 : List PrefixCut := [⟨64,188304829,188304945⟩]
theorem checked65088 : checkPrefixCuts (2^48) 8535146497 10 Manual.Count131072.C065088.packed 64 cuts65088 = true := by
 decide +kernel
def cuts65089 : List PrefixCut := [⟨2,6265785,6265789⟩,
⟨64,189489123,189489233⟩]
theorem checked65089 : checkPrefixCuts (2^48) 8535277569 10 Manual.Count131072.C065089.packed 64 cuts65089 = true := by
 decide +kernel
def pointBounds65089 : List (Nat × Nat × Nat) := [(8535281664,114920244911258,114920633895073)]
theorem point_links_checked65089 : (cuts65089.take 1).map (fun c => (8535277569-1+2*2^10*c.k,114920238645473+c.lower,114920627629284+c.upper)) = pointBounds65089 := by
 decide +kernel
def cuts65090 : List PrefixCut := [⟨64,189123465,189123579⟩]
theorem checked65090 : checkPrefixCuts (2^48) 8535408641 10 Manual.Count131072.C065090.packed 64 cuts65090 = true := by
 decide +kernel
def cuts65091 : List PrefixCut := [⟨5,14674673,14674681⟩,
⟨64,187438758,187438872⟩]
theorem checked65091 : checkPrefixCuts (2^48) 8535539713 10 Manual.Count131072.C065091.packed 64 cuts65091 = true := by
 decide +kernel
def pointBounds65091 : List (Nat × Nat × Nat) := [(8535549952,114920631932734,114921020916777)]
theorem point_links_checked65091 : (cuts65091.take 1).map (fun c => (8535539713-1+2*2^10*c.k,114920617258061+c.lower,114921006242096+c.upper)) = pointBounds65091 := by
 decide +kernel
def cuts65092 : List PrefixCut := [⟨64,190337772,190337882⟩]
theorem checked65092 : checkPrefixCuts (2^48) 8535670785 10 Manual.Count131072.C065092.packed 64 cuts65092 = true := by
 decide +kernel
def cuts65093 : List PrefixCut := [⟨8,23181965,23181978⟩,
⟨64,190829488,190829599⟩]
theorem checked65093 : checkPrefixCuts (2^48) 8535801857 10 Manual.Count131072.C065093.packed 64 cuts65093 = true := by
 decide +kernel
def pointBounds65093 : List (Nat × Nat × Nat) := [(8535818240,114921018216556,114921407200828)]
theorem point_links_checked65093 : (cuts65093.take 1).map (fun c => (8535801857-1+2*2^10*c.k,114920995034591+c.lower,114921384018850+c.upper)) = pointBounds65093 := by
 decide +kernel
def cuts65094 : List PrefixCut := [⟨64,187990711,187990823⟩]
theorem checked65094 : checkPrefixCuts (2^48) 8535932929 10 Manual.Count131072.C065094.packed 64 cuts65094 = true := by
 decide +kernel
def cuts65095 : List PrefixCut := [⟨11,32513096,32513115⟩,
⟨64,190955520,190955635⟩]
theorem checked65095 : checkPrefixCuts (2^48) 8536064001 10 Manual.Count131072.C065095.packed 64 cuts65095 = true := by
 decide +kernel
def pointBounds65095 : List (Nat × Nat × Nat) := [(8536086528,114921406367886,114921795352387)]
theorem point_links_checked65095 : (cuts65095.take 1).map (fun c => (8536064001-1+2*2^10*c.k,114921373854790+c.lower,114921762839272+c.upper)) = pointBounds65095 := by
 decide +kernel
def cuts65096 : List PrefixCut := [⟨64,189435779,189435890⟩]
theorem checked65096 : checkPrefixCuts (2^48) 8536195073 10 Manual.Count131072.C065096.packed 64 cuts65096 = true := by
 decide +kernel
def cuts65097 : List PrefixCut := [⟨14,41217150,41217172⟩,
⟨64,189268018,189268126⟩]
theorem checked65097 : checkPrefixCuts (2^48) 8536326145 10 Manual.Count131072.C065097.packed 64 cuts65097 = true := by
 decide +kernel
def pointBounds65097 : List (Nat × Nat × Nat) := [(8536354816,114921795463239,114922184447969)]
theorem point_links_checked65097 : (cuts65097.take 1).map (fun c => (8536326145-1+2*2^10*c.k,114921754246089+c.lower,114922143230797+c.upper)) = pointBounds65097 := by
 decide +kernel
def cuts65098 : List PrefixCut := [⟨64,193254862,193254965⟩]
theorem checked65098 : checkPrefixCuts (2^48) 8536457217 10 Manual.Count131072.C065098.packed 64 cuts65098 = true := by
 decide +kernel
def cuts65099 : List PrefixCut := [⟨17,49492016,49492045⟩,
⟨64,189756788,189756894⟩]
theorem checked65099 : checkPrefixCuts (2^48) 8536588289 10 Manual.Count131072.C065099.packed 64 cuts65099 = true := by
 decide +kernel
def pointBounds65099 : List (Nat × Nat × Nat) := [(8536623104,114922186260985,114922575245933)]
theorem point_links_checked65099 : (cuts65099.take 1).map (fun c => (8536588289-1+2*2^10*c.k,114922136768969+c.lower,114922525753888+c.upper)) = pointBounds65099 := by
 decide +kernel
def cuts65100 : List PrefixCut := [⟨64,186225862,186225981⟩]
theorem checked65100 : checkPrefixCuts (2^48) 8536719361 10 Manual.Count131072.C065100.packed 64 cuts65100 = true := by
 decide +kernel
def cuts65101 : List PrefixCut := [⟨20,57766367,57766402⟩,
⟨64,187673754,187673863⟩]
theorem checked65101 : checkPrefixCuts (2^48) 8536850433 10 Manual.Count131072.C065101.packed 64 cuts65101 = true := by
 decide +kernel
def pointBounds65101 : List (Nat × Nat × Nat) := [(8536891392,114922570517986,114922959503165)]
theorem point_links_checked65101 : (cuts65101.take 1).map (fun c => (8536850433-1+2*2^10*c.k,114922512751619+c.lower,114922901736763+c.upper)) = pointBounds65101 := by
 decide +kernel
def cuts65102 : List PrefixCut := [⟨64,190605299,190605410⟩]
theorem checked65102 : checkPrefixCuts (2^48) 8536981505 10 Manual.Count131072.C065102.packed 64 cuts65102 = true := by
 decide +kernel
def cuts65103 : List PrefixCut := [⟨23,67985477,67985514⟩,
⟨64,190305627,190305733⟩]
theorem checked65103 : checkPrefixCuts (2^48) 8537112577 10 Manual.Count131072.C065103.packed 64 cuts65103 = true := by
 decide +kernel
def pointBounds65103 : List (Nat × Nat × Nat) := [(8537159680,114922959016149,114923348001550)]
theorem point_links_checked65103 : (cuts65103.take 1).map (fun c => (8537112577-1+2*2^10*c.k,114922891030672+c.lower,114923280016036+c.upper)) = pointBounds65103 := by
 decide +kernel
def cuts65104 : List PrefixCut := [⟨64,189445484,189445592⟩]
theorem checked65104 : checkPrefixCuts (2^48) 8537243649 10 Manual.Count131072.C065104.packed 64 cuts65104 = true := by
 decide +kernel
def cuts65105 : List PrefixCut := [⟨26,76324672,76324716⟩,
⟨64,187134724,187134834⟩]
theorem checked65105 : checkPrefixCuts (2^48) 8537374721 10 Manual.Count131072.C065105.packed 64 cuts65105 = true := by
 decide +kernel
def pointBounds65105 : List (Nat × Nat × Nat) := [(8537427968,114923347106455,114923736092077)]
theorem point_links_checked65105 : (cuts65105.take 1).map (fun c => (8537374721-1+2*2^10*c.k,114923270781783+c.lower,114923659767361+c.upper)) = pointBounds65105 := by
 decide +kernel
def cuts65106 : List PrefixCut := [⟨64,187065906,187066020⟩]
theorem checked65106 : checkPrefixCuts (2^48) 8537505793 10 Manual.Count131072.C065106.packed 64 cuts65106 = true := by
 decide +kernel
def cuts65107 : List PrefixCut := [⟨29,86641472,86641521⟩,
⟨64,189964260,189964366⟩]
theorem checked65107 : checkPrefixCuts (2^48) 8537636865 10 Manual.Count131072.C065107.packed 64 cuts65107 = true := by
 decide +kernel
def pointBounds65107 : List (Nat × Nat × Nat) := [(8537696256,114923731623885,114924120609736)]
theorem point_links_checked65107 : (cuts65107.take 1).map (fun c => (8537636865-1+2*2^10*c.k,114923644982413+c.lower,114924033968215+c.upper)) = pointBounds65107 := by
 decide +kernel
def cuts65108 : List PrefixCut := [⟨64,187818419,187818530⟩]
theorem checked65108 : checkPrefixCuts (2^48) 8537767937 10 Manual.Count131072.C065108.packed 64 cuts65108 = true := by
 decide +kernel
def cuts65109 : List PrefixCut := [⟨32,95210348,95210404⟩,
⟨64,188375999,188376110⟩]
theorem checked65109 : checkPrefixCuts (2^48) 8537899009 10 Manual.Count131072.C065109.packed 64 cuts65109 = true := by
 decide +kernel
def pointBounds65109 : List (Nat × Nat × Nat) := [(8537964544,114924117975440,114924506961515)]
theorem point_links_checked65109 : (cuts65109.take 1).map (fun c => (8537899009-1+2*2^10*c.k,114924022765092+c.lower,114924411751111+c.upper)) = pointBounds65109 := by
 decide +kernel
def cuts65110 : List PrefixCut := [⟨64,188900574,188900684⟩]
theorem checked65110 : checkPrefixCuts (2^48) 8538030081 10 Manual.Count131072.C065110.packed 64 cuts65110 = true := by
 decide +kernel
def cuts65111 : List PrefixCut := [⟨35,103152338,103152400⟩,
⟨64,187875720,187875832⟩]
theorem checked65111 : checkPrefixCuts (2^48) 8538161153 10 Manual.Count131072.C065111.packed 64 cuts65111 = true := by
 decide +kernel
def pointBounds65111 : List (Nat × Nat × Nat) := [(8538232832,114924503194003,114924892180305)]
theorem point_links_checked65111 : (cuts65111.take 1).map (fun c => (8538161153-1+2*2^10*c.k,114924400041665+c.lower,114924789027905+c.upper)) = pointBounds65111 := by
 decide +kernel
def cuts65112 : List PrefixCut := [⟨64,190740864,190740976⟩]
theorem checked65112 : checkPrefixCuts (2^48) 8538292225 10 Manual.Count131072.C065112.packed 64 cuts65112 = true := by
 decide +kernel
def cuts65113 : List PrefixCut := [⟨38,111225683,111225744⟩,
⟨64,188199591,188199700⟩]
theorem checked65113 : checkPrefixCuts (2^48) 8538423297 10 Manual.Count131072.C065113.packed 64 cuts65113 = true := by
 decide +kernel
def pointBounds65113 : List (Nat × Nat × Nat) := [(8538501120,114924889883932,114925278870457)]
theorem point_links_checked65113 : (cuts65113.take 1).map (fun c => (8538423297-1+2*2^10*c.k,114924778658249+c.lower,114925167644713+c.upper)) = pointBounds65113 := by
 decide +kernel
def cuts65114 : List PrefixCut := [⟨64,187768164,187768271⟩]
theorem checked65114 : checkPrefixCuts (2^48) 8538554369 10 Manual.Count131072.C065114.packed 64 cuts65114 = true := by
 decide +kernel
def cuts65115 : List PrefixCut := [⟨41,122001629,122001694⟩,
⟨64,191094695,191094799⟩]
theorem checked65115 : checkPrefixCuts (2^48) 8538685441 10 Manual.Count131072.C065115.packed 64 cuts65115 = true := by
 decide +kernel
def pointBounds65115 : List (Nat × Nat × Nat) := [(8538769408,114925276627633,114925665614378)]
theorem point_links_checked65115 : (cuts65115.take 1).map (fun c => (8538685441-1+2*2^10*c.k,114925154626004+c.lower,114925543612684+c.upper)) = pointBounds65115 := by
 decide +kernel
def cuts65116 : List PrefixCut := [⟨64,186509772,186509877⟩]
theorem checked65116 : checkPrefixCuts (2^48) 8538816513 10 Manual.Count131072.C065116.packed 64 cuts65116 = true := by
 decide +kernel
def cuts65117 : List PrefixCut := [⟨44,128656454,128656532⟩,
⟨64,187067288,187067402⟩]
theorem checked65117 : checkPrefixCuts (2^48) 8538947585 10 Manual.Count131072.C065117.packed 64 cuts65117 = true := by
 decide +kernel
def pointBounds65117 : List (Nat × Nat × Nat) := [(8539037696,114925660886925,114926049873892)]
theorem point_links_checked65117 : (cuts65117.take 1).map (fun c => (8538947585-1+2*2^10*c.k,114925532230471+c.lower,114925921217360+c.upper)) = pointBounds65117 := by
 decide +kernel
def cuts65118 : List PrefixCut := [⟨64,191613312,191613424⟩]
theorem checked65118 : checkPrefixCuts (2^48) 8539078657 10 Manual.Count131072.C065118.packed 64 cuts65118 = true := by
 decide +kernel
def cuts65119 : List PrefixCut := [⟨47,138343421,138343506⟩,
⟨64,187852644,187852758⟩]
theorem checked65119 : checkPrefixCuts (2^48) 8539209729 10 Manual.Count131072.C065119.packed 64 cuts65119 = true := by
 decide +kernel
def pointBounds65119 : List (Nat × Nat × Nat) := [(8539305984,114926049254492,114926438241692)]
theorem point_links_checked65119 : (cuts65119.take 1).map (fun c => (8539209729-1+2*2^10*c.k,114925910911071+c.lower,114926299898186+c.upper)) = pointBounds65119 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S7.B000159
