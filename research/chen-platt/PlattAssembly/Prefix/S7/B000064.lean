import PlattAssemblyKernel
import PlattCertificates.Count131072.C062048
import PlattCertificates.Count131072.C062049
import PlattCertificates.Count131072.C062050
import PlattCertificates.Count131072.C062051
import PlattCertificates.Count131072.C062052
import PlattCertificates.Count131072.C062053
import PlattCertificates.Count131072.C062054
import PlattCertificates.Count131072.C062055
import PlattCertificates.Count131072.C062056
import PlattCertificates.Count131072.C062057
import PlattCertificates.Count131072.C062058
import PlattCertificates.Count131072.C062059
import PlattCertificates.Count131072.C062060
import PlattCertificates.Count131072.C062061
import PlattCertificates.Count131072.C062062
import PlattCertificates.Count131072.C062063
import PlattCertificates.Count131072.C062064
import PlattCertificates.Count131072.C062065
import PlattCertificates.Count131072.C062066
import PlattCertificates.Count131072.C062067
import PlattCertificates.Count131072.C062068
import PlattCertificates.Count131072.C062069
import PlattCertificates.Count131072.C062070
import PlattCertificates.Count131072.C062071
import PlattCertificates.Count131072.C062072
import PlattCertificates.Count131072.C062073
import PlattCertificates.Count131072.C062074
import PlattCertificates.Count131072.C062075
import PlattCertificates.Count131072.C062076
import PlattCertificates.Count131072.C062077
import PlattCertificates.Count131072.C062078
import PlattCertificates.Count131072.C062079
namespace ChenEffective.PlattWindow.Assembly.Prefix.S7.B000064
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts62048 : List PrefixCut := [⟨48,147470359,147470444⟩,
⟨64,197560754,197560866⟩]
theorem checked62048 : checkPrefixCuts (2^48) 8136687617 10 Manual.Count131072.C062048.packed 64 cuts62048 = true := by
 decide +kernel
def pointBounds62048 : List (Nat × Nat × Nat) := [(8136785920,114331057783428,114331446427808)]
theorem point_links_checked62048 : (cuts62048.take 1).map (fun c => (8136687617-1+2*2^10*c.k,114330910313069+c.lower,114331298957364+c.upper)) = pointBounds62048 := by
 decide +kernel
def cuts62049 : List PrefixCut := [⟨64,198318603,198318720⟩]
theorem checked62049 : checkPrefixCuts (2^48) 8136818689 10 Manual.Count131072.C062049.packed 64 cuts62049 = true := by
 decide +kernel
def cuts62050 : List PrefixCut := [⟨45,139509505,139509586⟩,
⟨64,200010410,200010526⟩]
theorem checked62050 : checkPrefixCuts (2^48) 8136949761 10 Manual.Count131072.C062050.packed 64 cuts62050 = true := by
 decide +kernel
def pointBounds62050 : List (Nat × Nat × Nat) := [(8137041920,114331445701931,114331834346536)]
theorem point_links_checked62050 : (cuts62050.take 1).map (fun c => (8136949761-1+2*2^10*c.k,114331306192426+c.lower,114331694836950+c.upper)) = pointBounds62050 := by
 decide +kernel
def cuts62051 : List PrefixCut := [⟨64,200110952,200111066⟩]
theorem checked62051 : checkPrefixCuts (2^48) 8137080833 10 Manual.Count131072.C062051.packed 64 cuts62051 = true := by
 decide +kernel
def cuts62052 : List PrefixCut := [⟨42,130407671,130407743⟩,
⟨64,197824775,197824882⟩]
theorem checked62052 : checkPrefixCuts (2^48) 8137211905 10 Manual.Count131072.C062052.packed 64 cuts62052 = true := by
 decide +kernel
def pointBounds62052 : List (Nat × Nat × Nat) := [(8137297920,114331836721459,114332225366285)]
theorem point_links_checked62052 : (cuts62052.take 1).map (fun c => (8137211905-1+2*2^10*c.k,114331706313788+c.lower,114332094958542+c.upper)) = pointBounds62052 := by
 decide +kernel
def cuts62053 : List PrefixCut := [⟨64,199620270,199620386⟩]
theorem checked62053 : checkPrefixCuts (2^48) 8137342977 10 Manual.Count131072.C062053.packed 64 cuts62053 = true := by
 decide +kernel
def cuts62054 : List PrefixCut := [⟨39,122620802,122620871⟩,
⟨64,199513282,199513396⟩]
theorem checked62054 : checkPrefixCuts (2^48) 8137474049 10 Manual.Count131072.C062054.packed 64 cuts62054 = true := by
 decide +kernel
def pointBounds62054 : List (Nat × Nat × Nat) := [(8137553920,114332226379635,114332615024681)]
theorem point_links_checked62054 : (cuts62054.take 1).map (fun c => (8137474049-1+2*2^10*c.k,114332103758833+c.lower,114332492403810+c.upper)) = pointBounds62054 := by
 decide +kernel
def cuts62055 : List PrefixCut := [⟨64,197503874,197503990⟩]
theorem checked62055 : checkPrefixCuts (2^48) 8137605121 10 Manual.Count131072.C062055.packed 64 cuts62055 = true := by
 decide +kernel
def cuts62056 : List PrefixCut := [⟨36,113243365,113243426⟩,
⟨64,198642147,198642260⟩]
theorem checked62056 : checkPrefixCuts (2^48) 8137736193 10 Manual.Count131072.C062056.packed 64 cuts62056 = true := by
 decide +kernel
def pointBounds62056 : List (Nat × Nat × Nat) := [(8137809920,114332614019354,114333002664622)]
theorem point_links_checked62056 : (cuts62056.take 1).map (fun c => (8137736193-1+2*2^10*c.k,114332500775989+c.lower,114332889421196+c.upper)) = pointBounds62056 := by
 decide +kernel
def cuts62057 : List PrefixCut := [⟨64,198258478,198258586⟩]
theorem checked62057 : checkPrefixCuts (2^48) 8137867265 10 Manual.Count131072.C062057.packed 64 cuts62057 = true := by
 decide +kernel
def cuts62058 : List PrefixCut := [⟨33,102067972,102068031⟩,
⟨64,200503451,200503566⟩]
theorem checked62058 : checkPrefixCuts (2^48) 8137998337 10 Manual.Count131072.C062058.packed 64 cuts62058 = true := by
 decide +kernel
def pointBounds62058 : List (Nat × Nat × Nat) := [(8138065920,114332999744586,114333388390073)]
theorem point_links_checked62058 : (cuts62058.take 1).map (fun c => (8137998337-1+2*2^10*c.k,114332897676614+c.lower,114333286322042+c.upper)) = pointBounds62058 := by
 decide +kernel
def cuts62059 : List PrefixCut := [⟨64,198390430,198390540⟩]
theorem checked62059 : checkPrefixCuts (2^48) 8138129409 10 Manual.Count131072.C062059.packed 64 cuts62059 = true := by
 decide +kernel
def cuts62060 : List PrefixCut := [⟨30,94628624,94628677⟩,
⟨64,197972204,197972316⟩]
theorem checked62060 : checkPrefixCuts (2^48) 8138260481 10 Manual.Count131072.C062060.packed 64 cuts62060 = true := by
 decide +kernel
def pointBounds62060 : List (Nat × Nat × Nat) := [(8138321920,114333391199119,114333779844825)]
theorem point_links_checked62060 : (cuts62060.take 1).map (fun c => (8138260481-1+2*2^10*c.k,114333296570495+c.lower,114333685216148+c.upper)) = pointBounds62060 := by
 decide +kernel
def cuts62061 : List PrefixCut := [⟨64,199732885,199733002⟩]
theorem checked62061 : checkPrefixCuts (2^48) 8138391553 10 Manual.Count131072.C062061.packed 64 cuts62061 = true := by
 decide +kernel
def cuts62062 : List PrefixCut := [⟨27,84837949,84837999⟩,
⟨64,198692124,198692242⟩]
theorem checked62062 : checkPrefixCuts (2^48) 8138522625 10 Manual.Count131072.C062062.packed 64 cuts62062 = true := by
 decide +kernel
def pointBounds62062 : List (Nat × Nat × Nat) := [(8138577920,114333779113533,114334167759465)]
theorem point_links_checked62062 : (cuts62062.take 1).map (fun c => (8138522625-1+2*2^10*c.k,114333694275584+c.lower,114334082921466+c.upper)) = pointBounds62062 := by
 decide +kernel
def cuts62063 : List PrefixCut := [⟨64,196959685,196959799⟩]
theorem checked62063 : checkPrefixCuts (2^48) 8138653697 10 Manual.Count131072.C062063.packed 64 cuts62063 = true := by
 decide +kernel
def cuts62064 : List PrefixCut := [⟨24,74356213,74356257⟩,
⟨64,199723234,199723352⟩]
theorem checked62064 : checkPrefixCuts (2^48) 8138784769 10 Manual.Count131072.C062064.packed 64 cuts62064 = true := by
 decide +kernel
def pointBounds62064 : List (Nat × Nat × Nat) := [(8138833920,114334164283606,114334552929764)]
theorem point_links_checked62064 : (cuts62064.take 1).map (fun c => (8138784769-1+2*2^10*c.k,114334089927393+c.lower,114334478573507+c.upper)) = pointBounds62064 := by
 decide +kernel
def cuts62065 : List PrefixCut := [⟨64,200169616,200169726⟩]
theorem checked62065 : checkPrefixCuts (2^48) 8138915841 10 Manual.Count131072.C062065.packed 64 cuts62065 = true := by
 decide +kernel
def cuts62066 : List PrefixCut := [⟨21,64947217,64947253⟩,
⟨64,197883903,197884014⟩]
theorem checked62066 : checkPrefixCuts (2^48) 8139046913 10 Manual.Count131072.C062066.packed 64 cuts62066 = true := by
 decide +kernel
def pointBounds62066 : List (Nat × Nat × Nat) := [(8139089920,114334554767460,114334943413838)]
theorem point_links_checked62066 : (cuts62066.take 1).map (fun c => (8139046913-1+2*2^10*c.k,114334489820243+c.lower,114334878466585+c.upper)) = pointBounds62066 := by
 decide +kernel
def cuts62067 : List PrefixCut := [⟨64,200993135,200993255⟩]
theorem checked62067 : checkPrefixCuts (2^48) 8139177985 10 Manual.Count131072.C062067.packed 64 cuts62067 = true := by
 decide +kernel
def cuts62068 : List PrefixCut := [⟨18,55884646,55884676⟩,
⟨64,199952448,199952565⟩]
theorem checked62068 : checkPrefixCuts (2^48) 8139309057 10 Manual.Count131072.C062068.packed 64 cuts62068 = true := by
 decide +kernel
def pointBounds62068 : List (Nat × Nat × Nat) := [(8139345920,114334944581927,114335333228530)]
theorem point_links_checked62068 : (cuts62068.take 1).map (fun c => (8139309057-1+2*2^10*c.k,114334888697281+c.lower,114335277343854+c.upper)) = pointBounds62068 := by
 decide +kernel
def cuts62069 : List PrefixCut := [⟨64,198393085,198393199⟩]
theorem checked62069 : checkPrefixCuts (2^48) 8139440129 10 Manual.Count131072.C062069.packed 64 cuts62069 = true := by
 decide +kernel
def cuts62070 : List PrefixCut := [⟨15,45888961,45888989⟩,
⟨64,200291801,200291916⟩]
theorem checked62070 : checkPrefixCuts (2^48) 8139571201 10 Manual.Count131072.C062070.packed 64 cuts62070 = true := by
 decide +kernel
def pointBounds62070 : List (Nat × Nat × Nat) := [(8139601920,114335332931775,114335721578607)]
theorem point_links_checked62070 : (cuts62070.take 1).map (fun c => (8139571201-1+2*2^10*c.k,114335287042814+c.lower,114335675689618+c.upper)) = pointBounds62070 := by
 decide +kernel
def cuts62071 : List PrefixCut := [⟨64,198248350,198248462⟩]
theorem checked62071 : checkPrefixCuts (2^48) 8139702273 10 Manual.Count131072.C062071.packed 64 cuts62071 = true := by
 decide +kernel
def cuts62072 : List PrefixCut := [⟨12,37138791,37138813⟩,
⟨64,197276921,197277037⟩]
theorem checked62072 : checkPrefixCuts (2^48) 8139833345 10 Manual.Count131072.C062072.packed 64 cuts62072 = true := by
 decide +kernel
def pointBounds62072 : List (Nat × Nat × Nat) := [(8139857920,114335722721756,114336111368809)]
theorem point_links_checked62072 : (cuts62072.take 1).map (fun c => (8139833345-1+2*2^10*c.k,114335685582965+c.lower,114336074229996+c.upper)) = pointBounds62072 := by
 decide +kernel
def cuts62073 : List PrefixCut := [⟨64,199383083,199383198⟩]
theorem checked62073 : checkPrefixCuts (2^48) 8139964417 10 Manual.Count131072.C062073.packed 64 cuts62073 = true := by
 decide +kernel
def cuts62074 : List PrefixCut := [⟨9,27524709,27524725⟩,
⟨64,198204191,198204309⟩]
theorem checked62074 : checkPrefixCuts (2^48) 8140095489 10 Manual.Count131072.C062074.packed 64 cuts62074 = true := by
 decide +kernel
def pointBounds62074 : List (Nat × Nat × Nat) := [(8140113920,114336109767678,114336498414956)]
theorem point_links_checked62074 : (cuts62074.take 1).map (fun c => (8140095489-1+2*2^10*c.k,114336082242969+c.lower,114336470890231+c.upper)) = pointBounds62074 := by
 decide +kernel
def cuts62075 : List PrefixCut := [⟨64,200171957,200172070⟩]
theorem checked62075 : checkPrefixCuts (2^48) 8140226561 10 Manual.Count131072.C062075.packed 64 cuts62075 = true := by
 decide +kernel
def cuts62076 : List PrefixCut := [⟨6,19086880,19086891⟩,
⟨64,198681908,198682023⟩]
theorem checked62076 : checkPrefixCuts (2^48) 8140357633 10 Manual.Count131072.C062076.packed 64 cuts62076 = true := by
 decide +kernel
def pointBounds62076 : List (Nat × Nat × Nat) := [(8140369920,114336499705997,114336888353501)]
theorem point_links_checked62076 : (cuts62076.take 1).map (fun c => (8140357633-1+2*2^10*c.k,114336480619117+c.lower,114336869266610+c.upper)) = pointBounds62076 := by
 decide +kernel
def cuts62077 : List PrefixCut := [⟨64,198125461,198125577⟩]
theorem checked62077 : checkPrefixCuts (2^48) 8140488705 10 Manual.Count131072.C062077.packed 64 cuts62077 = true := by
 decide +kernel
def cuts62078 : List PrefixCut := [⟨3,9404830,9404835⟩,
⟨64,198398893,198399005⟩]
theorem checked62078 : checkPrefixCuts (2^48) 8140619777 10 Manual.Count131072.C062078.packed 64 cuts62078 = true := by
 decide +kernel
def pointBounds62078 : List (Nat × Nat × Nat) := [(8140625920,114336886831316,114337275479045)]
theorem point_links_checked62078 : (cuts62078.take 1).map (fun c => (8140619777-1+2*2^10*c.k,114336877426486+c.lower,114337266074210+c.upper)) = pointBounds62078 := by
 decide +kernel
def cuts62079 : List PrefixCut := [⟨64,199052632,199052746⟩]
theorem checked62079 : checkPrefixCuts (2^48) 8140750849 10 Manual.Count131072.C062079.packed 64 cuts62079 = true := by
 decide +kernel
def pointBounds62079 : List (Nat × Nat × Nat) := [(8140881920,114337274878011,114337663525961)]
theorem point_links_checked62079 : (cuts62079.take 1).map (fun c => (8140750849-1+2*2^10*c.k,114337075825379+c.lower,114337464473215+c.upper)) = pointBounds62079 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S7.B000064
