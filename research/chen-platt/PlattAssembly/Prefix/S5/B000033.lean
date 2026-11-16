import PlattAssemblyKernel
import PlattCertificates.Count131072.C041056
import PlattCertificates.Count131072.C041057
import PlattCertificates.Count131072.C041058
import PlattCertificates.Count131072.C041059
import PlattCertificates.Count131072.C041060
import PlattCertificates.Count131072.C041061
import PlattCertificates.Count131072.C041062
import PlattCertificates.Count131072.C041063
import PlattCertificates.Count131072.C041064
import PlattCertificates.Count131072.C041065
import PlattCertificates.Count131072.C041066
import PlattCertificates.Count131072.C041067
import PlattCertificates.Count131072.C041068
import PlattCertificates.Count131072.C041069
import PlattCertificates.Count131072.C041070
import PlattCertificates.Count131072.C041071
import PlattCertificates.Count131072.C041072
import PlattCertificates.Count131072.C041073
import PlattCertificates.Count131072.C041074
import PlattCertificates.Count131072.C041075
import PlattCertificates.Count131072.C041076
import PlattCertificates.Count131072.C041077
import PlattCertificates.Count131072.C041078
import PlattCertificates.Count131072.C041079
import PlattCertificates.Count131072.C041080
import PlattCertificates.Count131072.C041081
import PlattCertificates.Count131072.C041082
import PlattCertificates.Count131072.C041083
import PlattCertificates.Count131072.C041084
import PlattCertificates.Count131072.C041085
import PlattCertificates.Count131072.C041086
import PlattCertificates.Count131072.C041087
namespace ChenEffective.PlattWindow.Assembly.Prefix.S5.B000033
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts41056 : List PrefixCut := [⟨33,155809934,155810025⟩,
⟨64,303412046,303412222⟩]
theorem checked41056 : checkPrefixCuts (2^48) 5385224193 10 Manual.Count131072.C041056.packed 64 cuts41056 = true := by
 decide +kernel
def pointBounds41056 : List (Nat × Nat × Nat) := [(5385291776,109193663466564,109194049166012)]
theorem point_links_checked41056 : (cuts41056.take 1).map (fun c => (5385224193-1+2*2^10*c.k,109193507656630+c.lower,109193893355987+c.upper)) = pointBounds41056 := by
 decide +kernel
def cuts41057 : List PrefixCut := [⟨52,251034630,251034772⟩,
⟨64,308526761,308526938⟩]
theorem checked41057 : checkPrefixCuts (2^48) 5385355265 10 Manual.Count131072.C041057.packed 64 cuts41057 = true := by
 decide +kernel
def pointBounds41057 : List (Nat × Nat × Nat) := [(5385461760,109194062103306,109194447802981)]
theorem point_links_checked41057 : (cuts41057.take 1).map (fun c => (5385355265-1+2*2^10*c.k,109193811068676+c.lower,109194196768209+c.upper)) = pointBounds41057 := by
 decide +kernel
def cuts41058 : List PrefixCut := [⟨64,302351973,302352152⟩]
theorem checked41058 : checkPrefixCuts (2^48) 5385486337 10 Manual.Count131072.C041058.packed 64 cuts41058 = true := by
 decide +kernel
def cuts41059 : List PrefixCut := [⟨7,34598844,34598865⟩,
⟨64,304957824,304958009⟩]
theorem checked41059 : checkPrefixCuts (2^48) 5385617409 10 Manual.Count131072.C041059.packed 64 cuts41059 = true := by
 decide +kernel
def pointBounds41059 : List (Nat × Nat × Nat) := [(5385631744,109194456546254,109194842246164)]
theorem point_links_checked41059 : (cuts41059.take 1).map (fun c => (5385617409-1+2*2^10*c.k,109194421947410+c.lower,109194807647299+c.upper)) = pointBounds41059 := by
 decide +kernel
def cuts41060 : List PrefixCut := [⟨26,121353881,121353955⟩,
⟨64,299880935,299881115⟩]
theorem checked41060 : checkPrefixCuts (2^48) 5385748481 10 Manual.Count131072.C041060.packed 64 cuts41060 = true := by
 decide +kernel
def pointBounds41060 : List (Nat × Nat × Nat) := [(5385801728,109194848259115,109195233959263)]
theorem point_links_checked41060 : (cuts41060.take 1).map (fun c => (5385748481-1+2*2^10*c.k,109194726905234+c.lower,109195112605308+c.upper)) = pointBounds41060 := by
 decide +kernel
def cuts41061 : List PrefixCut := [⟨45,214688969,214689094⟩,
⟨64,305517815,305517993⟩]
theorem checked41061 : checkPrefixCuts (2^48) 5385879553 10 Manual.Count131072.C041061.packed 64 cuts41061 = true := by
 decide +kernel
def pointBounds41061 : List (Nat × Nat × Nat) := [(5385971712,109195241475138,109195627175517)]
theorem point_links_checked41061 : (cuts41061.take 1).map (fun c => (5385879553-1+2*2^10*c.k,109195026786169+c.lower,109195412486423+c.upper)) = pointBounds41061 := by
 decide +kernel
def cuts41062 : List PrefixCut := [⟨64,307757570,307757746⟩]
theorem checked41062 : checkPrefixCuts (2^48) 5386010625 10 Manual.Count131072.C041062.packed 64 cuts41062 = true := by
 decide +kernel
def pointBounds41062 : List (Nat × Nat × Nat) := [(5386141696,109195640061554,109196025762162)]
theorem point_links_checked41062 : (cuts41062.take 1).map (fun c => (5386010625-1+2*2^10*c.k,109195332303984+c.lower,109195718004416+c.upper)) = pointBounds41062 := by
 decide +kernel
def cuts41063 : List PrefixCut := [⟨64,309788123,309788308⟩]
theorem checked41063 : checkPrefixCuts (2^48) 5386141697 10 Manual.Count131072.C041063.packed 64 cuts41063 = true := by
 decide +kernel
def cuts41064 : List PrefixCut := [⟨19,90144423,90144473⟩,
⟨64,303980074,303980248⟩]
theorem checked41064 : checkPrefixCuts (2^48) 5386272769 10 Manual.Count131072.C041064.packed 64 cuts41064 = true := by
 decide +kernel
def pointBounds41064 : List (Nat × Nat × Nat) := [(5386311680,109196039994100,109196425694943)]
theorem point_links_checked41064 : (cuts41064.take 1).map (fun c => (5386272769-1+2*2^10*c.k,109195949849677+c.lower,109196335550470+c.upper)) = pointBounds41064 := by
 decide +kernel
def cuts41065 : List PrefixCut := [⟨38,181642469,181642574⟩,
⟨64,306428695,306428875⟩]
theorem checked41065 : checkPrefixCuts (2^48) 5386403841 10 Manual.Count131072.C041065.packed 64 cuts41065 = true := by
 decide +kernel
def pointBounds41065 : List (Nat × Nat × Nat) := [(5386481664,109196435472220,109196821173292)]
theorem point_links_checked41065 : (cuts41065.take 1).map (fun c => (5386403841-1+2*2^10*c.k,109196253829751+c.lower,109196639530718+c.upper)) = pointBounds41065 := by
 decide +kernel
def cuts41066 : List PrefixCut := [⟨57,268171177,268171336⟩,
⟨64,300673214,300673393⟩]
theorem checked41066 : checkPrefixCuts (2^48) 5386534913 10 Manual.Count131072.C041066.packed 64 cuts41066 = true := by
 decide +kernel
def pointBounds41066 : List (Nat × Nat × Nat) := [(5386651648,109196828429623,109197214130929)]
theorem point_links_checked41066 : (cuts41066.take 1).map (fun c => (5386534913-1+2*2^10*c.k,109196560258446+c.lower,109196945959593+c.upper)) = pointBounds41066 := by
 decide +kernel
def cuts41067 : List PrefixCut := [⟨64,303957843,303958024⟩]
theorem checked41067 : checkPrefixCuts (2^48) 5386665985 10 Manual.Count131072.C041067.packed 64 cuts41067 = true := by
 decide +kernel
def cuts41068 : List PrefixCut := [⟨12,56432828,56432862⟩,
⟨64,303532431,303532608⟩]
theorem checked41068 : checkPrefixCuts (2^48) 5386797057 10 Manual.Count131072.C041068.packed 64 cuts41068 = true := by
 decide +kernel
def pointBounds41068 : List (Nat × Nat × Nat) := [(5386821632,109197221322331,109197607023872)]
theorem point_links_checked41068 : (cuts41068.take 1).map (fun c => (5386797057-1+2*2^10*c.k,109197164889503+c.lower,109197550591010+c.upper)) = pointBounds41068 := by
 decide +kernel
def cuts41069 : List PrefixCut := [⟨31,146878001,146878088⟩,
⟨64,304413339,304413518⟩]
theorem checked41069 : checkPrefixCuts (2^48) 5386928129 10 Manual.Count131072.C041069.packed 64 cuts41069 = true := by
 decide +kernel
def pointBounds41069 : List (Nat × Nat × Nat) := [(5386991616,109197615299935,109198001001706)]
theorem point_links_checked41069 : (cuts41069.take 1).map (fun c => (5386928129-1+2*2^10*c.k,109197468421934+c.lower,109197854123618+c.upper)) = pointBounds41069 := by
 decide +kernel
def cuts41070 : List PrefixCut := [⟨50,236952391,236952538⟩,
⟨64,302733957,302734144⟩]
theorem checked41070 : checkPrefixCuts (2^48) 5387059201 10 Manual.Count131072.C041070.packed 64 cuts41070 = true := by
 decide +kernel
def pointBounds41070 : List (Nat × Nat × Nat) := [(5387161600,109198009787664,109198395489674)]
theorem point_links_checked41070 : (cuts41070.take 1).map (fun c => (5387059201-1+2*2^10*c.k,109197772835273+c.lower,109198158537136+c.upper)) = pointBounds41070 := by
 decide +kernel
def cuts41071 : List PrefixCut := [⟨64,308735138,308735320⟩]
theorem checked41071 : checkPrefixCuts (2^48) 5387190273 10 Manual.Count131072.C041071.packed 64 cuts41071 = true := by
 decide +kernel
def cuts41072 : List PrefixCut := [⟨5,23615916,23615931⟩,
⟨64,307473706,307473889⟩]
theorem checked41072 : checkPrefixCuts (2^48) 5387321345 10 Manual.Count131072.C041072.packed 64 cuts41072 = true := by
 decide +kernel
def pointBounds41072 : List (Nat × Nat × Nat) := [(5387331584,109198407920284,109198793622531)]
theorem point_links_checked41072 : (cuts41072.take 1).map (fun c => (5387321345-1+2*2^10*c.k,109198384304368+c.lower,109198770006600+c.upper)) = pointBounds41072 := by
 decide +kernel
def cuts41073 : List PrefixCut := [⟨24,111911239,111911304⟩,
⟨64,301823659,301823838⟩]
theorem checked41073 : checkPrefixCuts (2^48) 5387452417 10 Manual.Count131072.C041073.packed 64 cuts41073 = true := by
 decide +kernel
def pointBounds41073 : List (Nat × Nat × Nat) := [(5387501568,109198803689313,109199189391793)]
theorem point_links_checked41073 : (cuts41073.take 1).map (fun c => (5387452417-1+2*2^10*c.k,109198691778074+c.lower,109199077480489+c.upper)) = pointBounds41073 := by
 decide +kernel
def cuts41074 : List PrefixCut := [⟨43,205582834,205582956⟩,
⟨64,306675071,306675252⟩]
theorem checked41074 : checkPrefixCuts (2^48) 5387583489 10 Manual.Count131072.C041074.packed 64 cuts41074 = true := by
 decide +kernel
def pointBounds41074 : List (Nat × Nat × Nat) := [(5387671552,109199199184567,109199584887283)]
theorem point_links_checked41074 : (cuts41074.take 1).map (fun c => (5387583489-1+2*2^10*c.k,109198993601733+c.lower,109199379304327+c.upper)) = pointBounds41074 := by
 decide +kernel
def cuts41075 : List PrefixCut := [⟨62,295801117,295801297⟩,
⟨64,305048055,305048240⟩]
theorem checked41075 : checkPrefixCuts (2^48) 5387714561 10 Manual.Count131072.C041075.packed 64 cuts41075 = true := by
 decide +kernel
def pointBounds41075 : List (Nat × Nat × Nat) := [(5387841536,109199596077921,109199981780876)]
theorem point_links_checked41075 : (cuts41075.take 1).map (fun c => (5387714561-1+2*2^10*c.k,109199300276804+c.lower,109199685979579+c.upper)) = pointBounds41075 := by
 decide +kernel
def cuts41076 : List PrefixCut := [⟨64,303630104,303630282⟩]
theorem checked41076 : checkPrefixCuts (2^48) 5387845633 10 Manual.Count131072.C041076.packed 64 cuts41076 = true := by
 decide +kernel
def cuts41077 : List PrefixCut := [⟨17,82645466,82645517⟩,
⟨64,306078075,306078257⟩]
theorem checked41077 : checkPrefixCuts (2^48) 5387976705 10 Manual.Count131072.C041077.packed 64 cuts41077 = true := by
 decide +kernel
def pointBounds41077 : List (Nat × Nat × Nat) := [(5388011520,109199991600429,109200377303618)]
theorem point_links_checked41077 : (cuts41077.take 1).map (fun c => (5387976705-1+2*2^10*c.k,109199908954963+c.lower,109200294658101+c.upper)) = pointBounds41077 := by
 decide +kernel
def cuts41078 : List PrefixCut := [⟨36,169152068,169152168⟩,
⟨64,303458626,303458807⟩]
theorem checked41078 : checkPrefixCuts (2^48) 5388107777 10 Manual.Count131072.C041078.packed 64 cuts41078 = true := by
 decide +kernel
def pointBounds41078 : List (Nat × Nat × Nat) := [(5388181504,109200384185106,109200769888526)]
theorem point_links_checked41078 : (cuts41078.take 1).map (fun c => (5388107777-1+2*2^10*c.k,109200215033038+c.lower,109200600736358+c.upper)) = pointBounds41078 := by
 decide +kernel
def cuts41079 : List PrefixCut := [⟨55,264011910,264012064⟩,
⟨64,305906443,305906623⟩]
theorem checked41079 : checkPrefixCuts (2^48) 5388238849 10 Manual.Count131072.C041079.packed 64 cuts41079 = true := by
 decide +kernel
def pointBounds41079 : List (Nat × Nat × Nat) := [(5388351488,109200782503574,109201168207229)]
theorem point_links_checked41079 : (cuts41079.take 1).map (fun c => (5388238849-1+2*2^10*c.k,109200518491664+c.lower,109200904195165+c.upper)) = pointBounds41079 := by
 decide +kernel
def cuts41080 : List PrefixCut := [⟨64,305637812,305637992⟩]
theorem checked41080 : checkPrefixCuts (2^48) 5388369921 10 Manual.Count131072.C041080.packed 64 cuts41080 = true := by
 decide +kernel
def cuts41081 : List PrefixCut := [⟨10,47325921,47325948⟩,
⟨64,304846833,304847013⟩]
theorem checked41081 : checkPrefixCuts (2^48) 5388500993 10 Manual.Count131072.C041081.packed 64 cuts41081 = true := by
 decide +kernel
def pointBounds41081 : List (Nat × Nat × Nat) := [(5388521472,109201177361840,109201563065728)]
theorem point_links_checked41081 : (cuts41081.take 1).map (fun c => (5388500993-1+2*2^10*c.k,109201130035919+c.lower,109201515739780+c.upper)) = pointBounds41081 := by
 decide +kernel
def cuts41082 : List PrefixCut := [⟨29,142130502,142130585⟩,
⟨64,308548085,308548262⟩]
theorem checked41082 : checkPrefixCuts (2^48) 5388632065 10 Manual.Count131072.C041082.packed 64 cuts41082 = true := by
 decide +kernel
def pointBounds41082 : List (Nat × Nat × Nat) := [(5388691456,109201577013254,109201962717378)]
theorem point_links_checked41082 : (cuts41082.take 1).map (fun c => (5388632065-1+2*2^10*c.k,109201434882752+c.lower,109201820586793+c.upper)) = pointBounds41082 := by
 decide +kernel
def cuts41083 : List PrefixCut := [⟨48,226639822,226639956⟩,
⟨64,301854711,301854889⟩]
theorem checked41083 : checkPrefixCuts (2^48) 5388763137 10 Manual.Count131072.C041083.packed 64 cuts41083 = true := by
 decide +kernel
def pointBounds41083 : List (Nat × Nat × Nat) := [(5388861440,109201970070659,109202355775011)]
theorem point_links_checked41083 : (cuts41083.take 1).map (fun c => (5388763137-1+2*2^10*c.k,109201743430837+c.lower,109202129135055+c.upper)) = pointBounds41083 := by
 decide +kernel
def cuts41084 : List PrefixCut := [⟨64,308846426,308846612⟩]
theorem checked41084 : checkPrefixCuts (2^48) 5388894209 10 Manual.Count131072.C041084.packed 64 cuts41084 = true := by
 decide +kernel
def cuts41085 : List PrefixCut := [⟨3,14206860,14206868⟩,
⟨64,302310115,302310295⟩]
theorem checked41085 : checkPrefixCuts (2^48) 5389025281 10 Manual.Count131072.C041085.packed 64 cuts41085 = true := by
 decide +kernel
def pointBounds41085 : List (Nat × Nat × Nat) := [(5389031424,109202368338834,109202754043424)]
theorem point_links_checked41085 : (cuts41085.take 1).map (fun c => (5389025281-1+2*2^10*c.k,109202354131974+c.lower,109202739836556+c.upper)) = pointBounds41085 := by
 decide +kernel
def cuts41086 : List PrefixCut := [⟨22,107854213,107854277⟩,
⟨64,305070974,305071151⟩]
theorem checked41086 : checkPrefixCuts (2^48) 5389156353 10 Manual.Count131072.C041086.packed 64 cuts41086 = true := by
 decide +kernel
def pointBounds41086 : List (Nat × Nat × Nat) := [(5389201408,109202764296302,109203150001128)]
theorem point_links_checked41086 : (cuts41086.take 1).map (fun c => (5389156353-1+2*2^10*c.k,109202656442089+c.lower,109203042146851+c.upper)) = pointBounds41086 := by
 decide +kernel
def cuts41087 : List PrefixCut := [⟨41,192774233,192774345⟩,
⟨64,303183272,303183450⟩]
theorem checked41087 : checkPrefixCuts (2^48) 5389287425 10 Manual.Count131072.C041087.packed 64 cuts41087 = true := by
 decide +kernel
def pointBounds41087 : List (Nat × Nat × Nat) := [(5389371392,109203154287296,109203539992347)]
theorem point_links_checked41087 : (cuts41087.take 1).map (fun c => (5389287425-1+2*2^10*c.k,109202961513063+c.lower,109203347218002+c.upper)) = pointBounds41087 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S5.B000033
