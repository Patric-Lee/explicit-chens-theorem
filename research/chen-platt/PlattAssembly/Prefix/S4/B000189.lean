import PlattAssemblyKernel
import PlattCertificates.Count131072.C036048
import PlattCertificates.Count131072.C036049
import PlattCertificates.Count131072.C036050
import PlattCertificates.Count131072.C036051
import PlattCertificates.Count131072.C036052
import PlattCertificates.Count131072.C036053
import PlattCertificates.Count131072.C036054
import PlattCertificates.Count131072.C036055
import PlattCertificates.Count131072.C036056
import PlattCertificates.Count131072.C036057
import PlattCertificates.Count131072.C036058
import PlattCertificates.Count131072.C036059
import PlattCertificates.Count131072.C036060
import PlattCertificates.Count131072.C036061
import PlattCertificates.Count131072.C036062
import PlattCertificates.Count131072.C036063
import PlattCertificates.Count131072.C036064
import PlattCertificates.Count131072.C036065
import PlattCertificates.Count131072.C036066
import PlattCertificates.Count131072.C036067
import PlattCertificates.Count131072.C036068
import PlattCertificates.Count131072.C036069
import PlattCertificates.Count131072.C036070
import PlattCertificates.Count131072.C036071
import PlattCertificates.Count131072.C036072
import PlattCertificates.Count131072.C036073
import PlattCertificates.Count131072.C036074
import PlattCertificates.Count131072.C036075
import PlattCertificates.Count131072.C036076
import PlattCertificates.Count131072.C036077
import PlattCertificates.Count131072.C036078
import PlattCertificates.Count131072.C036079
namespace ChenEffective.PlattWindow.Assembly.Prefix.S4.B000189
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts36048 : List PrefixCut := [⟨12,64582655,64582696⟩,
⟨64,350825687,350825907⟩]
theorem checked36048 : checkPrefixCuts (2^48) 4728815617 10 Manual.Count131072.C036048.packed 64 cuts36048 = true := by
 decide +kernel
def pointBounds36048 : List (Nat × Nat × Nat) := [(4728840192,107556014173421,107556398886948)]
theorem point_links_checked36048 : (cuts36048.take 1).map (fun c => (4728815617-1+2*2^10*c.k,107555949590766+c.lower,107556334304252+c.upper)) = pointBounds36048 := by
 decide +kernel
def cuts36049 : List PrefixCut := [⟨21,111424094,111424160⟩,
⟨64,349685037,349685246⟩]
theorem checked36049 : checkPrefixCuts (2^48) 4728946689 10 Manual.Count131072.C036049.packed 64 cuts36049 = true := by
 decide +kernel
def pointBounds36049 : List (Nat × Nat × Nat) := [(4728989696,107556411840547,107556796554319)]
theorem point_links_checked36049 : (cuts36049.take 1).map (fun c => (4728946689-1+2*2^10*c.k,107556300416453+c.lower,107556685130159+c.upper)) = pointBounds36049 := by
 decide +kernel
def cuts36050 : List PrefixCut := [⟨30,162607704,162607803⟩,
⟨64,349139698,349139908⟩]
theorem checked36050 : checkPrefixCuts (2^48) 4729077761 10 Manual.Count131072.C036050.packed 64 cuts36050 = true := by
 decide +kernel
def pointBounds36050 : List (Nat × Nat × Nat) := [(4729139200,107556812709194,107557197423208)]
theorem point_links_checked36050 : (cuts36050.take 1).map (fun c => (4729077761-1+2*2^10*c.k,107556650101490+c.lower,107557034815405+c.upper)) = pointBounds36050 := by
 decide +kernel
def cuts36051 : List PrefixCut := [⟨39,210931381,210931514⟩,
⟨64,348891928,348892145⟩]
theorem checked36051 : checkPrefixCuts (2^48) 4729208833 10 Manual.Count131072.C036051.packed 64 cuts36051 = true := by
 decide +kernel
def pointBounds36051 : List (Nat × Nat × Nat) := [(4729288704,107557210172569,107557594886827)]
theorem point_links_checked36051 : (cuts36051.take 1).map (fun c => (4729208833-1+2*2^10*c.k,107556999241188+c.lower,107557383955313+c.upper)) = pointBounds36051 := by
 decide +kernel
def cuts36052 : List PrefixCut := [⟨48,259549792,259549952⟩,
⟨64,346680187,346680398⟩]
theorem checked36052 : checkPrefixCuts (2^48) 4729339905 10 Manual.Count131072.C036052.packed 64 cuts36052 = true := by
 decide +kernel
def pointBounds36052 : List (Nat × Nat × Nat) := [(4729438208,107557607682908,107557992397410)]
theorem point_links_checked36052 : (cuts36052.take 1).map (fun c => (4729339905-1+2*2^10*c.k,107557348133116+c.lower,107557732847458+c.upper)) = pointBounds36052 := by
 decide +kernel
def cuts36053 : List PrefixCut := [⟨57,312331319,312331514⟩,
⟨64,350955601,350955818⟩]
theorem checked36053 : checkPrefixCuts (2^48) 4729470977 10 Manual.Count131072.C036053.packed 64 cuts36053 = true := by
 decide +kernel
def pointBounds36053 : List (Nat × Nat × Nat) := [(4729587712,107558007144622,107558391859370)]
theorem point_links_checked36053 : (cuts36053.take 1).map (fun c => (4729470977-1+2*2^10*c.k,107557694813303+c.lower,107558079527856+c.upper)) = pointBounds36053 := by
 decide +kernel
def cuts36054 : List PrefixCut := [⟨64,349279555,349279766⟩]
theorem checked36054 : checkPrefixCuts (2^48) 4729602049 10 Manual.Count131072.C036054.packed 64 cuts36054 = true := by
 decide +kernel
def cuts36055 : List PrefixCut := [⟨2,10057488,10057494⟩,
⟨64,350400582,350400797⟩]
theorem checked36055 : checkPrefixCuts (2^48) 4729733121 10 Manual.Count131072.C036055.packed 64 cuts36055 = true := by
 decide +kernel
def pointBounds36055 : List (Nat × Nat × Nat) := [(4729737216,107558405105947,107558789820934)]
theorem point_links_checked36055 : (cuts36055.take 1).map (fun c => (4729733121-1+2*2^10*c.k,107558395048459+c.lower,107558779763440+c.upper)) = pointBounds36055 := by
 decide +kernel
def cuts36056 : List PrefixCut := [⟨11,60224121,60224157⟩,
⟨64,346760811,346761030⟩]
theorem checked36056 : checkPrefixCuts (2^48) 4729864193 10 Manual.Count131072.C036056.packed 64 cuts36056 = true := by
 decide +kernel
def pointBounds36056 : List (Nat × Nat × Nat) := [(4729886720,107558805673162,107559190388394)]
theorem point_links_checked36056 : (cuts36056.take 1).map (fun c => (4729864193-1+2*2^10*c.k,107558745449041+c.lower,107559130164237+c.upper)) = pointBounds36056 := by
 decide +kernel
def cuts36057 : List PrefixCut := [⟨20,106995809,106995880⟩,
⟨64,345858566,345858787⟩]
theorem checked36057 : checkPrefixCuts (2^48) 4729995265 10 Manual.Count131072.C036057.packed 64 cuts36057 = true := by
 decide +kernel
def pointBounds36057 : List (Nat × Nat × Nat) := [(4730036224,107559199205661,107559583921147)]
theorem point_links_checked36057 : (cuts36057.take 1).map (fun c => (4729995265-1+2*2^10*c.k,107559092209852+c.lower,107559476925267+c.upper)) = pointBounds36057 := by
 decide +kernel
def cuts36058 : List PrefixCut := [⟨29,157870665,157870763⟩,
⟨64,347634166,347634383⟩]
theorem checked36058 : checkPrefixCuts (2^48) 4730126337 10 Manual.Count131072.C036058.packed 64 cuts36058 = true := by
 decide +kernel
def pointBounds36058 : List (Nat × Nat × Nat) := [(4730185728,107559595939083,107559980654817)]
theorem point_links_checked36058 : (cuts36058.take 1).map (fun c => (4730126337-1+2*2^10*c.k,107559438068418+c.lower,107559822784054+c.upper)) = pointBounds36058 := by
 decide +kernel
def cuts36059 : List PrefixCut := [⟨38,202078007,202078131⟩,
⟨64,348041031,348041245⟩]
theorem checked36059 : checkPrefixCuts (2^48) 4730257409 10 Manual.Count131072.C036059.packed 64 cuts36059 = true := by
 decide +kernel
def pointBounds36059 : List (Nat × Nat × Nat) := [(4730335232,107559987780591,107560372496568)]
theorem point_links_checked36059 : (cuts36059.take 1).map (fun c => (4730257409-1+2*2^10*c.k,107559785702584+c.lower,107560170418437+c.upper)) = pointBounds36059 := by
 decide +kernel
def cuts36060 : List PrefixCut := [⟨47,257588226,257588385⟩,
⟨64,354814695,354814914⟩]
theorem checked36060 : checkPrefixCuts (2^48) 4730388481 10 Manual.Count131072.C036060.packed 64 cuts36060 = true := by
 decide +kernel
def pointBounds36060 : List (Nat × Nat × Nat) := [(4730484736,107560391331841,107560776048067)]
theorem point_links_checked36060 : (cuts36060.take 1).map (fun c => (4730388481-1+2*2^10*c.k,107560133743615+c.lower,107560518459682+c.upper)) = pointBounds36060 := by
 decide +kernel
def cuts36061 : List PrefixCut := [⟨56,307383122,307383313⟩,
⟨64,351413383,351413601⟩]
theorem checked36061 : checkPrefixCuts (2^48) 4730519553 10 Manual.Count131072.C036061.packed 64 cuts36061 = true := by
 decide +kernel
def pointBounds36061 : List (Nat × Nat × Nat) := [(4730634240,107560795941432,107561180657909)]
theorem point_links_checked36061 : (cuts36061.take 1).map (fun c => (4730519553-1+2*2^10*c.k,107560488558310+c.lower,107560873274596+c.upper)) = pointBounds36061 := by
 decide +kernel
def cuts36062 : List PrefixCut := [⟨64,350035110,350035322⟩]
theorem checked36062 : checkPrefixCuts (2^48) 4730650625 10 Manual.Count131072.C036062.packed 64 cuts36062 = true := by
 decide +kernel
def cuts36063 : List PrefixCut := [⟨1,4878884,4878887⟩,
⟨64,348359500,348359716⟩]
theorem checked36063 : checkPrefixCuts (2^48) 4730781697 10 Manual.Count131072.C036063.packed 64 cuts36063 = true := by
 decide +kernel
def pointBounds36063 : List (Nat × Nat × Nat) := [(4730783744,107561194885687,107561579602406)]
theorem point_links_checked36063 : (cuts36063.take 1).map (fun c => (4730781697-1+2*2^10*c.k,107561190006803+c.lower,107561574723519+c.upper)) = pointBounds36063 := by
 decide +kernel
def cuts36064 : List PrefixCut := [⟨10,55510539,55510571⟩,
⟨64,354061434,354061649⟩]
theorem checked36064 : checkPrefixCuts (2^48) 4730912769 10 Manual.Count131072.C036064.packed 64 cuts36064 = true := by
 decide +kernel
def pointBounds36064 : List (Nat × Nat × Nat) := [(4730933248,107561593876842,107561978593806)]
theorem point_links_checked36064 : (cuts36064.take 1).map (fun c => (4730912769-1+2*2^10*c.k,107561538366303+c.lower,107561923083235+c.upper)) = pointBounds36064 := by
 decide +kernel
def cuts36065 : List PrefixCut := [⟨19,102153015,102153078⟩,
⟨64,350719942,350720155⟩]
theorem checked36065 : checkPrefixCuts (2^48) 4731043841 10 Manual.Count131072.C036065.packed 64 cuts36065 = true := by
 decide +kernel
def pointBounds36065 : List (Nat × Nat × Nat) := [(4731082752,107561994580752,107562379297962)]
theorem point_links_checked36065 : (cuts36065.take 1).map (fun c => (4731043841-1+2*2^10*c.k,107561892427737+c.lower,107562277144884+c.upper)) = pointBounds36065 := by
 decide +kernel
def cuts36066 : List PrefixCut := [⟨28,150458549,150458643⟩,
⟨64,344522988,344523200⟩]
theorem checked36066 : checkPrefixCuts (2^48) 4731174913 10 Manual.Count131072.C036066.packed 64 cuts36066 = true := by
 decide +kernel
def pointBounds36066 : List (Nat × Nat × Nat) := [(4731232256,107562393606228,107562778323682)]
theorem point_links_checked36066 : (cuts36066.take 1).map (fun c => (4731174913-1+2*2^10*c.k,107562243147679+c.lower,107562627865039+c.upper)) = pointBounds36066 := by
 decide +kernel
def cuts36067 : List PrefixCut := [⟨37,202628154,202628275⟩,
⟨64,351295424,351295636⟩]
theorem checked36067 : checkPrefixCuts (2^48) 4731305985 10 Manual.Count131072.C036067.packed 64 cuts36067 = true := by
 decide +kernel
def pointBounds36067 : List (Nat × Nat × Nat) := [(4731381760,107562790298821,107563175016514)]
theorem point_links_checked36067 : (cuts36067.take 1).map (fun c => (4731305985-1+2*2^10*c.k,107562587670667+c.lower,107562972388239+c.upper)) = pointBounds36067 := by
 decide +kernel
def cuts36068 : List PrefixCut := [⟨46,253128961,253129113⟩,
⟨64,351226236,351226445⟩]
theorem checked36068 : checkPrefixCuts (2^48) 4731437057 10 Manual.Count131072.C036068.packed 64 cuts36068 = true := by
 decide +kernel
def pointBounds36068 : List (Nat × Nat × Nat) := [(4731531264,107563192095052,107563576812988)]
theorem point_links_checked36068 : (cuts36068.take 1).map (fun c => (4731437057-1+2*2^10*c.k,107562938966091+c.lower,107563323683875+c.upper)) = pointBounds36068 := by
 decide +kernel
def cuts36069 : List PrefixCut := [⟨55,304875991,304876174⟩,
⟨64,353120092,353120304⟩]
theorem checked36069 : checkPrefixCuts (2^48) 4731568129 10 Manual.Count131072.C036069.packed 64 cuts36069 = true := by
 decide +kernel
def pointBounds36069 : List (Nat × Nat × Nat) := [(4731680768,107563595068318,107563979786494)]
theorem point_links_checked36069 : (cuts36069.take 1).map (fun c => (4731568129-1+2*2^10*c.k,107563290192327+c.lower,107563674910320+c.upper)) = pointBounds36069 := by
 decide +kernel
def cuts36070 : List PrefixCut := [⟨64,346804786,346805002⟩]
theorem checked36070 : checkPrefixCuts (2^48) 4731699201 10 Manual.Count131072.C036070.packed 64 cuts36070 = true := by
 decide +kernel
def pointBounds36070 : List (Nat × Nat × Nat) := [(4731830272,107563990117205,107564374835626)]
theorem point_links_checked36070 : (cuts36070.take 1).map (fun c => (4731699201-1+2*2^10*c.k,107563643312419+c.lower,107564028030624+c.upper)) = pointBounds36070 := by
 decide +kernel
def cuts36071 : List PrefixCut := [⟨64,350602194,350602403⟩]
theorem checked36071 : checkPrefixCuts (2^48) 4731830273 10 Manual.Count131072.C036071.packed 64 cuts36071 = true := by
 decide +kernel
def cuts36072 : List PrefixCut := [⟨9,48181757,48181785⟩,
⟨64,354220939,354221154⟩]
theorem checked36072 : checkPrefixCuts (2^48) 4731961345 10 Manual.Count131072.C036072.packed 64 cuts36072 = true := by
 decide +kernel
def pointBounds36072 : List (Nat × Nat × Nat) := [(4731979776,107564388901156,107564773619814)]
theorem point_links_checked36072 : (cuts36072.take 1).map (fun c => (4731961345-1+2*2^10*c.k,107564340719399+c.lower,107564725438029+c.upper)) = pointBounds36072 := by
 decide +kernel
def cuts36073 : List PrefixCut := [⟨18,100108022,100108083⟩,
⟨64,354449072,354449287⟩]
theorem checked36073 : checkPrefixCuts (2^48) 4732092417 10 Manual.Count131072.C036073.packed 64 cuts36073 = true := by
 decide +kernel
def pointBounds36073 : List (Nat × Nat × Nat) := [(4732129280,107564795048360,107565179767266)]
theorem point_links_checked36073 : (cuts36073.take 1).map (fun c => (4732092417-1+2*2^10*c.k,107564694940338+c.lower,107565079659183+c.upper)) = pointBounds36073 := by
 decide +kernel
def cuts36074 : List PrefixCut := [⟨27,147510707,147510801⟩,
⟨64,345993123,345993340⟩]
theorem checked36074 : checkPrefixCuts (2^48) 4732223489 10 Manual.Count131072.C036074.packed 64 cuts36074 = true := by
 decide +kernel
def pointBounds36074 : List (Nat × Nat × Nat) := [(4732278784,107565196900117,107565581619271)]
theorem point_links_checked36074 : (cuts36074.take 1).map (fun c => (4732223489-1+2*2^10*c.k,107565049389410+c.lower,107565434108470+c.upper)) = pointBounds36074 := by
 decide +kernel
def cuts36075 : List PrefixCut := [⟨36,198003476,198003598⟩,
⟨64,350087542,350087758⟩]
theorem checked36075 : checkPrefixCuts (2^48) 4732354561 10 Manual.Count131072.C036075.packed 64 cuts36075 = true := by
 decide +kernel
def pointBounds36075 : List (Nat × Nat × Nat) := [(4732428288,107565593386009,107565978105408)]
theorem point_links_checked36075 : (cuts36075.take 1).map (fun c => (4732354561-1+2*2^10*c.k,107565395382533+c.lower,107565780101810+c.upper)) = pointBounds36075 := by
 decide +kernel
def cuts36076 : List PrefixCut := [⟨45,246471037,246471182⟩,
⟨64,354062713,354062924⟩]
theorem checked36076 : checkPrefixCuts (2^48) 4732485633 10 Manual.Count131072.C036076.packed 64 cuts36076 = true := by
 decide +kernel
def pointBounds36076 : List (Nat × Nat × Nat) := [(4732577792,107565991941112,107566376660750)]
theorem point_links_checked36076 : (cuts36076.take 1).map (fun c => (4732485633-1+2*2^10*c.k,107565745470075+c.lower,107566130189568+c.upper)) = pointBounds36076 := by
 decide +kernel
def cuts36077 : List PrefixCut := [⟨54,294221975,294222160⟩,
⟨64,346440162,346440379⟩]
theorem checked36077 : checkPrefixCuts (2^48) 4732616705 10 Manual.Count131072.C036077.packed 64 cuts36077 = true := by
 decide +kernel
def pointBounds36077 : List (Nat × Nat × Nat) := [(4732727296,107566393754763,107566778474652)]
theorem point_links_checked36077 : (cuts36077.take 1).map (fun c => (4732616705-1+2*2^10*c.k,107566099532788+c.lower,107566484252492+c.upper)) = pointBounds36077 := by
 decide +kernel
def cuts36078 : List PrefixCut := [⟨63,350177405,350177617⟩,
⟨64,355767796,355768012⟩]
theorem checked36078 : checkPrefixCuts (2^48) 4732747777 10 Manual.Count131072.C036078.packed 64 cuts36078 = true := by
 decide +kernel
def pointBounds36078 : List (Nat × Nat × Nat) := [(4732876800,107566796150355,107567180870488)]
theorem point_links_checked36078 : (cuts36078.take 1).map (fun c => (4732747777-1+2*2^10*c.k,107566445972950+c.lower,107566830692871+c.upper)) = pointBounds36078 := by
 decide +kernel
def cuts36079 : List PrefixCut := [⟨64,350108214,350108432⟩]
theorem checked36079 : checkPrefixCuts (2^48) 4732878849 10 Manual.Count131072.C036079.packed 64 cuts36079 = true := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S4.B000189
