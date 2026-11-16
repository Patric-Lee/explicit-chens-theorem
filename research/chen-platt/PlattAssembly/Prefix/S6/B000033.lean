import PlattAssemblyKernel
import PlattCertificates.Count131072.C051056
import PlattCertificates.Count131072.C051057
import PlattCertificates.Count131072.C051058
import PlattCertificates.Count131072.C051059
import PlattCertificates.Count131072.C051060
import PlattCertificates.Count131072.C051061
import PlattCertificates.Count131072.C051062
import PlattCertificates.Count131072.C051063
import PlattCertificates.Count131072.C051064
import PlattCertificates.Count131072.C051065
import PlattCertificates.Count131072.C051066
import PlattCertificates.Count131072.C051067
import PlattCertificates.Count131072.C051068
import PlattCertificates.Count131072.C051069
import PlattCertificates.Count131072.C051070
import PlattCertificates.Count131072.C051071
import PlattCertificates.Count131072.C051072
import PlattCertificates.Count131072.C051073
import PlattCertificates.Count131072.C051074
import PlattCertificates.Count131072.C051075
import PlattCertificates.Count131072.C051076
import PlattCertificates.Count131072.C051077
import PlattCertificates.Count131072.C051078
import PlattCertificates.Count131072.C051079
import PlattCertificates.Count131072.C051080
import PlattCertificates.Count131072.C051081
import PlattCertificates.Count131072.C051082
import PlattCertificates.Count131072.C051083
import PlattCertificates.Count131072.C051084
import PlattCertificates.Count131072.C051085
import PlattCertificates.Count131072.C051086
import PlattCertificates.Count131072.C051087
namespace ChenEffective.PlattWindow.Assembly.Prefix.S6.B000033
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts51056 : List PrefixCut := [⟨13,48804423,48804450⟩,
⟨64,242254704,242254842⟩]
theorem checked51056 : checkPrefixCuts (2^48) 6695944193 10 Manual.Count131072.C051056.packed 64 cuts51056 = true := by
 decide +kernel
def pointBounds51056 : List (Nat × Nat × Nat) := [(6695970816,111916926136572,111917313406579)]
theorem point_links_checked51056 : (cuts51056.take 1).map (fun c => (6695944193-1+2*2^10*c.k,111916877332149+c.lower,111917264602129+c.upper)) = pointBounds51056 := by
 decide +kernel
def cuts51057 : List PrefixCut := [⟨52,198785724,198785838⟩,
⟨64,243426955,243427094⟩]
theorem checked51057 : checkPrefixCuts (2^48) 6696075265 10 Manual.Count131072.C051057.packed 64 cuts51057 = true := by
 decide +kernel
def pointBounds51057 : List (Nat × Nat × Nat) := [(6696181760,111917318372577,111917705642809)]
theorem point_links_checked51057 : (cuts51057.take 1).map (fun c => (6696075265-1+2*2^10*c.k,111917119586853+c.lower,111917506856971+c.upper)) = pointBounds51057 := by
 decide +kernel
def cuts51058 : List PrefixCut := [⟨64,244935430,244935569⟩]
theorem checked51058 : checkPrefixCuts (2^48) 6696206337 10 Manual.Count131072.C051058.packed 64 cuts51058 = true := by
 decide +kernel
def cuts51059 : List PrefixCut := [⟨27,100881559,100881619⟩,
⟨64,240895385,240895524⟩]
theorem checked51059 : checkPrefixCuts (2^48) 6696337409 10 Manual.Count131072.C051059.packed 64 cuts51059 = true := by
 decide +kernel
def pointBounds51059 : List (Nat × Nat × Nat) := [(6696392704,111917708830797,111918096101253)]
theorem point_links_checked51059 : (cuts51059.take 1).map (fun c => (6696337409-1+2*2^10*c.k,111917607949238+c.lower,111917995219634+c.upper)) = pointBounds51059 := by
 decide +kernel
def cuts51060 : List PrefixCut := [⟨64,245976655,245976791⟩]
theorem checked51060 : checkPrefixCuts (2^48) 6696468481 10 Manual.Count131072.C051060.packed 64 cuts51060 = true := by
 decide +kernel
def cuts51061 : List PrefixCut := [⟨2,6599102,6599106⟩,
⟨64,241684580,241684720⟩]
theorem checked51061 : checkPrefixCuts (2^48) 6696599553 10 Manual.Count131072.C051061.packed 64 cuts51061 = true := by
 decide +kernel
def pointBounds51061 : List (Nat × Nat × Nat) := [(6696603648,111918101420380,111918488691055)]
theorem point_links_checked51061 : (cuts51061.take 1).map (fun c => (6696599553-1+2*2^10*c.k,111918094821278+c.lower,111918482091949+c.upper)) = pointBounds51061 := by
 decide +kernel
def cuts51062 : List PrefixCut := [⟨41,160181753,160181843⟩,
⟨64,245336587,245336725⟩]
theorem checked51062 : checkPrefixCuts (2^48) 6696730625 10 Manual.Count131072.C051062.packed 64 cuts51062 = true := by
 decide +kernel
def pointBounds51062 : List (Nat × Nat × Nat) := [(6696814592,111918496687611,111918883958512)]
theorem point_links_checked51062 : (cuts51062.take 1).map (fun c => (6696730625-1+2*2^10*c.k,111918336505858+c.lower,111918723776669+c.upper)) = pointBounds51062 := by
 decide +kernel
def cuts51063 : List PrefixCut := [⟨64,244028788,244028925⟩]
theorem checked51063 : checkPrefixCuts (2^48) 6696861697 10 Manual.Count131072.C051063.packed 64 cuts51063 = true := by
 decide +kernel
def cuts51064 : List PrefixCut := [⟨16,60186876,60186910⟩,
⟨64,241334142,241334281⟩]
theorem checked51064 : checkPrefixCuts (2^48) 6696992769 10 Manual.Count131072.C051064.packed 64 cuts51064 = true := by
 decide +kernel
def pointBounds51064 : List (Nat × Nat × Nat) := [(6697025536,111918886058109,111919273329229)]
theorem point_links_checked51064 : (cuts51064.take 1).map (fun c => (6696992769-1+2*2^10*c.k,111918825871233+c.lower,111919213142319+c.upper)) = pointBounds51064 := by
 decide +kernel
def cuts51065 : List PrefixCut := [⟨55,207286357,207286475⟩,
⟨64,241035207,241035345⟩]
theorem checked51065 : checkPrefixCuts (2^48) 6697123841 10 Manual.Count131072.C051065.packed 64 cuts51065 = true := by
 decide +kernel
def pointBounds51065 : List (Nat × Nat × Nat) := [(6697236480,111919274491732,111919661763075)]
theorem point_links_checked51065 : (cuts51065.take 1).map (fun c => (6697123841-1+2*2^10*c.k,111919067205375+c.lower,111919454476600+c.upper)) = pointBounds51065 := by
 decide +kernel
def cuts51066 : List PrefixCut := [⟨64,241660928,241661066⟩]
theorem checked51066 : checkPrefixCuts (2^48) 6697254913 10 Manual.Count131072.C051066.packed 64 cuts51066 = true := by
 decide +kernel
def cuts51067 : List PrefixCut := [⟨30,115323143,115323204⟩,
⟨64,243799597,243799733⟩]
theorem checked51067 : checkPrefixCuts (2^48) 6697385985 10 Manual.Count131072.C051067.packed 64 cuts51067 = true := by
 decide +kernel
def pointBounds51067 : List (Nat × Nat × Nat) := [(6697447424,111919665224653,111920052496215)]
theorem point_links_checked51067 : (cuts51067.take 1).map (fun c => (6697385985-1+2*2^10*c.k,111919549901510+c.lower,111919937173011+c.upper)) = pointBounds51067 := by
 decide +kernel
def cuts51068 : List PrefixCut := [⟨64,244341162,244341298⟩]
theorem checked51068 : checkPrefixCuts (2^48) 6697517057 10 Manual.Count131072.C051068.packed 64 cuts51068 = true := by
 decide +kernel
def cuts51069 : List PrefixCut := [⟨5,19415965,19415976⟩,
⟨64,245639156,245639295⟩]
theorem checked51069 : checkPrefixCuts (2^48) 6697648129 10 Manual.Count131072.C051069.packed 64 cuts51069 = true := by
 decide +kernel
def pointBounds51069 : List (Nat × Nat × Nat) := [(6697658368,111920057458234,111920444730018)]
theorem point_links_checked51069 : (cuts51069.take 1).map (fun c => (6697648129-1+2*2^10*c.k,111920038042269+c.lower,111920425314042+c.upper)) = pointBounds51069 := by
 decide +kernel
def cuts51070 : List PrefixCut := [⟨44,167721085,167721178⟩,
⟨64,244121472,244121607⟩]
theorem checked51070 : checkPrefixCuts (2^48) 6697779201 10 Manual.Count131072.C051070.packed 64 cuts51070 = true := by
 decide +kernel
def pointBounds51070 : List (Nat × Nat × Nat) := [(6697869312,111920451402510,111920838674515)]
theorem point_links_checked51070 : (cuts51070.take 1).map (fun c => (6697779201-1+2*2^10*c.k,111920283681425+c.lower,111920670953337+c.upper)) = pointBounds51070 := by
 decide +kernel
def cuts51071 : List PrefixCut := [⟨64,242477766,242477903⟩]
theorem checked51071 : checkPrefixCuts (2^48) 6697910273 10 Manual.Count131072.C051071.packed 64 cuts51071 = true := by
 decide +kernel
def cuts51072 : List PrefixCut := [⟨19,73498823,73498864⟩,
⟨64,246381157,246381298⟩]
theorem checked51072 : checkPrefixCuts (2^48) 6698041345 10 Manual.Count131072.C051072.packed 64 cuts51072 = true := by
 decide +kernel
def pointBounds51072 : List (Nat × Nat × Nat) := [(6698080256,111920843779486,111921231051711)]
theorem point_links_checked51072 : (cuts51072.take 1).map (fun c => (6698041345-1+2*2^10*c.k,111920770280663+c.lower,111921157552847+c.upper)) = pointBounds51072 := by
 decide +kernel
def cuts51073 : List PrefixCut := [⟨58,219986561,219986687⟩,
⟨64,243056561,243056699⟩]
theorem checked51073 : checkPrefixCuts (2^48) 6698172417 10 Manual.Count131072.C051073.packed 64 cuts51073 = true := by
 decide +kernel
def pointBounds51073 : List (Nat × Nat × Nat) := [(6698291200,111921236648381,111921623920832)]
theorem point_links_checked51073 : (cuts51073.take 1).map (fun c => (6698172417-1+2*2^10*c.k,111921016661820+c.lower,111921403934145+c.upper)) = pointBounds51073 := by
 decide +kernel
def cuts51074 : List PrefixCut := [⟨64,241160870,241161011⟩]
theorem checked51074 : checkPrefixCuts (2^48) 6698303489 10 Manual.Count131072.C051074.packed 64 cuts51074 = true := by
 decide +kernel
def cuts51075 : List PrefixCut := [⟨33,126524585,126524659⟩,
⟨64,242836972,242837113⟩]
theorem checked51075 : checkPrefixCuts (2^48) 6698434561 10 Manual.Count131072.C051075.packed 64 cuts51075 = true := by
 decide +kernel
def pointBounds51075 : List (Nat × Nat × Nat) := [(6698502144,111921627403836,111922014676514)]
theorem point_links_checked51075 : (cuts51075.take 1).map (fun c => (6698434561-1+2*2^10*c.k,111921500879251+c.lower,111921888151855+c.upper)) = pointBounds51075 := by
 decide +kernel
def cuts51076 : List PrefixCut := [⟨64,244933181,244933321⟩]
theorem checked51076 : checkPrefixCuts (2^48) 6698565633 10 Manual.Count131072.C051076.packed 64 cuts51076 = true := by
 decide +kernel
def cuts51077 : List PrefixCut := [⟨8,29707646,29707662⟩,
⟨64,242575354,242575489⟩]
theorem checked51077 : checkPrefixCuts (2^48) 6698696705 10 Manual.Count131072.C051077.packed 64 cuts51077 = true := by
 decide +kernel
def pointBounds51077 : List (Nat × Nat × Nat) := [(6698713088,111922018357050,111922405629951)]
theorem point_links_checked51077 : (cuts51077.take 1).map (fun c => (6698696705-1+2*2^10*c.k,111921988649404+c.lower,111922375922289+c.upper)) = pointBounds51077 := by
 decide +kernel
def cuts51078 : List PrefixCut := [⟨47,177653068,177653168⟩,
⟨64,240385670,240385806⟩]
theorem checked51078 : checkPrefixCuts (2^48) 6698827777 10 Manual.Count131072.C051078.packed 64 cuts51078 = true := by
 decide +kernel
def pointBounds51078 : List (Nat × Nat × Nat) := [(6698924032,111922408877826,111922796150946)]
theorem point_links_checked51078 : (cuts51078.take 1).map (fun c => (6698827777-1+2*2^10*c.k,111922231224758+c.lower,111922618497778+c.upper)) = pointBounds51078 := by
 decide +kernel
def cuts51079 : List PrefixCut := [⟨64,239708666,239708805⟩]
theorem checked51079 : checkPrefixCuts (2^48) 6698958849 10 Manual.Count131072.C051079.packed 64 cuts51079 = true := by
 decide +kernel
def cuts51080 : List PrefixCut := [⟨22,82310808,82310853⟩,
⟨64,238821642,238821775⟩]
theorem checked51080 : checkPrefixCuts (2^48) 6699089921 10 Manual.Count131072.C051080.packed 64 cuts51080 = true := by
 decide +kernel
def pointBounds51080 : List (Nat × Nat × Nat) := [(6699134976,111922793629902,111923180903242)]
theorem point_links_checked51080 : (cuts51080.take 1).map (fun c => (6699089921-1+2*2^10*c.k,111922711319094+c.lower,111923098592389+c.upper)) = pointBounds51080 := by
 decide +kernel
def cuts51081 : List PrefixCut := [⟨61,234489454,234489587⟩,
⟨64,245119315,245119454⟩]
theorem checked51081 : checkPrefixCuts (2^48) 6699220993 10 Manual.Count131072.C051081.packed 64 cuts51081 = true := by
 decide +kernel
def pointBounds51081 : List (Nat × Nat × Nat) := [(6699345920,111923184630190,111923571903751)]
theorem point_links_checked51081 : (cuts51081.take 1).map (fun c => (6699220993-1+2*2^10*c.k,111922950140736+c.lower,111923337414164+c.upper)) = pointBounds51081 := by
 decide +kernel
def cuts51082 : List PrefixCut := [⟨64,242509572,242509712⟩]
theorem checked51082 : checkPrefixCuts (2^48) 6699352065 10 Manual.Count131072.C051082.packed 64 cuts51082 = true := by
 decide +kernel
def cuts51083 : List PrefixCut := [⟨36,137428410,137428485⟩,
⟨64,244017364,244017502⟩]
theorem checked51083 : checkPrefixCuts (2^48) 6699483137 10 Manual.Count131072.C051083.packed 64 cuts51083 = true := by
 decide +kernel
def pointBounds51083 : List (Nat × Nat × Nat) := [(6699556864,111923575198033,111923962471815)]
theorem point_links_checked51083 : (cuts51083.take 1).map (fun c => (6699483137-1+2*2^10*c.k,111923437769623+c.lower,111923825043330+c.upper)) = pointBounds51083 := by
 decide +kernel
def cuts51084 : List PrefixCut := [⟨64,243046275,243046415⟩]
theorem checked51084 : checkPrefixCuts (2^48) 6699614209 10 Manual.Count131072.C051084.packed 64 cuts51084 = true := by
 decide +kernel
def cuts51085 : List PrefixCut := [⟨11,40878365,40878387⟩,
⟨64,246024394,246024529⟩]
theorem checked51085 : checkPrefixCuts (2^48) 6699745281 10 Manual.Count131072.C051085.packed 64 cuts51085 = true := by
 decide +kernel
def pointBounds51085 : List (Nat × Nat × Nat) := [(6699767808,111923965711627,111924352985634)]
theorem point_links_checked51085 : (cuts51085.take 1).map (fun c => (6699745281-1+2*2^10*c.k,111923924833262+c.lower,111924312107247+c.upper)) = pointBounds51085 := by
 decide +kernel
def cuts51086 : List PrefixCut := [⟨50,187329882,187329989⟩,
⟨64,241398325,241398463⟩]
theorem checked51086 : checkPrefixCuts (2^48) 6699876353 10 Manual.Count131072.C051086.packed 64 cuts51086 = true := by
 decide +kernel
def pointBounds51086 : List (Nat × Nat × Nat) := [(6699978752,111924358187538,111924745461765)]
theorem point_links_checked51086 : (cuts51086.take 1).map (fun c => (6699876353-1+2*2^10*c.k,111924170857656+c.lower,111924558131776+c.upper)) = pointBounds51086 := by
 decide +kernel
def cuts51087 : List PrefixCut := [⟨64,245384601,245384740⟩]
theorem checked51087 : checkPrefixCuts (2^48) 6700007425 10 Manual.Count131072.C051087.packed 64 cuts51087 = true := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S6.B000033
