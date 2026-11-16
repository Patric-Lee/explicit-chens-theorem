import PlattAssemblyKernel
import PlattCertificates.Count131072.C075152
import PlattCertificates.Count131072.C075153
import PlattCertificates.Count131072.C075154
import PlattCertificates.Count131072.C075155
import PlattCertificates.Count131072.C075156
import PlattCertificates.Count131072.C075157
import PlattCertificates.Count131072.C075158
import PlattCertificates.Count131072.C075159
import PlattCertificates.Count131072.C075160
import PlattCertificates.Count131072.C075161
import PlattCertificates.Count131072.C075162
import PlattCertificates.Count131072.C075163
import PlattCertificates.Count131072.C075164
import PlattCertificates.Count131072.C075165
import PlattCertificates.Count131072.C075166
import PlattCertificates.Count131072.C075167
import PlattCertificates.Count131072.C075168
import PlattCertificates.Count131072.C075169
import PlattCertificates.Count131072.C075170
import PlattCertificates.Count131072.C075171
import PlattCertificates.Count131072.C075172
import PlattCertificates.Count131072.C075173
import PlattCertificates.Count131072.C075174
import PlattCertificates.Count131072.C075175
import PlattCertificates.Count131072.C075176
import PlattCertificates.Count131072.C075177
import PlattCertificates.Count131072.C075178
import PlattCertificates.Count131072.C075179
import PlattCertificates.Count131072.C075180
import PlattCertificates.Count131072.C075181
import PlattCertificates.Count131072.C075182
import PlattCertificates.Count131072.C075183
namespace ChenEffective.PlattWindow.Assembly.Prefix.S8.B000161
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts75152 : List PrefixCut := [⟨10,25993026,25993038⟩,
⟨64,162498335,162498423⟩]
theorem checked75152 : checkPrefixCuts (2^48) 9854255105 10 Manual.Count131072.C075152.packed 64 cuts75152 = true := by
 decide +kernel
def pointBounds75152 : List (Nat × Nat × Nat) := [(9854275584,116683498552691,116683888574867)]
theorem point_links_checked75152 : (cuts75152.take 1).map (fun c => (9854255105-1+2*2^10*c.k,116683472559665+c.lower,116683862581829+c.upper)) = pointBounds75152 := by
 decide +kernel
def cuts75153 : List PrefixCut := [⟨64,162096285,162096382⟩]
theorem checked75153 : checkPrefixCuts (2^48) 9854386177 10 Manual.Count131072.C075153.packed 64 cuts75153 = true := by
 decide +kernel
def cuts75154 : List PrefixCut := [⟨33,83118133,83118185⟩,
⟨64,160865919,160866018⟩]
theorem checked75154 : checkPrefixCuts (2^48) 9854517249 10 Manual.Count131072.C075154.packed 64 cuts75154 = true := by
 decide +kernel
def pointBounds75154 : List (Nat × Nat × Nat) := [(9854584832,116683880272418,116684270294819)]
theorem point_links_checked75154 : (cuts75154.take 1).map (fun c => (9854517249-1+2*2^10*c.k,116683797154285+c.lower,116684187176634+c.upper)) = pointBounds75154 := by
 decide +kernel
def cuts75155 : List PrefixCut := [⟨64,161235101,161235197⟩]
theorem checked75155 : checkPrefixCuts (2^48) 9854648321 10 Manual.Count131072.C075155.packed 64 cuts75155 = true := by
 decide +kernel
def cuts75156 : List PrefixCut := [⟨56,142267853,142267937⟩,
⟨64,162918119,162918215⟩]
theorem checked75156 : checkPrefixCuts (2^48) 9854779393 10 Manual.Count131072.C075156.packed 64 cuts75156 = true := by
 decide +kernel
def pointBounds75156 : List (Nat × Nat × Nat) := [(9854894080,116684261523158,116684651545786)]
theorem point_links_checked75156 : (cuts75156.take 1).map (fun c => (9854779393-1+2*2^10*c.k,116684119255305+c.lower,116684509277849+c.upper)) = pointBounds75156 := by
 decide +kernel
def cuts75157 : List PrefixCut := [⟨64,162230480,162230573⟩]
theorem checked75157 : checkPrefixCuts (2^48) 9854910465 10 Manual.Count131072.C075157.packed 64 cuts75157 = true := by
 decide +kernel
def cuts75158 : List PrefixCut := [⟨64,162056940,162057034⟩]
theorem checked75158 : checkPrefixCuts (2^48) 9855041537 10 Manual.Count131072.C075158.packed 64 cuts75158 = true := by
 decide +kernel
def cuts75159 : List PrefixCut := [⟨15,38700274,38700297⟩,
⟨64,165824838,165824930⟩]
theorem checked75159 : checkPrefixCuts (2^48) 9855172609 10 Manual.Count131072.C075159.packed 64 cuts75159 = true := by
 decide +kernel
def pointBounds75159 : List (Nat × Nat × Nat) := [(9855203328,116684645161118,116685035183968)]
theorem point_links_checked75159 : (cuts75159.take 1).map (fun c => (9855172609-1+2*2^10*c.k,116684606460844+c.lower,116684996483671+c.upper)) = pointBounds75159 := by
 decide +kernel
def cuts75160 : List PrefixCut := [⟨64,161652791,161652887⟩]
theorem checked75160 : checkPrefixCuts (2^48) 9855303681 10 Manual.Count131072.C075160.packed 64 cuts75160 = true := by
 decide +kernel
def cuts75161 : List PrefixCut := [⟨38,96105273,96105330⟩,
⟨64,163107192,163107296⟩]
theorem checked75161 : checkPrefixCuts (2^48) 9855434753 10 Manual.Count131072.C075161.packed 64 cuts75161 = true := by
 decide +kernel
def pointBounds75161 : List (Nat × Nat × Nat) := [(9855512576,116685030043746,116685420066818)]
theorem point_links_checked75161 : (cuts75161.take 1).map (fun c => (9855434753-1+2*2^10*c.k,116684933938473+c.lower,116685323961488+c.upper)) = pointBounds75161 := by
 decide +kernel
def cuts75162 : List PrefixCut := [⟨64,161105848,161105948⟩]
theorem checked75162 : checkPrefixCuts (2^48) 9855565825 10 Manual.Count131072.C075162.packed 64 cuts75162 = true := by
 decide +kernel
def cuts75163 : List PrefixCut := [⟨61,156020171,156020264⟩,
⟨64,163873963,163874061⟩]
theorem checked75163 : checkPrefixCuts (2^48) 9855696897 10 Manual.Count131072.C075163.packed 64 cuts75163 = true := by
 decide +kernel
def pointBounds75163 : List (Nat × Nat × Nat) := [(9855821824,116685414171684,116685804194996)]
theorem point_links_checked75163 : (cuts75163.take 1).map (fun c => (9855696897-1+2*2^10*c.k,116685258151513+c.lower,116685648174732+c.upper)) = pointBounds75163 := by
 decide +kernel
def cuts75164 : List PrefixCut := [⟨64,163986038,163986128⟩]
theorem checked75164 : checkPrefixCuts (2^48) 9855827969 10 Manual.Count131072.C075164.packed 64 cuts75164 = true := by
 decide +kernel
def cuts75165 : List PrefixCut := [⟨64,159871405,159871510⟩]
theorem checked75165 : checkPrefixCuts (2^48) 9855959041 10 Manual.Count131072.C075165.packed 64 cuts75165 = true := by
 decide +kernel
def cuts75166 : List PrefixCut := [⟨20,49520291,49520322⟩,
⟨64,162953559,162953663⟩]
theorem checked75166 : checkPrefixCuts (2^48) 9856090113 10 Manual.Count131072.C075166.packed 64 cuts75166 = true := by
 decide +kernel
def pointBounds75166 : List (Nat × Nat × Nat) := [(9856131072,116685795403210,116686185426753)]
theorem point_links_checked75166 : (cuts75166.take 1).map (fun c => (9856090113-1+2*2^10*c.k,116685745882919+c.lower,116686135906431+c.upper)) = pointBounds75166 := by
 decide +kernel
def cuts75167 : List PrefixCut := [⟨64,163722471,163722566⟩]
theorem checked75167 : checkPrefixCuts (2^48) 9856221185 10 Manual.Count131072.C075167.packed 64 cuts75167 = true := by
 decide +kernel
def cuts75168 : List PrefixCut := [⟨43,108861518,108861588⟩,
⟨64,164062966,164063068⟩]
theorem checked75168 : checkPrefixCuts (2^48) 9856352257 10 Manual.Count131072.C075168.packed 64 cuts75168 = true := by
 decide +kernel
def pointBounds75168 : List (Nat × Nat × Nat) := [(9856440320,116686181420467,116686571444248)]
theorem point_links_checked75168 : (cuts75168.take 1).map (fun c => (9856352257-1+2*2^10*c.k,116686072558949+c.lower,116686462582660+c.upper)) = pointBounds75168 := by
 decide +kernel
def cuts75169 : List PrefixCut := [⟨64,163032728,163032835⟩]
theorem checked75169 : checkPrefixCuts (2^48) 9856483329 10 Manual.Count131072.C075169.packed 64 cuts75169 = true := by
 decide +kernel
def cuts75170 : List PrefixCut := [⟨64,159432425,159432519⟩]
theorem checked75170 : checkPrefixCuts (2^48) 9856614401 10 Manual.Count131072.C075170.packed 64 cuts75170 = true := by
 decide +kernel
def cuts75171 : List PrefixCut := [⟨2,4626164,4626167⟩,
⟨64,163199748,163199840⟩]
theorem checked75171 : checkPrefixCuts (2^48) 9856745473 10 Manual.Count131072.C075171.packed 64 cuts75171 = true := by
 decide +kernel
def pointBounds75171 : List (Nat × Nat × Nat) := [(9856749568,116686563713232,116686953737249)]
theorem point_links_checked75171 : (cuts75171.take 1).map (fun c => (9856745473-1+2*2^10*c.k,116686559087068+c.lower,116686949111082+c.upper)) = pointBounds75171 := by
 decide +kernel
def cuts75172 : List PrefixCut := [⟨64,162769237,162769333⟩]
theorem checked75172 : checkPrefixCuts (2^48) 9856876545 10 Manual.Count131072.C075172.packed 64 cuts75172 = true := by
 decide +kernel
def cuts75173 : List PrefixCut := [⟨25,64478866,64478903⟩,
⟨64,163595184,163595281⟩]
theorem checked75173 : checkPrefixCuts (2^48) 9857007617 10 Manual.Count131072.C075173.packed 64 cuts75173 = true := by
 decide +kernel
def pointBounds75173 : List (Nat × Nat × Nat) := [(9857058816,116686949534919,116687339559158)]
theorem point_links_checked75173 : (cuts75173.take 1).map (fun c => (9857007617-1+2*2^10*c.k,116686885056053+c.lower,116687275080255+c.upper)) = pointBounds75173 := by
 decide +kernel
def cuts75174 : List PrefixCut := [⟨64,163621573,163621668⟩]
theorem checked75174 : checkPrefixCuts (2^48) 9857138689 10 Manual.Count131072.C075174.packed 64 cuts75174 = true := by
 decide +kernel
def cuts75175 : List PrefixCut := [⟨48,120101973,120102044⟩,
⟨64,160192805,160192900⟩]
theorem checked75175 : checkPrefixCuts (2^48) 9857269761 10 Manual.Count131072.C075175.packed 64 cuts75175 = true := by
 decide +kernel
def pointBounds75175 : List (Nat × Nat × Nat) := [(9857368064,116687332374783,116687722399248)]
theorem point_links_checked75175 : (cuts75175.take 1).map (fun c => (9857269761-1+2*2^10*c.k,116687212272810+c.lower,116687602297204+c.upper)) = pointBounds75175 := by
 decide +kernel
def cuts75176 : List PrefixCut := [⟨64,162246598,162246697⟩]
theorem checked75176 : checkPrefixCuts (2^48) 9857400833 10 Manual.Count131072.C075176.packed 64 cuts75176 = true := by
 decide +kernel
def cuts75177 : List PrefixCut := [⟨64,166070680,166070779⟩]
theorem checked75177 : checkPrefixCuts (2^48) 9857531905 10 Manual.Count131072.C075177.packed 64 cuts75177 = true := by
 decide +kernel
def cuts75178 : List PrefixCut := [⟨7,17789077,17789089⟩,
⟨64,163155993,163156091⟩]
theorem checked75178 : checkPrefixCuts (2^48) 9857662977 10 Manual.Count131072.C075178.packed 64 cuts75178 = true := by
 decide +kernel
def pointBounds75178 : List (Nat × Nat × Nat) := [(9857677312,116687718571970,116688108596669)]
theorem point_links_checked75178 : (cuts75178.take 1).map (fun c => (9857662977-1+2*2^10*c.k,116687700782893+c.lower,116688090807580+c.upper)) = pointBounds75178 := by
 decide +kernel
def cuts75179 : List PrefixCut := [⟨64,162468549,162468644⟩]
theorem checked75179 : checkPrefixCuts (2^48) 9857794049 10 Manual.Count131072.C075179.packed 64 cuts75179 = true := by
 decide +kernel
def cuts75180 : List PrefixCut := [⟨30,76208144,76208187⟩,
⟨64,165692866,165692962⟩]
theorem checked75180 : checkPrefixCuts (2^48) 9857925121 10 Manual.Count131072.C075180.packed 64 cuts75180 = true := by
 decide +kernel
def pointBounds75180 : List (Nat × Nat × Nat) := [(9857986560,116688102615579,116688492640502)]
theorem point_links_checked75180 : (cuts75180.take 1).map (fun c => (9857925121-1+2*2^10*c.k,116688026407435+c.lower,116688416432315+c.upper)) = pointBounds75180 := by
 decide +kernel
def cuts75181 : List PrefixCut := [⟨64,161293569,161293672⟩]
theorem checked75181 : checkPrefixCuts (2^48) 9858056193 10 Manual.Count131072.C075181.packed 64 cuts75181 = true := by
 decide +kernel
def cuts75182 : List PrefixCut := [⟨53,136508261,136508348⟩,
⟨64,164432169,164432269⟩]
theorem checked75182 : checkPrefixCuts (2^48) 9858187265 10 Manual.Count131072.C075182.packed 64 cuts75182 = true := by
 decide +kernel
def pointBounds75182 : List (Nat × Nat × Nat) := [(9858295808,116688489902131,116688879927297)]
theorem point_links_checked75182 : (cuts75182.take 1).map (fun c => (9858187265-1+2*2^10*c.k,116688353393870+c.lower,116688743418949+c.upper)) = pointBounds75182 := by
 decide +kernel
def cuts75183 : List PrefixCut := [⟨64,163030943,163031046⟩]
theorem checked75183 : checkPrefixCuts (2^48) 9858318337 10 Manual.Count131072.C075183.packed 64 cuts75183 = true := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S8.B000161
