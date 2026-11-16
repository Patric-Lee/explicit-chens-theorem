import PlattAssemblyKernel
import PlattCertificates.Count131072.C073168
import PlattCertificates.Count131072.C073169
import PlattCertificates.Count131072.C073170
import PlattCertificates.Count131072.C073171
import PlattCertificates.Count131072.C073172
import PlattCertificates.Count131072.C073173
import PlattCertificates.Count131072.C073174
import PlattCertificates.Count131072.C073175
import PlattCertificates.Count131072.C073176
import PlattCertificates.Count131072.C073177
import PlattCertificates.Count131072.C073178
import PlattCertificates.Count131072.C073179
import PlattCertificates.Count131072.C073180
import PlattCertificates.Count131072.C073181
import PlattCertificates.Count131072.C073182
import PlattCertificates.Count131072.C073183
import PlattCertificates.Count131072.C073184
import PlattCertificates.Count131072.C073185
import PlattCertificates.Count131072.C073186
import PlattCertificates.Count131072.C073187
import PlattCertificates.Count131072.C073188
import PlattCertificates.Count131072.C073189
import PlattCertificates.Count131072.C073190
import PlattCertificates.Count131072.C073191
import PlattCertificates.Count131072.C073192
import PlattCertificates.Count131072.C073193
import PlattCertificates.Count131072.C073194
import PlattCertificates.Count131072.C073195
import PlattCertificates.Count131072.C073196
import PlattCertificates.Count131072.C073197
import PlattCertificates.Count131072.C073198
import PlattCertificates.Count131072.C073199
namespace ChenEffective.PlattWindow.Assembly.Prefix.S8.B000099
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts73168 : List PrefixCut := [⟨2,5427529,5427532⟩,
⟨64,165025144,165025232⟩]
theorem checked73168 : checkPrefixCuts (2^48) 9594208257 10 Manual.Count131072.C073168.packed 64 cuts73168 = true := by
 decide +kernel
def pointBounds73168 : List (Nat × Nat × Nat) := [(9594212352,116356114726169,116356504552696)]
theorem point_links_checked73168 : (cuts73168.take 1).map (fun c => (9594208257-1+2*2^10*c.k,116356109298640+c.lower,116356499125164+c.upper)) = pointBounds73168 := by
 decide +kernel
def cuts73169 : List PrefixCut := [⟨64,167193837,167193934⟩]
theorem checked73169 : checkPrefixCuts (2^48) 9594339329 10 Manual.Count131072.C073169.packed 64 cuts73169 = true := by
 decide +kernel
def cuts73170 : List PrefixCut := [⟨21,52953527,52953560⟩,
⟨64,165196638,165196742⟩]
theorem checked73170 : checkPrefixCuts (2^48) 9594470401 10 Manual.Count131072.C073170.packed 64 cuts73170 = true := by
 decide +kernel
def pointBounds73170 : List (Nat × Nat × Nat) := [(9594513408,116356494471148,116356884297890)]
theorem point_links_checked73170 : (cuts73170.take 1).map (fun c => (9594470401-1+2*2^10*c.k,116356441517621+c.lower,116356831344330+c.upper)) = pointBounds73170 := by
 decide +kernel
def cuts73171 : List PrefixCut := [⟨64,167247940,167248041⟩]
theorem checked73171 : checkPrefixCuts (2^48) 9594601473 10 Manual.Count131072.C073171.packed 64 cuts73171 = true := by
 decide +kernel
def cuts73172 : List PrefixCut := [⟨40,103087657,103087723⟩,
⟨64,166805603,166805709⟩]
theorem checked73172 : checkPrefixCuts (2^48) 9594732545 10 Manual.Count131072.C073172.packed 64 cuts73172 = true := by
 decide +kernel
def pointBounds73172 : List (Nat × Nat × Nat) := [(9594814464,116356877049856,116357266876836)]
theorem point_links_checked73172 : (cuts73172.take 1).map (fun c => (9594732545-1+2*2^10*c.k,116356773962199+c.lower,116357163789113+c.upper)) = pointBounds73172 := by
 decide +kernel
def cuts73173 : List PrefixCut := [⟨64,169355553,169355654⟩]
theorem checked73173 : checkPrefixCuts (2^48) 9594863617 10 Manual.Count131072.C073173.packed 64 cuts73173 = true := by
 decide +kernel
def cuts73174 : List PrefixCut := [⟨59,153864233,153864324⟩,
⟨64,166214357,166214456⟩]
theorem checked73174 : checkPrefixCuts (2^48) 9594994689 10 Manual.Count131072.C073174.packed 64 cuts73174 = true := by
 decide +kernel
def pointBounds73174 : List (Nat × Nat × Nat) := [(9595115520,116357263987588,116357653814800)]
theorem point_links_checked73174 : (cuts73174.take 1).map (fun c => (9594994689-1+2*2^10*c.k,116357110123355+c.lower,116357499950476+c.upper)) = pointBounds73174 := by
 decide +kernel
def cuts73175 : List PrefixCut := [⟨64,166153404,166153503⟩]
theorem checked73175 : checkPrefixCuts (2^48) 9595125761 10 Manual.Count131072.C073175.packed 64 cuts73175 = true := by
 decide +kernel
def cuts73176 : List PrefixCut := [⟨64,165036441,165036535⟩]
theorem checked73176 : checkPrefixCuts (2^48) 9595256833 10 Manual.Count131072.C073176.packed 64 cuts73176 = true := by
 decide +kernel
def cuts73177 : List PrefixCut := [⟨14,36051918,36051939⟩,
⟨64,167703592,167703687⟩]
theorem checked73177 : checkPrefixCuts (2^48) 9595387905 10 Manual.Count131072.C073177.packed 64 cuts73177 = true := by
 decide +kernel
def pointBounds73177 : List (Nat × Nat × Nat) := [(9595416576,116357643579475,116358033406909)]
theorem point_links_checked73177 : (cuts73177.take 1).map (fun c => (9595387905-1+2*2^10*c.k,116357607527557+c.lower,116357997354970+c.upper)) = pointBounds73177 := by
 decide +kernel
def cuts73178 : List PrefixCut := [⟨64,168111976,168112076⟩]
theorem checked73178 : checkPrefixCuts (2^48) 9595518977 10 Manual.Count131072.C073178.packed 64 cuts73178 = true := by
 decide +kernel
def cuts73179 : List PrefixCut := [⟨33,86856465,86856517⟩,
⟨64,167699007,167699107⟩]
theorem checked73179 : checkPrefixCuts (2^48) 9595650049 10 Manual.Count131072.C073179.packed 64 cuts73179 = true := by
 decide +kernel
def pointBounds73179 : List (Nat × Nat × Nat) := [(9595717632,116358030199590,116358420027250)]
theorem point_links_checked73179 : (cuts73179.take 1).map (fun c => (9595650049-1+2*2^10*c.k,116357943343125+c.lower,116358333170733+c.upper)) = pointBounds73179 := by
 decide +kernel
def cuts73180 : List PrefixCut := [⟨64,166816727,166816829⟩]
theorem checked73180 : checkPrefixCuts (2^48) 9595781121 10 Manual.Count131072.C073180.packed 64 cuts73180 = true := by
 decide +kernel
def cuts73181 : List PrefixCut := [⟨52,138068684,138068767⟩,
⟨64,169601045,169601146⟩]
theorem checked73181 : checkPrefixCuts (2^48) 9595912193 10 Manual.Count131072.C073181.packed 64 cuts73181 = true := by
 decide +kernel
def pointBounds73181 : List (Nat × Nat × Nat) := [(9596018688,116358415927543,116358805755436)]
theorem point_links_checked73181 : (cuts73181.take 1).map (fun c => (9595912193-1+2*2^10*c.k,116358277858859+c.lower,116358667686669+c.upper)) = pointBounds73181 := by
 decide +kernel
def cuts73182 : List PrefixCut := [⟨64,167809467,167809560⟩]
theorem checked73182 : checkPrefixCuts (2^48) 9596043265 10 Manual.Count131072.C073182.packed 64 cuts73182 = true := by
 decide +kernel
def cuts73183 : List PrefixCut := [⟨64,168540464,168540571⟩]
theorem checked73183 : checkPrefixCuts (2^48) 9596174337 10 Manual.Count131072.C073183.packed 64 cuts73183 = true := by
 decide +kernel
def cuts73184 : List PrefixCut := [⟨7,18508221,18508230⟩,
⟨64,167716886,167716979⟩]
theorem checked73184 : checkPrefixCuts (2^48) 9596305409 10 Manual.Count131072.C073184.packed 64 cuts73184 = true := by
 decide +kernel
def pointBounds73184 : List (Nat × Nat × Nat) := [(9596319744,116358802318056,116359192146176)]
theorem point_links_checked73184 : (cuts73184.take 1).map (fun c => (9596305409-1+2*2^10*c.k,116358783809835+c.lower,116359173637946+c.upper)) = pointBounds73184 := by
 decide +kernel
def cuts73185 : List PrefixCut := [⟨64,167861243,167861338⟩]
theorem checked73185 : checkPrefixCuts (2^48) 9596436481 10 Manual.Count131072.C073185.packed 64 cuts73185 = true := by
 decide +kernel
def cuts73186 : List PrefixCut := [⟨26,66815352,66815391⟩,
⟨64,166773721,166773824⟩]
theorem checked73186 : checkPrefixCuts (2^48) 9596567553 10 Manual.Count131072.C073186.packed 64 cuts73186 = true := by
 decide +kernel
def pointBounds73186 : List (Nat × Nat × Nat) := [(9596620800,116359186203316,116359576031654)]
theorem point_links_checked73186 : (cuts73186.take 1).map (fun c => (9596567553-1+2*2^10*c.k,116359119387964+c.lower,116359509216263+c.upper)) = pointBounds73186 := by
 decide +kernel
def cuts73187 : List PrefixCut := [⟨64,166888765,166888867⟩]
theorem checked73187 : checkPrefixCuts (2^48) 9596698625 10 Manual.Count131072.C073187.packed 64 cuts73187 = true := by
 decide +kernel
def cuts73188 : List PrefixCut := [⟨45,117817993,117818062⟩,
⟨64,167707721,167707819⟩]
theorem checked73188 : checkPrefixCuts (2^48) 9596829697 10 Manual.Count131072.C073188.packed 64 cuts73188 = true := by
 decide +kernel
def pointBounds73188 : List (Nat × Nat × Nat) := [(9596921856,116359570868443,116359960697016)]
theorem point_links_checked73188 : (cuts73188.take 1).map (fun c => (9596829697-1+2*2^10*c.k,116359453050450+c.lower,116359842878954+c.upper)) = pointBounds73188 := by
 decide +kernel
def cuts73189 : List PrefixCut := [⟨64,168321356,168321461⟩]
theorem checked73189 : checkPrefixCuts (2^48) 9596960769 10 Manual.Count131072.C073189.packed 64 cuts73189 = true := by
 decide +kernel
def cuts73190 : List PrefixCut := [⟨64,166031395,166031494⟩]
theorem checked73190 : checkPrefixCuts (2^48) 9597091841 10 Manual.Count131072.C073190.packed 64 cuts73190 = true := by
 decide +kernel
def pointBounds73190 : List (Nat × Nat × Nat) := [(9597222912,116359955110922,116360344939728)]
theorem point_links_checked73190 : (cuts73190.take 1).map (fun c => (9597091841-1+2*2^10*c.k,116359789079527+c.lower,116360178908234+c.upper)) = pointBounds73190 := by
 decide +kernel
def cuts73191 : List PrefixCut := [⟨64,168492725,168492829⟩]
theorem checked73191 : checkPrefixCuts (2^48) 9597222913 10 Manual.Count131072.C073191.packed 64 cuts73191 = true := by
 decide +kernel
def cuts73192 : List PrefixCut := [⟨64,168578410,168578506⟩]
theorem checked73192 : checkPrefixCuts (2^48) 9597353985 10 Manual.Count131072.C073192.packed 64 cuts73192 = true := by
 decide +kernel
def cuts73193 : List PrefixCut := [⟨19,48743011,48743041⟩,
⟨64,166699122,166699224⟩]
theorem checked73193 : checkPrefixCuts (2^48) 9597485057 10 Manual.Count131072.C073193.packed 64 cuts73193 = true := by
 decide +kernel
def pointBounds73193 : List (Nat × Nat × Nat) := [(9597523968,116360340925068,116360730754104)]
theorem point_links_checked73193 : (cuts73193.take 1).map (fun c => (9597485057-1+2*2^10*c.k,116360292182057+c.lower,116360682011063+c.upper)) = pointBounds73193 := by
 decide +kernel
def cuts73194 : List PrefixCut := [⟨64,168456484,168456585⟩]
theorem checked73194 : checkPrefixCuts (2^48) 9597616129 10 Manual.Count131072.C073194.packed 64 cuts73194 = true := by
 decide +kernel
def cuts73195 : List PrefixCut := [⟨38,100445192,100445254⟩,
⟨64,166841212,166841313⟩]
theorem checked73195 : checkPrefixCuts (2^48) 9597747201 10 Manual.Count131072.C073195.packed 64 cuts73195 = true := by
 decide +kernel
def pointBounds73195 : List (Nat × Nat × Nat) := [(9597825024,116360727782855,116361117612126)]
theorem point_links_checked73195 : (cuts73195.take 1).map (fun c => (9597747201-1+2*2^10*c.k,116360627337663+c.lower,116361017166872+c.upper)) = pointBounds73195 := by
 decide +kernel
def cuts73196 : List PrefixCut := [⟨64,169097080,169097182⟩]
theorem checked73196 : checkPrefixCuts (2^48) 9597878273 10 Manual.Count131072.C073196.packed 64 cuts73196 = true := by
 decide +kernel
def cuts73197 : List PrefixCut := [⟨57,149739590,149739679⟩,
⟨64,168039016,168039115⟩]
theorem checked73197 : checkPrefixCuts (2^48) 9598009345 10 Manual.Count131072.C073197.packed 64 cuts73197 = true := by
 decide +kernel
def pointBounds73197 : List (Nat × Nat × Nat) := [(9598126080,116361113015545,116361502845046)]
theorem point_links_checked73197 : (cuts73197.take 1).map (fun c => (9598009345-1+2*2^10*c.k,116360963275955+c.lower,116361353105367+c.upper)) = pointBounds73197 := by
 decide +kernel
def cuts73198 : List PrefixCut := [⟨64,167890102,167890210⟩]
theorem checked73198 : checkPrefixCuts (2^48) 9598140417 10 Manual.Count131072.C073198.packed 64 cuts73198 = true := by
 decide +kernel
def cuts73199 : List PrefixCut := [⟨64,165160549,165160646⟩]
theorem checked73199 : checkPrefixCuts (2^48) 9598271489 10 Manual.Count131072.C073199.packed 64 cuts73199 = true := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S8.B000099
