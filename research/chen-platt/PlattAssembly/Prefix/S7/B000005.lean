import PlattAssemblyKernel
import PlattCertificates.Count131072.C060160
import PlattCertificates.Count131072.C060161
import PlattCertificates.Count131072.C060162
import PlattCertificates.Count131072.C060163
import PlattCertificates.Count131072.C060164
import PlattCertificates.Count131072.C060165
import PlattCertificates.Count131072.C060166
import PlattCertificates.Count131072.C060167
import PlattCertificates.Count131072.C060168
import PlattCertificates.Count131072.C060169
import PlattCertificates.Count131072.C060170
import PlattCertificates.Count131072.C060171
import PlattCertificates.Count131072.C060172
import PlattCertificates.Count131072.C060173
import PlattCertificates.Count131072.C060174
import PlattCertificates.Count131072.C060175
import PlattCertificates.Count131072.C060176
import PlattCertificates.Count131072.C060177
import PlattCertificates.Count131072.C060178
import PlattCertificates.Count131072.C060179
import PlattCertificates.Count131072.C060180
import PlattCertificates.Count131072.C060181
import PlattCertificates.Count131072.C060182
import PlattCertificates.Count131072.C060183
import PlattCertificates.Count131072.C060184
import PlattCertificates.Count131072.C060185
import PlattCertificates.Count131072.C060186
import PlattCertificates.Count131072.C060187
import PlattCertificates.Count131072.C060188
import PlattCertificates.Count131072.C060189
import PlattCertificates.Count131072.C060190
import PlattCertificates.Count131072.C060191
namespace ChenEffective.PlattWindow.Assembly.Prefix.S7.B000005
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts60160 : List PrefixCut := [⟨64,204756630,204756755⟩]
theorem checked60160 : checkPrefixCuts (2^48) 7889223681 10 Manual.Count131072.C060160.packed 64 cuts60160 = true := by
 decide +kernel
def cuts60161 : List PrefixCut := [⟨36,118200029,118200096⟩,
⟨64,207429075,207429191⟩]
theorem checked60161 : checkPrefixCuts (2^48) 7889354753 10 Manual.Count131072.C060161.packed 64 cuts60161 = true := by
 decide +kernel
def pointBounds60161 : List (Nat × Nat × Nat) := [(7889428480,113949978300864,113950366727050)]
theorem point_links_checked60161 : (cuts60161.take 1).map (fun c => (7889354753-1+2*2^10*c.k,113949860100835+c.lower,113950248526954+c.upper)) = pointBounds60161 := by
 decide +kernel
def cuts60162 : List PrefixCut := [⟨64,205392020,205392138⟩]
theorem checked60162 : checkPrefixCuts (2^48) 7889485825 10 Manual.Count131072.C060162.packed 64 cuts60162 = true := by
 decide +kernel
def cuts60163 : List PrefixCut := [⟨29,94078898,94078952⟩,
⟨64,205888083,205888202⟩]
theorem checked60163 : checkPrefixCuts (2^48) 7889616897 10 Manual.Count131072.C060163.packed 64 cuts60163 = true := by
 decide +kernel
def pointBounds60163 : List (Nat × Nat × Nat) := [(7889676288,113950367000828,113950755427235)]
theorem point_links_checked60163 : (cuts60163.take 1).map (fun c => (7889616897-1+2*2^10*c.k,113950272921930+c.lower,113950661348283+c.upper)) = pointBounds60163 := by
 decide +kernel
def cuts60164 : List PrefixCut := [⟨64,204600347,204600464⟩]
theorem checked60164 : checkPrefixCuts (2^48) 7889747969 10 Manual.Count131072.C060164.packed 64 cuts60164 = true := by
 decide +kernel
def cuts60165 : List PrefixCut := [⟨22,70779868,70779908⟩,
⟨64,208271472,208271591⟩]
theorem checked60165 : checkPrefixCuts (2^48) 7889879041 10 Manual.Count131072.C060165.packed 64 cuts60165 = true := by
 decide +kernel
def pointBounds60165 : List (Nat × Nat × Nat) := [(7889924096,113950754190228,113951142616857)]
theorem point_links_checked60165 : (cuts60165.take 1).map (fun c => (7889879041-1+2*2^10*c.k,113950683410360+c.lower,113951071836949+c.upper)) = pointBounds60165 := by
 decide +kernel
def cuts60166 : List PrefixCut := [⟨64,207340476,207340591⟩]
theorem checked60166 : checkPrefixCuts (2^48) 7890010113 10 Manual.Count131072.C060166.packed 64 cuts60166 = true := by
 decide +kernel
def cuts60167 : List PrefixCut := [⟨15,47625036,47625062⟩,
⟨64,205481985,205482101⟩]
theorem checked60167 : checkPrefixCuts (2^48) 7890141185 10 Manual.Count131072.C060167.packed 64 cuts60167 = true := by
 decide +kernel
def pointBounds60167 : List (Nat × Nat × Nat) := [(7890171904,113951146647344,113951535074193)]
theorem point_links_checked60167 : (cuts60167.take 1).map (fun c => (7890141185-1+2*2^10*c.k,113951099022308+c.lower,113951487449131+c.upper)) = pointBounds60167 := by
 decide +kernel
def cuts60168 : List PrefixCut := [⟨64,202945759,202945876⟩]
theorem checked60168 : checkPrefixCuts (2^48) 7890272257 10 Manual.Count131072.C060168.packed 64 cuts60168 = true := by
 decide +kernel
def cuts60169 : List PrefixCut := [⟨8,26719100,26719115⟩,
⟨64,205475178,205475295⟩]
theorem checked60169 : checkPrefixCuts (2^48) 7890403329 10 Manual.Count131072.C060169.packed 64 cuts60169 = true := by
 decide +kernel
def pointBounds60169 : List (Nat × Nat × Nat) := [(7890419712,113951534169152,113951922596223)]
theorem point_links_checked60169 : (cuts60169.take 1).map (fun c => (7890403329-1+2*2^10*c.k,113951507450052+c.lower,113951895877108+c.upper)) = pointBounds60169 := by
 decide +kernel
def cuts60170 : List PrefixCut := [⟨64,204865327,204865444⟩]
theorem checked60170 : checkPrefixCuts (2^48) 7890534401 10 Manual.Count131072.C060170.packed 64 cuts60170 = true := by
 decide +kernel
def cuts60171 : List PrefixCut := [⟨1,3281813,3281815⟩,
⟨64,204505213,204505333⟩]
theorem checked60171 : checkPrefixCuts (2^48) 7890665473 10 Manual.Count131072.C060171.packed 64 cuts60171 = true := by
 decide +kernel
def pointBounds60171 : List (Nat × Nat × Nat) := [(7890667520,113951921072370,113952309499662)]
theorem point_links_checked60171 : (cuts60171.take 1).map (fun c => (7890665473-1+2*2^10*c.k,113951917790557+c.lower,113952306217847+c.upper)) = pointBounds60171 := by
 decide +kernel
def cuts60172 : List PrefixCut := [⟨58,186381084,186381197⟩,
⟨64,205001202,205001325⟩]
theorem checked60172 : checkPrefixCuts (2^48) 7890796545 10 Manual.Count131072.C060172.packed 64 cuts60172 = true := by
 decide +kernel
def pointBounds60172 : List (Nat × Nat × Nat) := [(7890915328,113952308676854,113952697104377)]
theorem point_links_checked60172 : (cuts60172.take 1).map (fun c => (7890796545-1+2*2^10*c.k,113952122295770+c.lower,113952510723180+c.upper)) = pointBounds60172 := by
 decide +kernel
def cuts60173 : List PrefixCut := [⟨64,205140496,205140614⟩]
theorem checked60173 : checkPrefixCuts (2^48) 7890927617 10 Manual.Count131072.C060173.packed 64 cuts60173 = true := by
 decide +kernel
def cuts60174 : List PrefixCut := [⟨51,163153996,163154081⟩,
⟨64,204066997,204067104⟩]
theorem checked60174 : checkPrefixCuts (2^48) 7891058689 10 Manual.Count131072.C060174.packed 64 cuts60174 = true := by
 decide +kernel
def pointBounds60174 : List (Nat × Nat × Nat) := [(7891163136,113952695591464,113953084019200)]
theorem point_links_checked60174 : (cuts60174.take 1).map (fun c => (7891058689-1+2*2^10*c.k,113952532437468+c.lower,113952920865119+c.upper)) = pointBounds60174 := by
 decide +kernel
def cuts60175 : List PrefixCut := [⟨64,204170605,204170721⟩]
theorem checked60175 : checkPrefixCuts (2^48) 7891189761 10 Manual.Count131072.C060175.packed 64 cuts60175 = true := by
 decide +kernel
def cuts60176 : List PrefixCut := [⟨44,140998440,140998519⟩,
⟨64,204630904,204631019⟩]
theorem checked60176 : checkPrefixCuts (2^48) 7891320833 10 Manual.Count131072.C060176.packed 64 cuts60176 = true := by
 decide +kernel
def pointBounds60176 : List (Nat × Nat × Nat) := [(7891410944,113953081673510,113953470101463)]
theorem point_links_checked60176 : (cuts60176.take 1).map (fun c => (7891320833-1+2*2^10*c.k,113952940675070+c.lower,113953329102944+c.upper)) = pointBounds60176 := by
 decide +kernel
def cuts60177 : List PrefixCut := [⟨64,203022452,203022570⟩]
theorem checked60177 : checkPrefixCuts (2^48) 7891451905 10 Manual.Count131072.C060177.packed 64 cuts60177 = true := by
 decide +kernel
def cuts60178 : List PrefixCut := [⟨37,118523317,118523387⟩,
⟨64,205373118,205373237⟩]
theorem checked60178 : checkPrefixCuts (2^48) 7891582977 10 Manual.Count131072.C060178.packed 64 cuts60178 = true := by
 decide +kernel
def pointBounds60178 : List (Nat × Nat × Nat) := [(7891658752,113953466851743,113953855279920)]
theorem point_links_checked60178 : (cuts60178.take 1).map (fun c => (7891582977-1+2*2^10*c.k,113953348328426+c.lower,113953736756533+c.upper)) = pointBounds60178 := by
 decide +kernel
def cuts60179 : List PrefixCut := [⟨64,203800359,203800481⟩]
theorem checked60179 : checkPrefixCuts (2^48) 7891714049 10 Manual.Count131072.C060179.packed 64 cuts60179 = true := by
 decide +kernel
def cuts60180 : List PrefixCut := [⟨30,97832966,97833024⟩,
⟨64,206364957,206365077⟩]
theorem checked60180 : checkPrefixCuts (2^48) 7891845121 10 Manual.Count131072.C060180.packed 64 cuts60180 = true := by
 decide +kernel
def pointBounds60180 : List (Nat × Nat × Nat) := [(7891906560,113953855334869,113954243763275)]
theorem point_links_checked60180 : (cuts60180.take 1).map (fun c => (7891845121-1+2*2^10*c.k,113953757501903+c.lower,113954145930251+c.upper)) = pointBounds60180 := by
 decide +kernel
def cuts60181 : List PrefixCut := [⟨64,203757946,203758060⟩]
theorem checked60181 : checkPrefixCuts (2^48) 7891976193 10 Manual.Count131072.C060181.packed 64 cuts60181 = true := by
 decide +kernel
def cuts60182 : List PrefixCut := [⟨23,75146707,75146746⟩,
⟨64,205502146,205502258⟩]
theorem checked60182 : checkPrefixCuts (2^48) 7892107265 10 Manual.Count131072.C060182.packed 64 cuts60182 = true := by
 decide +kernel
def pointBounds60182 : List (Nat × Nat × Nat) := [(7892154368,113954242771513,113954631200134)]
theorem point_links_checked60182 : (cuts60182.take 1).map (fun c => (7892107265-1+2*2^10*c.k,113954167624806+c.lower,113954556053388+c.upper)) = pointBounds60182 := by
 decide +kernel
def cuts60183 : List PrefixCut := [⟨64,207246296,207246416⟩]
theorem checked60183 : checkPrefixCuts (2^48) 7892238337 10 Manual.Count131072.C060183.packed 64 cuts60183 = true := by
 decide +kernel
def cuts60184 : List PrefixCut := [⟨16,50500377,50500408⟩,
⟨64,203676444,203676563⟩]
theorem checked60184 : checkPrefixCuts (2^48) 7892369409 10 Manual.Count131072.C060184.packed 64 cuts60184 = true := by
 decide +kernel
def pointBounds60184 : List (Nat × Nat × Nat) := [(7892402176,113954630873625,113955019302470)]
theorem point_links_checked60184 : (cuts60184.take 1).map (fun c => (7892369409-1+2*2^10*c.k,113954580373248+c.lower,113954968802062+c.upper)) = pointBounds60184 := by
 decide +kernel
def cuts60185 : List PrefixCut := [⟨64,207275051,207275165⟩]
theorem checked60185 : checkPrefixCuts (2^48) 7892500481 10 Manual.Count131072.C060185.packed 64 cuts60185 = true := by
 decide +kernel
def cuts60186 : List PrefixCut := [⟨9,28423375,28423392⟩,
⟨64,205559810,205559931⟩]
theorem checked60186 : checkPrefixCuts (2^48) 7892631553 10 Manual.Count131072.C060186.packed 64 cuts60186 = true := by
 decide +kernel
def pointBounds60186 : List (Nat × Nat × Nat) := [(7892649984,113955019748118,113955408177182)]
theorem point_links_checked60186 : (cuts60186.take 1).map (fun c => (7892631553-1+2*2^10*c.k,113954991324743+c.lower,113955379753790+c.upper)) = pointBounds60186 := by
 decide +kernel
def cuts60187 : List PrefixCut := [⟨64,206483614,206483733⟩]
theorem checked60187 : checkPrefixCuts (2^48) 7892762625 10 Manual.Count131072.C060187.packed 64 cuts60187 = true := by
 decide +kernel
def cuts60188 : List PrefixCut := [⟨2,6419124,6419128⟩,
⟨64,206444511,206444632⟩]
theorem checked60188 : checkPrefixCuts (2^48) 7892893697 10 Manual.Count131072.C060188.packed 64 cuts60188 = true := by
 decide +kernel
def pointBounds60188 : List (Nat × Nat × Nat) := [(7892897792,113955409787291,113955798216582)]
theorem point_links_checked60188 : (cuts60188.take 1).map (fun c => (7892893697-1+2*2^10*c.k,113955403368167+c.lower,113955791797454+c.upper)) = pointBounds60188 := by
 decide +kernel
def cuts60189 : List PrefixCut := [⟨59,189537928,189538037⟩,
⟨64,206583719,206583838⟩]
theorem checked60189 : checkPrefixCuts (2^48) 7893024769 10 Manual.Count131072.C060189.packed 64 cuts60189 = true := by
 decide +kernel
def pointBounds60189 : List (Nat × Nat × Nat) := [(7893145600,113955799350606,113956187780123)]
theorem point_links_checked60189 : (cuts60189.take 1).map (fun c => (7893024769-1+2*2^10*c.k,113955609812678+c.lower,113955998242086+c.upper)) = pointBounds60189 := by
 decide +kernel
def cuts60190 : List PrefixCut := [⟨64,205189557,205189674⟩]
theorem checked60190 : checkPrefixCuts (2^48) 7893155841 10 Manual.Count131072.C060190.packed 64 cuts60190 = true := by
 decide +kernel
def cuts60191 : List PrefixCut := [⟨52,165960690,165960787⟩,
⟨64,204686908,204687026⟩]
theorem checked60191 : checkPrefixCuts (2^48) 7893286913 10 Manual.Count131072.C060191.packed 64 cuts60191 = true := by
 decide +kernel
def pointBounds60191 : List (Nat × Nat × Nat) := [(7893393408,113956187546644,113956575976385)]
theorem point_links_checked60191 : (cuts60191.take 1).map (fun c => (7893286913-1+2*2^10*c.k,113956021585954+c.lower,113956410015598+c.upper)) = pointBounds60191 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S7.B000005
