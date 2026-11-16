import PlattAssemblyKernel
import PlattCertificates.Count131072.C065184
import PlattCertificates.Count131072.C065185
import PlattCertificates.Count131072.C065186
import PlattCertificates.Count131072.C065187
import PlattCertificates.Count131072.C065188
import PlattCertificates.Count131072.C065189
import PlattCertificates.Count131072.C065190
import PlattCertificates.Count131072.C065191
import PlattCertificates.Count131072.C065192
import PlattCertificates.Count131072.C065193
import PlattCertificates.Count131072.C065194
import PlattCertificates.Count131072.C065195
import PlattCertificates.Count131072.C065196
import PlattCertificates.Count131072.C065197
import PlattCertificates.Count131072.C065198
import PlattCertificates.Count131072.C065199
import PlattCertificates.Count131072.C065200
import PlattCertificates.Count131072.C065201
import PlattCertificates.Count131072.C065202
import PlattCertificates.Count131072.C065203
import PlattCertificates.Count131072.C065204
import PlattCertificates.Count131072.C065205
import PlattCertificates.Count131072.C065206
import PlattCertificates.Count131072.C065207
import PlattCertificates.Count131072.C065208
import PlattCertificates.Count131072.C065209
import PlattCertificates.Count131072.C065210
import PlattCertificates.Count131072.C065211
import PlattCertificates.Count131072.C065212
import PlattCertificates.Count131072.C065213
import PlattCertificates.Count131072.C065214
import PlattCertificates.Count131072.C065215
namespace ChenEffective.PlattWindow.Assembly.Prefix.S7.B000162
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts65184 : List PrefixCut := [⟨64,191814532,191814649⟩]
theorem checked65184 : checkPrefixCuts (2^48) 8547729409 10 Manual.Count131072.C065184.packed 64 cuts65184 = true := by
 decide +kernel
def cuts65185 : List PrefixCut := [⟨15,43894647,43894676⟩,
⟨64,187695463,187695576⟩]
theorem checked65185 : checkPrefixCuts (2^48) 8547860481 10 Manual.Count131072.C065185.packed 64 cuts65185 = true := by
 decide +kernel
def pointBounds65185 : List (Nat × Nat × Nat) := [(8547891200,114938422445028,114938811439389)]
theorem point_links_checked65185 : (cuts65185.take 1).map (fun c => (8547860481-1+2*2^10*c.k,114938378550381+c.lower,114938767544713+c.upper)) = pointBounds65185 := by
 decide +kernel
def cuts65186 : List PrefixCut := [⟨64,189800003,189800110⟩]
theorem checked65186 : checkPrefixCuts (2^48) 8547991553 10 Manual.Count131072.C065186.packed 64 cuts65186 = true := by
 decide +kernel
def cuts65187 : List PrefixCut := [⟨18,54430318,54430346⟩,
⟨64,189138550,189138655⟩]
theorem checked65187 : checkPrefixCuts (2^48) 8548122625 10 Manual.Count131072.C065187.packed 64 cuts65187 = true := by
 decide +kernel
def pointBounds65187 : List (Nat × Nat × Nat) := [(8548159488,114938810476165,114939199470745)]
theorem point_links_checked65187 : (cuts65187.take 1).map (fun c => (8548122625-1+2*2^10*c.k,114938756045847+c.lower,114939145040399+c.upper)) = pointBounds65187 := by
 decide +kernel
def cuts65188 : List PrefixCut := [⟨64,188279533,188279638⟩]
theorem checked65188 : checkPrefixCuts (2^48) 8548253697 10 Manual.Count131072.C065188.packed 64 cuts65188 = true := by
 decide +kernel
def cuts65189 : List PrefixCut := [⟨21,59664046,59664084⟩,
⟨64,185444903,185445012⟩]
theorem checked65189 : checkPrefixCuts (2^48) 8548384769 10 Manual.Count131072.C065189.packed 64 cuts65189 = true := by
 decide +kernel
def pointBounds65189 : List (Nat × Nat × Nat) := [(8548427776,114939193127976,114939582122776)]
theorem point_links_checked65189 : (cuts65189.take 1).map (fun c => (8548384769-1+2*2^10*c.k,114939133463930+c.lower,114939522458692+c.upper)) = pointBounds65189 := by
 decide +kernel
def cuts65190 : List PrefixCut := [⟨64,189557881,189557994⟩]
theorem checked65190 : checkPrefixCuts (2^48) 8548515841 10 Manual.Count131072.C065190.packed 64 cuts65190 = true := by
 decide +kernel
def cuts65191 : List PrefixCut := [⟨24,69671746,69671786⟩,
⟨64,188863516,188863624⟩]
theorem checked65191 : checkPrefixCuts (2^48) 8548646913 10 Manual.Count131072.C065191.packed 64 cuts65191 = true := by
 decide +kernel
def pointBounds65191 : List (Nat × Nat × Nat) := [(8548696064,114939578138460,114939967133484)]
theorem point_links_checked65191 : (cuts65191.take 1).map (fun c => (8548646913-1+2*2^10*c.k,114939508466714+c.lower,114939897461698+c.upper)) = pointBounds65191 := by
 decide +kernel
def cuts65192 : List PrefixCut := [⟨64,187214373,187214482⟩]
theorem checked65192 : checkPrefixCuts (2^48) 8548777985 10 Manual.Count131072.C065192.packed 64 cuts65192 = true := by
 decide +kernel
def cuts65193 : List PrefixCut := [⟨27,80567807,80567853⟩,
⟨64,189055290,189055402⟩]
theorem checked65193 : checkPrefixCuts (2^48) 8548909057 10 Manual.Count131072.C065193.packed 64 cuts65193 = true := by
 decide +kernel
def pointBounds65193 : List (Nat × Nat × Nat) := [(8548964352,114939965112410,114940354107657)]
theorem point_links_checked65193 : (cuts65193.take 1).map (fun c => (8548909057-1+2*2^10*c.k,114939884544603+c.lower,114940273539804+c.upper)) = pointBounds65193 := by
 decide +kernel
def cuts65194 : List PrefixCut := [⟨64,191126646,191126757⟩]
theorem checked65194 : checkPrefixCuts (2^48) 8549040129 10 Manual.Count131072.C065194.packed 64 cuts65194 = true := by
 decide +kernel
def cuts65195 : List PrefixCut := [⟨30,88730487,88730539⟩,
⟨64,189016569,189016681⟩]
theorem checked65195 : checkPrefixCuts (2^48) 8549171201 10 Manual.Count131072.C065195.packed 64 cuts65195 = true := by
 decide +kernel
def pointBounds65195 : List (Nat × Nat × Nat) := [(8549232640,114940353457026,114940742452502)]
theorem point_links_checked65195 : (cuts65195.take 1).map (fun c => (8549171201-1+2*2^10*c.k,114940264726539+c.lower,114940653721963+c.upper)) = pointBounds65195 := by
 decide +kernel
def cuts65196 : List PrefixCut := [⟨64,189902613,189902721⟩]
theorem checked65196 : checkPrefixCuts (2^48) 8549302273 10 Manual.Count131072.C065196.packed 64 cuts65196 = true := by
 decide +kernel
def cuts65197 : List PrefixCut := [⟨33,98966817,98966867⟩,
⟨64,190788619,190788723⟩]
theorem checked65197 : checkPrefixCuts (2^48) 8549433345 10 Manual.Count131072.C065197.packed 64 cuts65197 = true := by
 decide +kernel
def pointBounds65197 : List (Nat × Nat × Nat) := [(8549500928,114940742612538,114941131608232)]
theorem point_links_checked65197 : (cuts65197.take 1).map (fun c => (8549433345-1+2*2^10*c.k,114940643645721+c.lower,114941032641365+c.upper)) = pointBounds65197 := by
 decide +kernel
def cuts65198 : List PrefixCut := [⟨64,190851548,190851658⟩]
theorem checked65198 : checkPrefixCuts (2^48) 8549564417 10 Manual.Count131072.C065198.packed 64 cuts65198 = true := by
 decide +kernel
def cuts65199 : List PrefixCut := [⟨36,105844458,105844519⟩,
⟨64,189103741,189103850⟩]
theorem checked65199 : checkPrefixCuts (2^48) 8549695489 10 Manual.Count131072.C065199.packed 64 cuts65199 = true := by
 decide +kernel
def pointBounds65199 : List (Nat × Nat × Nat) := [(8549769216,114941131130346,114941520126265)]
theorem point_links_checked65199 : (cuts65199.take 1).map (fun c => (8549695489-1+2*2^10*c.k,114941025285888+c.lower,114941414281746+c.upper)) = pointBounds65199 := by
 decide +kernel
def cuts65200 : List PrefixCut := [⟨64,191043215,191043326⟩]
theorem checked65200 : checkPrefixCuts (2^48) 8549826561 10 Manual.Count131072.C065200.packed 64 cuts65200 = true := by
 decide +kernel
def cuts65201 : List PrefixCut := [⟨39,115421200,115421269⟩,
⟨64,186991013,186991125⟩]
theorem checked65201 : checkPrefixCuts (2^48) 8549957633 10 Manual.Count131072.C065201.packed 64 cuts65201 = true := by
 decide +kernel
def pointBounds65201 : List (Nat × Nat × Nat) := [(8550037504,114941520854044,114941909850191)]
theorem point_links_checked65201 : (cuts65201.take 1).map (fun c => (8549957633-1+2*2^10*c.k,114941405432844+c.lower,114941794428922+c.upper)) = pointBounds65201 := by
 decide +kernel
def cuts65202 : List PrefixCut := [⟨64,187975741,187975853⟩]
theorem checked65202 : checkPrefixCuts (2^48) 8550088705 10 Manual.Count131072.C065202.packed 64 cuts65202 = true := by
 decide +kernel
def cuts65203 : List PrefixCut := [⟨42,123186746,123186816⟩,
⟨64,188762938,188763047⟩]
theorem checked65203 : checkPrefixCuts (2^48) 8550219777 10 Manual.Count131072.C065203.packed 64 cuts65203 = true := by
 decide +kernel
def pointBounds65203 : List (Nat × Nat × Nat) := [(8550305792,114941903586344,114942292582716)]
theorem point_links_checked65203 : (cuts65203.take 1).map (fun c => (8550219777-1+2*2^10*c.k,114941780399598+c.lower,114942169395900+c.upper)) = pointBounds65203 := by
 decide +kernel
def cuts65204 : List PrefixCut := [⟨64,188101664,188101776⟩]
theorem checked65204 : checkPrefixCuts (2^48) 8550350849 10 Manual.Count131072.C065204.packed 64 cuts65204 = true := by
 decide +kernel
def cuts65205 : List PrefixCut := [⟨45,134441229,134441309⟩,
⟨64,189711819,189711930⟩]
theorem checked65205 : checkPrefixCuts (2^48) 8550481921 10 Manual.Count131072.C065205.packed 64 cuts65205 = true := by
 decide +kernel
def pointBounds65205 : List (Nat × Nat × Nat) := [(8550574080,114942291705429,114942680702032)]
theorem point_links_checked65205 : (cuts65205.take 1).map (fun c => (8550481921-1+2*2^10*c.k,114942157264200+c.lower,114942546260723+c.upper)) = pointBounds65205 := by
 decide +kernel
def cuts65206 : List PrefixCut := [⟨64,190070999,190071108⟩]
theorem checked65206 : checkPrefixCuts (2^48) 8550612993 10 Manual.Count131072.C065206.packed 64 cuts65206 = true := by
 decide +kernel
def cuts65207 : List PrefixCut := [⟨48,141514427,141514507⟩,
⟨64,188652624,188652729⟩]
theorem checked65207 : checkPrefixCuts (2^48) 8550744065 10 Manual.Count131072.C065207.packed 64 cuts65207 = true := by
 decide +kernel
def pointBounds65207 : List (Nat × Nat × Nat) := [(8550842368,114942678561445,114943067558268)]
theorem point_links_checked65207 : (cuts65207.take 1).map (fun c => (8550744065-1+2*2^10*c.k,114942537047018+c.lower,114942926043761+c.upper)) = pointBounds65207 := by
 decide +kernel
def cuts65208 : List PrefixCut := [⟨64,188913068,188913178⟩]
theorem checked65208 : checkPrefixCuts (2^48) 8550875137 10 Manual.Count131072.C065208.packed 64 cuts65208 = true := by
 decide +kernel
def cuts65209 : List PrefixCut := [⟨51,150331785,150331870⟩,
⟨64,188910173,188910281⟩]
theorem checked65209 : checkPrefixCuts (2^48) 8551006209 10 Manual.Count131072.C065209.packed 64 cuts65209 = true := by
 decide +kernel
def pointBounds65209 : List (Nat × Nat × Nat) := [(8551110656,114943064944495,114943453941538)]
theorem point_links_checked65209 : (cuts65209.take 1).map (fun c => (8551006209-1+2*2^10*c.k,114942914612710+c.lower,114943303609668+c.upper)) = pointBounds65209 := by
 decide +kernel
def cuts65210 : List PrefixCut := [⟨64,191441828,191441935⟩]
theorem checked65210 : checkPrefixCuts (2^48) 8551137281 10 Manual.Count131072.C065210.packed 64 cuts65210 = true := by
 decide +kernel
def cuts65211 : List PrefixCut := [⟨54,158556098,158556187⟩,
⟨64,188805618,188805724⟩]
theorem checked65211 : checkPrefixCuts (2^48) 8551268353 10 Manual.Count131072.C065211.packed 64 cuts65211 = true := by
 decide +kernel
def pointBounds65211 : List (Nat × Nat × Nat) := [(8551378944,114943453520809,114943842518071)]
theorem point_links_checked65211 : (cuts65211.take 1).map (fun c => (8551268353-1+2*2^10*c.k,114943294964711+c.lower,114943683961884+c.upper)) = pointBounds65211 := by
 decide +kernel
def cuts65212 : List PrefixCut := [⟨64,188703989,188704096⟩]
theorem checked65212 : checkPrefixCuts (2^48) 8551399425 10 Manual.Count131072.C065212.packed 64 cuts65212 = true := by
 decide +kernel
def cuts65213 : List PrefixCut := [⟨57,165232927,165233025⟩,
⟨64,186923696,186923805⟩]
theorem checked65213 : checkPrefixCuts (2^48) 8551530497 10 Manual.Count131072.C065213.packed 64 cuts65213 = true := by
 decide +kernel
def pointBounds65213 : List (Nat × Nat × Nat) := [(8551647232,114943837707245,114944226704729)]
theorem point_links_checked65213 : (cuts65213.take 1).map (fun c => (8551530497-1+2*2^10*c.k,114943672474318+c.lower,114944061471704+c.upper)) = pointBounds65213 := by
 decide +kernel
def cuts65214 : List PrefixCut := [⟨64,188764026,188764141⟩]
theorem checked65214 : checkPrefixCuts (2^48) 8551661569 10 Manual.Count131072.C065214.packed 64 cuts65214 = true := by
 decide +kernel
def cuts65215 : List PrefixCut := [⟨60,176912229,176912332⟩,
⟨64,188958625,188958736⟩]
theorem checked65215 : checkPrefixCuts (2^48) 8551792641 10 Manual.Count131072.C065215.packed 64 cuts65215 = true := by
 decide +kernel
def pointBounds65215 : List (Nat × Nat × Nat) := [(8551915520,114944225074269,114944614071982)]
theorem point_links_checked65215 : (cuts65215.take 1).map (fun c => (8551792641-1+2*2^10*c.k,114944048162040+c.lower,114944437159650+c.upper)) = pointBounds65215 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S7.B000162
