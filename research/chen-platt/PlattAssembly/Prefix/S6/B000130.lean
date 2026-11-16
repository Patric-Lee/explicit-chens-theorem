import PlattAssemblyKernel
import PlattCertificates.Count131072.C054160
import PlattCertificates.Count131072.C054161
import PlattCertificates.Count131072.C054162
import PlattCertificates.Count131072.C054163
import PlattCertificates.Count131072.C054164
import PlattCertificates.Count131072.C054165
import PlattCertificates.Count131072.C054166
import PlattCertificates.Count131072.C054167
import PlattCertificates.Count131072.C054168
import PlattCertificates.Count131072.C054169
import PlattCertificates.Count131072.C054170
import PlattCertificates.Count131072.C054171
import PlattCertificates.Count131072.C054172
import PlattCertificates.Count131072.C054173
import PlattCertificates.Count131072.C054174
import PlattCertificates.Count131072.C054175
import PlattCertificates.Count131072.C054176
import PlattCertificates.Count131072.C054177
import PlattCertificates.Count131072.C054178
import PlattCertificates.Count131072.C054179
import PlattCertificates.Count131072.C054180
import PlattCertificates.Count131072.C054181
import PlattCertificates.Count131072.C054182
import PlattCertificates.Count131072.C054183
import PlattCertificates.Count131072.C054184
import PlattCertificates.Count131072.C054185
import PlattCertificates.Count131072.C054186
import PlattCertificates.Count131072.C054187
import PlattCertificates.Count131072.C054188
import PlattCertificates.Count131072.C054189
import PlattCertificates.Count131072.C054190
import PlattCertificates.Count131072.C054191
namespace ChenEffective.PlattWindow.Assembly.Prefix.S6.B000130
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts54160 : List PrefixCut := [⟨64,230082503,230082632⟩]
theorem checked54160 : checkPrefixCuts (2^48) 7102791681 10 Manual.Count131072.C054160.packed 64 cuts54160 = true := by
 decide +kernel
def cuts54161 : List PrefixCut := [⟨1,3447639,3447641⟩,
⟨64,226947673,226947802⟩]
theorem checked54161 : checkPrefixCuts (2^48) 7102922753 10 Manual.Count131072.C054161.packed 64 cuts54161 = true := by
 decide +kernel
def pointBounds54161 : List (Nat × Nat × Nat) := [(7102924800,112649974720578,112650362407014)]
theorem point_links_checked54161 : (cuts54161.take 1).map (fun c => (7102922753-1+2*2^10*c.k,112649971272939+c.lower,112650358959373+c.upper)) = pointBounds54161 := by
 decide +kernel
def cuts54162 : List PrefixCut := [⟨46,165641055,165641148⟩,
⟨64,230509928,230510058⟩]
theorem checked54162 : checkPrefixCuts (2^48) 7103053825 10 Manual.Count131072.C054162.packed 64 cuts54162 = true := by
 decide +kernel
def pointBounds54162 : List (Nat × Nat × Nat) := [(7103148032,112650363861667,112650751548323)]
theorem point_links_checked54162 : (cuts54162.take 1).map (fun c => (7103053825-1+2*2^10*c.k,112650198220612+c.lower,112650585907175+c.upper)) = pointBounds54162 := by
 decide +kernel
def cuts54163 : List PrefixCut := [⟨64,232922886,232923020⟩]
theorem checked54163 : checkPrefixCuts (2^48) 7103184897 10 Manual.Count131072.C054163.packed 64 cuts54163 = true := by
 decide +kernel
def cuts54164 : List PrefixCut := [⟨27,95497912,95497968⟩,
⟨64,227093608,227093740⟩]
theorem checked54164 : checkPrefixCuts (2^48) 7103315969 10 Manual.Count131072.C054164.packed 64 cuts54164 = true := by
 decide +kernel
def pointBounds54164 : List (Nat × Nat × Nat) := [(7103371264,112650757151338,112651144838221)]
theorem point_links_checked54164 : (cuts54164.take 1).map (fun c => (7103315969-1+2*2^10*c.k,112650661653426+c.lower,112651049340253+c.upper)) = pointBounds54164 := by
 decide +kernel
def cuts54165 : List PrefixCut := [⟨64,228436659,228436787⟩]
theorem checked54165 : checkPrefixCuts (2^48) 7103447041 10 Manual.Count131072.C054165.packed 64 cuts54165 = true := by
 decide +kernel
def cuts54166 : List PrefixCut := [⟨8,28529522,28529538⟩,
⟨64,229938172,229938300⟩]
theorem checked54166 : checkPrefixCuts (2^48) 7103578113 10 Manual.Count131072.C054166.packed 64 cuts54166 = true := by
 decide +kernel
def pointBounds54166 : List (Nat × Nat × Nat) := [(7103594496,112651145713215,112651533400318)]
theorem point_links_checked54166 : (cuts54166.take 1).map (fun c => (7103578113-1+2*2^10*c.k,112651117183693+c.lower,112651504870780+c.upper)) = pointBounds54166 := by
 decide +kernel
def cuts54167 : List PrefixCut := [⟨53,187933544,187933652⟩,
⟨64,225931986,225932117⟩]
theorem checked54167 : checkPrefixCuts (2^48) 7103709185 10 Manual.Count131072.C054167.packed 64 cuts54167 = true := by
 decide +kernel
def pointBounds54167 : List (Nat × Nat × Nat) := [(7103817728,112651535055409,112651922742732)]
theorem point_links_checked54167 : (cuts54167.take 1).map (fun c => (7103709185-1+2*2^10*c.k,112651347121865+c.lower,112651734809080+c.upper)) = pointBounds54167 := by
 decide +kernel
def cuts54168 : List PrefixCut := [⟨64,233971189,233971319⟩]
theorem checked54168 : checkPrefixCuts (2^48) 7103840257 10 Manual.Count131072.C054168.packed 64 cuts54168 = true := by
 decide +kernel
def cuts54169 : List PrefixCut := [⟨34,122907428,122907497⟩,
⟨64,229251886,229252016⟩]
theorem checked54169 : checkPrefixCuts (2^48) 7103971329 10 Manual.Count131072.C054169.packed 64 cuts54169 = true := by
 decide +kernel
def pointBounds54169 : List (Nat × Nat × Nat) := [(7104040960,112651929932468,112652317620013)]
theorem point_links_checked54169 : (cuts54169.take 1).map (fun c => (7103971329-1+2*2^10*c.k,112651807025040+c.lower,112652194712516+c.upper)) = pointBounds54169 := by
 decide +kernel
def cuts54170 : List PrefixCut := [⟨64,228930664,228930790⟩]
theorem checked54170 : checkPrefixCuts (2^48) 7104102401 10 Manual.Count131072.C054170.packed 64 cuts54170 = true := by
 decide +kernel
def cuts54171 : List PrefixCut := [⟨15,53329383,53329414⟩,
⟨64,229441509,229441641⟩]
theorem checked54171 : checkPrefixCuts (2^48) 7104233473 10 Manual.Count131072.C054171.packed 64 cuts54171 = true := by
 decide +kernel
def pointBounds54171 : List (Nat × Nat × Nat) := [(7104264192,112652318536973,112652706224736)]
theorem point_links_checked54171 : (cuts54171.take 1).map (fun c => (7104233473-1+2*2^10*c.k,112652265207590+c.lower,112652652895322+c.upper)) = pointBounds54171 := by
 decide +kernel
def cuts54172 : List PrefixCut := [⟨60,215847886,215848006⟩,
⟨64,230982454,230982582⟩]
theorem checked54172 : checkPrefixCuts (2^48) 7104364545 10 Manual.Count131072.C054172.packed 64 cuts54172 = true := by
 decide +kernel
def pointBounds54172 : List (Nat × Nat × Nat) := [(7104487424,112652710496985,112653098184969)]
theorem point_links_checked54172 : (cuts54172.take 1).map (fun c => (7104364545-1+2*2^10*c.k,112652494649099+c.lower,112652882336963+c.upper)) = pointBounds54172 := by
 decide +kernel
def cuts54173 : List PrefixCut := [⟨64,227531341,227531470⟩]
theorem checked54173 : checkPrefixCuts (2^48) 7104495617 10 Manual.Count131072.C054173.packed 64 cuts54173 = true := by
 decide +kernel
def cuts54174 : List PrefixCut := [⟨41,146904649,146904733⟩,
⟨64,229270335,229270465⟩]
theorem checked54174 : checkPrefixCuts (2^48) 7104626689 10 Manual.Count131072.C054174.packed 64 cuts54174 = true := by
 decide +kernel
def pointBounds54174 : List (Nat × Nat × Nat) := [(7104710656,112653100067543,112653487755748)]
theorem point_links_checked54174 : (cuts54174.take 1).map (fun c => (7104626689-1+2*2^10*c.k,112652953162894+c.lower,112653340851015+c.upper)) = pointBounds54174 := by
 decide +kernel
def cuts54175 : List PrefixCut := [⟨64,228711477,228711608⟩]
theorem checked54175 : checkPrefixCuts (2^48) 7104757761 10 Manual.Count131072.C054175.packed 64 cuts54175 = true := by
 decide +kernel
def cuts54176 : List PrefixCut := [⟨22,77926533,77926576⟩,
⟨64,228905327,228905454⟩]
theorem checked54176 : checkPrefixCuts (2^48) 7104888833 10 Manual.Count131072.C054176.packed 64 cuts54176 = true := by
 decide +kernel
def pointBounds54176 : List (Nat × Nat × Nat) := [(7104933888,112653489071239,112653876759664)]
theorem point_links_checked54176 : (cuts54176.take 1).map (fun c => (7104888833-1+2*2^10*c.k,112653411144706+c.lower,112653798833088+c.upper)) = pointBounds54176 := by
 decide +kernel
def cuts54177 : List PrefixCut := [⟨64,229851924,229852052⟩]
theorem checked54177 : checkPrefixCuts (2^48) 7105019905 10 Manual.Count131072.C054177.packed 64 cuts54177 = true := by
 decide +kernel
def cuts54178 : List PrefixCut := [⟨3,10300054,10300060⟩,
⟨64,228144184,228144313⟩]
theorem checked54178 : checkPrefixCuts (2^48) 7105150977 10 Manual.Count131072.C054178.packed 64 cuts54178 = true := by
 decide +kernel
def pointBounds54178 : List (Nat × Nat × Nat) := [(7105157120,112653880202011,112654267890654)]
theorem point_links_checked54178 : (cuts54178.take 1).map (fun c => (7105150977-1+2*2^10*c.k,112653869901957+c.lower,112654257590594+c.upper)) = pointBounds54178 := by
 decide +kernel
def cuts54179 : List PrefixCut := [⟨48,167173627,167173725⟩,
⟨64,224733117,224733251⟩]
theorem checked54179 : checkPrefixCuts (2^48) 7105282049 10 Manual.Count131072.C054179.packed 64 cuts54179 = true := by
 decide +kernel
def pointBounds54179 : List (Nat × Nat × Nat) := [(7105380352,112654265219768,112654652908632)]
theorem point_links_checked54179 : (cuts54179.take 1).map (fun c => (7105282049-1+2*2^10*c.k,112654098046141+c.lower,112654485734907+c.upper)) = pointBounds54179 := by
 decide +kernel
def cuts54180 : List PrefixCut := [⟨64,226155091,226155221⟩]
theorem checked54180 : checkPrefixCuts (2^48) 7105413121 10 Manual.Count131072.C054180.packed 64 cuts54180 = true := by
 decide +kernel
def cuts54181 : List PrefixCut := [⟨29,105014738,105014796⟩,
⟨64,230706425,230706555⟩]
theorem checked54181 : checkPrefixCuts (2^48) 7105544193 10 Manual.Count131072.C054181.packed 64 cuts54181 = true := by
 decide +kernel
def pointBounds54181 : List (Nat × Nat × Nat) := [(7105603584,112654653949087,112655041638175)]
theorem point_links_checked54181 : (cuts54181.take 1).map (fun c => (7105544193-1+2*2^10*c.k,112654548934349+c.lower,112654936623379+c.upper)) = pointBounds54181 := by
 decide +kernel
def cuts54182 : List PrefixCut := [⟨64,227929301,227929431⟩]
theorem checked54182 : checkPrefixCuts (2^48) 7105675265 10 Manual.Count131072.C054182.packed 64 cuts54182 = true := by
 decide +kernel
def cuts54183 : List PrefixCut := [⟨10,36046830,36046849⟩,
⟨64,226815968,226816096⟩]
theorem checked54183 : checkPrefixCuts (2^48) 7105806337 10 Manual.Count131072.C054183.packed 64 cuts54183 = true := by
 decide +kernel
def pointBounds54183 : List (Nat × Nat × Nat) := [(7105826816,112655043616905,112655431306214)]
theorem point_links_checked54183 : (cuts54183.take 1).map (fun c => (7105806337-1+2*2^10*c.k,112655007570075+c.lower,112655395259365+c.upper)) = pointBounds54183 := by
 decide +kernel
def cuts54184 : List PrefixCut := [⟨55,197816899,197817005⟩,
⟨64,229663779,229663904⟩]
theorem checked54184 : checkPrefixCuts (2^48) 7105937409 10 Manual.Count131072.C054184.packed 64 cuts54184 = true := by
 decide +kernel
def pointBounds54184 : List (Nat × Nat × Nat) := [(7106050048,112655432202942,112655819892466)]
theorem point_links_checked54184 : (cuts54184.take 1).map (fun c => (7105937409-1+2*2^10*c.k,112655234386043+c.lower,112655622075461+c.upper)) = pointBounds54184 := by
 decide +kernel
def cuts54185 : List PrefixCut := [⟨64,229184219,229184353⟩]
theorem checked54185 : checkPrefixCuts (2^48) 7106068481 10 Manual.Count131072.C054185.packed 64 cuts54185 = true := by
 decide +kernel
def cuts54186 : List PrefixCut := [⟨36,128691456,128691531⟩,
⟨64,228427402,228427534⟩]
theorem checked54186 : checkPrefixCuts (2^48) 7106199553 10 Manual.Count131072.C054186.packed 64 cuts54186 = true := by
 decide +kernel
def pointBounds54186 : List (Nat × Nat × Nat) := [(7106273280,112655821925497,112656209615249)]
theorem point_links_checked54186 : (cuts54186.take 1).map (fun c => (7106199553-1+2*2^10*c.k,112655693234041+c.lower,112656080923718+c.upper)) = pointBounds54186 := by
 decide +kernel
def cuts54187 : List PrefixCut := [⟨64,226680423,226680551⟩]
theorem checked54187 : checkPrefixCuts (2^48) 7106330625 10 Manual.Count131072.C054187.packed 64 cuts54187 = true := by
 decide +kernel
def cuts54188 : List PrefixCut := [⟨17,62105670,62105707⟩,
⟨64,230914290,230914421⟩]
theorem checked54188 : checkPrefixCuts (2^48) 7106461697 10 Manual.Count131072.C054188.packed 64 cuts54188 = true := by
 decide +kernel
def pointBounds54188 : List (Nat × Nat × Nat) := [(7106496512,112656210447536,112656598137510)]
theorem point_links_checked54188 : (cuts54188.take 1).map (fun c => (7106461697-1+2*2^10*c.k,112656148341866+c.lower,112656536031803+c.upper)) = pointBounds54188 := by
 decide +kernel
def cuts54189 : List PrefixCut := [⟨62,219463615,219463741⟩,
⟨64,226196780,226196910⟩]
theorem checked54189 : checkPrefixCuts (2^48) 7106592769 10 Manual.Count131072.C054189.packed 64 cuts54189 = true := by
 decide +kernel
def pointBounds54189 : List (Nat × Nat × Nat) := [(7106719744,112656598719771,112656986409965)]
theorem point_links_checked54189 : (cuts54189.take 1).map (fun c => (7106592769-1+2*2^10*c.k,112656379256156+c.lower,112656766946224+c.upper)) = pointBounds54189 := by
 decide +kernel
def cuts54190 : List PrefixCut := [⟨64,231183026,231183155⟩]
theorem checked54190 : checkPrefixCuts (2^48) 7106723841 10 Manual.Count131072.C054190.packed 64 cuts54190 = true := by
 decide +kernel
def cuts54191 : List PrefixCut := [⟨43,154423287,154423374⟩,
⟨64,231178751,231178881⟩]
theorem checked54191 : checkPrefixCuts (2^48) 7106854913 10 Manual.Count131072.C054191.packed 64 cuts54191 = true := by
 decide +kernel
def pointBounds54191 : List (Nat × Nat × Nat) := [(7106942976,112656991059249,112657378749663)]
theorem point_links_checked54191 : (cuts54191.take 1).map (fun c => (7106854913-1+2*2^10*c.k,112656836635962+c.lower,112657224326289+c.upper)) = pointBounds54191 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S6.B000130
